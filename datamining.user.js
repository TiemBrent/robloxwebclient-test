// ==UserScript==
// @name         SourceMiner (rbx)
// @namespace    https://venice.ai/
// @version      5.0.2
// @description  Harvest engine source, Lua packages, configs, shaders and asset payloads from WASM-hosted apps. OPFS-spooled storage, streaming ZIP, resource-timing seeding, manifest expansion, runtime capture, POST replay, rbxm Lua extraction, crash recovery.
// @author       Venice
// @match        *://*/*
// @grant        GM_xmlhttpRequest
// @grant        GM_setValue
// @grant        GM_getValue
// @grant        GM_registerMenuCommand
// @connect      *
// @run-at       document-start
// @noframes
// ==/UserScript==

(function () {
  'use strict';

  const VERSION = '5.0.2';
  const CFG_KEY = 'sm_cfg_v5';
  const OWN = '__sm_own__';
  const ROOT = 'sourceminer';

  const ALLOW_HOSTS = ['roblox.com', 'rbxcdn.com', 'rbx.com', 'robloxlabs.com', 'roblox.cn'];

  const cfg = Object.assign({
    scope: 'all',
    followLinks: false,
    maxDepth: 4,
    maxFiles: 200000,
    maxMB: 0,              // 0 = disk-bound, no ceiling
    maxBodyMB: 512,
    concurrency: 6,
    delay: 60,
    inlineCode: true,
    sourcemaps: true,
    assets: true,
    allowQuery: true,
    runtime: true,
    captureRequests: true,
    captureWs: true,
    seedKnown: true,
    seedTiming: true,
    expandJson: true,
    rbxLua: true,
    exclude: '\\.(?:mp4|webm|mp3|wav|ogg|zip|gz|7z|rar|exe|dmg|apk)$',
  }, GM_getValue(CFG_KEY, {}));

  const saveCfg = () => GM_setValue(CFG_KEY, cfg);

  /* =============================== state ============================== */

  // metadata only — bytes live in OPFS (or memStore when OPFS is absent)
  const files = new Map();       // key -> { name, size, type, source, meta }
  const memStore = new Map();    // name -> Uint8Array  (fallback only)
  const usedNames = new Set();
  const queued = new Set();
  const seen = new Set();
  const queue = [];
  const netIndex = [];
  let totalBytes = 0, runtimeCount = 0, running = false, stopFlag = false;
  let shadow, panel, logBox, statsBox, fileList, capToggle;
  let opfsRoot = null, sessionDir = null, USE_OPFS = false, writeChain = Promise.resolve();
  let indexTimer = null, renderTimer = null;

  const TEXTISH = /^(?:text\/|application\/(?:json|ld\+json|javascript|ecmascript|xml|xhtml\+xml|manifest\+json|graphql|wasm|octet-stream)|image\/svg)/i;

  const TYPE_EXT = {
    'text/html': 'html', 'application/xhtml+xml': 'html', 'text/css': 'css',
    'text/javascript': 'js', 'application/javascript': 'js', 'application/x-javascript': 'js',
    'application/json': 'json', 'application/ld+json': 'json', 'application/manifest+json': 'webmanifest',
    'text/plain': 'txt', 'text/xml': 'xml', 'application/xml': 'xml', 'image/svg+xml': 'svg',
    'application/wasm': 'wasm', 'application/octet-stream': 'bin',
    'image/png': 'png', 'image/jpeg': 'jpg', 'image/webp': 'webp', 'image/avif': 'avif',
    'image/x-icon': 'ico', 'font/ttf': 'ttf', 'font/otf': 'otf', 'font/woff': 'woff', 'font/woff2': 'woff2',
  };

  /* ============================== helpers ============================= */

  const $ = (s, r) => (r || shadow).querySelector(s);
  const $$ = (s, r) => Array.from((r || shadow).querySelectorAll(s));
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const decodeBytes = (u8) => new TextDecoder('utf-8').decode(u8);

  function log(msg, cls) {
    if (!logBox) return;
    const line = document.createElement('div');
    line.textContent = `[${new Date().toLocaleTimeString()}] ${msg}`;
    if (cls) line.style.color = cls;
    logBox.prepend(line);
    while (logBox.children.length > 600) logBox.lastChild.remove();
  }

  function toast(msg, ms) {
    if (!shadow) return;
    const t = document.createElement('div');
    t.className = 'toast';
    t.textContent = msg;
    shadow.appendChild(t);
    setTimeout(() => t.remove(), ms || 2200);
  }

  const fmtBytes = (n) => n < 1024 ? n + ' B' : n < 1048576 ? (n / 1024).toFixed(1) + ' KB' : n < 1073741824 ? (n / 1048576).toFixed(1) + ' MB' : (n / 1073741824).toFixed(2) + ' GB';
  const stripHash = (u) => { const i = u.indexOf('#'); return i === -1 ? u : u.slice(0, i); };
  const extOf = (u) => ((/\.([a-z0-9]{1,8})(?:[?#]|$)/i.exec(u) || [])[1] || '').toLowerCase();

  function absolutize(raw, base) {
    if (!raw) return null;
    raw = raw.trim().replace(/^["']|["']$/g, '');
    if (/^(?:javascript|mailto|tel|blob):/i.test(raw)) return null;
    if (/^data:/i.test(raw)) return raw;
    try { return new URL(raw, base || location.href).href; } catch { return null; }
  }

  const hostAllowed = (h) => ALLOW_HOSTS.some((a) => h === a || h.endsWith('.' + a));

  // compiled once per change — the old code rebuilt a broken regex on every URL
  let excludeRe = null, excludeSrc = null;
  function excluded(pathname) {
    if (!cfg.exclude) return false;
    if (excludeSrc !== cfg.exclude) {
      excludeSrc = cfg.exclude;
      try { excludeRe = new RegExp(cfg.exclude, 'i'); } catch { excludeRe = null; }
    }
    return excludeRe ? excludeRe.test(pathname) : false;
  }

  function inScope(url) {
    if (!url || url.startsWith('data:')) return true;
    let u;
    try { u = new URL(url); } catch { return false; }
    if (!/^https?:$/.test(u.protocol)) return false;
    if (excluded(u.pathname)) return false;
    if (cfg.scope === 'all') return true;
    if (cfg.scope === 'hosts') return hostAllowed(u.hostname) || u.origin === location.origin;
    return u.origin === location.origin;
  }

  function kindOf(url, type) {
    if (url.startsWith('data:')) return 'data';
    const ext = extOf(url);
    if (/^(?:html?|xhtml|php|aspx?|jsp)$/.test(ext) || /html/.test(type || '')) return 'page';
    if (/^(?:js|mjs|cjs|jsx|ts|tsx|luau?)$/.test(ext)) return 'code';
    if (/^(?:css|scss|sass|less)$/.test(ext)) return 'style';
    if (/^map$/.test(ext)) return 'map';
    if (/^(?:json|json5|jsonc|xml|svg|txt|md|csv|tsv|ya?ml|toml|ini|graphql|webmanifest|config)$/.test(ext)) return 'doc';
    if (/^(?:wasm|rbxm|rbxmx|mesh|dds|tex|pack|bin)$/.test(ext)) return 'asset';
    if (/^(?:png|jpe?g|gif|webp|avif|ico|bmp|tga|ttf|otf|woff2?)$/.test(ext)) return 'asset';
    if (/json|octet-stream|wasm/.test(type || '')) return 'doc';
    return 'asset';
  }

  function hash32(s) {
    let h = 2166136261;
    for (let i = 0; i < s.length; i++) { h ^= s.charCodeAt(i); h = Math.imul(h, 16777619); }
    return (h | 0) >>> 0;
  }

  // O(1) collision handling
  function uniqueName(base) {
    if (!usedNames.has(base)) { usedNames.add(base); return base; }
    let n = 1, name;
    do { name = base.replace(/(\.[a-z0-9]+)?$/i, `_${n++}$1`); } while (usedNames.has(name));
    usedNames.add(name);
    return name;
  }

  function fileNameFor(url, type, prefix) {
    let u;
    try { u = new URL(url); } catch { return uniqueName((prefix || '') + 'unknown/' + Date.now()); }
    let path = decodeURIComponent(u.pathname);
    if (!path || path.endsWith('/')) path += 'index.html';
    if (!/\.[a-z0-9]{1,8}$/i.test(path.split('/').pop())) {
      const g = TYPE_EXT[(type || '').split(';')[0].trim().toLowerCase()];
      path += '.' + (g || 'txt');
    }
    let name = (prefix || '') + u.host + path;
    if (cfg.allowQuery && u.search) name += '__' + hash32(u.search).toString(36);
    name = name.replace(/[^\w.\-\/]/g, '_').replace(/\/{2,}/g, '/').replace(/^\/+/, '');
    return uniqueName(name);
  }

  /* ============================== storage ============================= */

  async function initOPFS() {
    try {
      if (!navigator.storage?.getDirectory) return false;
      opfsRoot = await navigator.storage.getDirectory();
      const root = await opfsRoot.getDirectoryHandle(ROOT, { create: true });
      const stamp = new Date().toISOString().replace(/[:.]/g, '-').slice(0, 19);
      const uniq = Math.random().toString(36).slice(2, 6);
      sessionDir = await root.getDirectoryHandle(`s_${location.hostname}_${stamp}_${uniq}`, { create: true });
      const est = await navigator.storage.estimate().catch(() => null);
      if (est?.quota) log(`disk: ${fmtBytes(est.quota - est.usage)} free of ${fmtBytes(est.quota)}`, '#8fa0b3');
      USE_OPFS = true;
      return true;
    } catch (e) {
      log('OPFS unavailable, falling back to memory: ' + e.message, '#ffb86b');
      USE_OPFS = false;
      return false;
    }
  }

  // serialized so concurrent writers don't thrash the same stream budget
  function writeFile(name, bytes) {
    if (!USE_OPFS) { memStore.set(name, bytes); return Promise.resolve(); }
    writeChain = writeChain.then(async () => {
      const fh = await sessionDir.getFileHandle(name.replace(/\//g, '__SLASH__'), { create: true });
      const ws = await fh.createWritable();
      await ws.write(bytes);
      await ws.close();
    }).catch((e) => log('write fail ' + name + ': ' + e.message, '#ff7a8a'));
    return writeChain;
  }

  async function readFile(name) {
    if (!USE_OPFS) return memStore.get(name);
    const fh = await sessionDir.getFileHandle(name.replace(/\//g, '__SLASH__'));
    return new Uint8Array(await (await fh.getFile()).arrayBuffer());
  }

  async function readFileHandle(name) {
    return sessionDir.getFileHandle(name.replace(/\//g, '__SLASH__'));
  }

  function scheduleIndex() {
    if (!USE_OPFS || indexTimer) return;
    indexTimer = setTimeout(async () => {
      indexTimer = null;
      try {
        const idx = [...files.entries()].map(([k, f]) => ({ k, ...f }));
        const fh = await sessionDir.getFileHandle('_index.json', { create: true });
        const ws = await fh.createWritable();
        await ws.write(new TextEncoder().encode(JSON.stringify(idx)));
        await ws.close();
      } catch {}
    }, 1200);
  }

  async function store(key, bytes, type, opts) {
    if (files.has(key)) return false;
    if (bytes.length > cfg.maxBodyMB * 1048576) { log('body too large: ' + key, '#ffb86b'); return false; }
    if (files.size >= cfg.maxFiles) { log('file cap reached', '#ffb86b'); return false; }
    if (cfg.maxMB > 0 && totalBytes + bytes.length > cfg.maxMB * 1048576) { log('size cap reached', '#ffb86b'); return false; }

    const o = opts || {};
    const name = o.name || fileNameFor(key, type, o.prefix);
    totalBytes += bytes.length;
    if ((o.source || 'static') === 'runtime') runtimeCount++;
    files.set(key, { name, size: bytes.length, type: type || '', source: o.source || 'static', meta: o.meta || null });
    await writeFile(name, bytes);
    scheduleIndex();
    scheduleRender(); updateStats();
    return true;
  }

  function enqueue(url, depth, kind) {
    if (!url || !inScope(url)) return;
    const key = stripHash(url);
    if (queued.has(key) || seen.has(key)) return;
    queued.add(key);
    queue.push({ url: key, depth, kind });
  }

  async function listSessions() {
    if (!opfsRoot) return [];
    try {
      const root = await opfsRoot.getDirectoryHandle(ROOT);
      const out = [];
      for await (const [name, handle] of root.entries()) {
        if (handle.kind === 'directory') out.push(name);
      }
      return out.sort().reverse();
    } catch { return []; }
  }

  async function adoptSession(name) {
    const root = await opfsRoot.getDirectoryHandle(ROOT);
    sessionDir = await root.getDirectoryHandle(name);
    const fh = await sessionDir.getFileHandle('_index.json');
    const idx = JSON.parse(await (await fh.getFile()).text());
    files.clear(); usedNames.clear(); memStore.clear(); totalBytes = 0; runtimeCount = 0;
    for (const rec of idx) {
      files.set(rec.k, { name: rec.name, size: rec.size, type: rec.type, source: rec.source, meta: rec.meta });
      usedNames.add(rec.name);
      totalBytes += rec.size;
      if (rec.source === 'runtime') runtimeCount++;
    }
    USE_OPFS = true;
    renderFiles(); updateStats();
    log(`recovered ${files.size} files from ${name}`, '#00e0a4');
  }

  /* ============================ transport ============================ */

  function request(url, binary, method, body) {
    method = method || 'GET';
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method, url, timeout: 40000,
        responseType: binary ? 'arraybuffer' : 'text',
        headers: body ? { 'Content-Type': 'application/json' } : {},
        data: body || undefined,
        onload: (r) => {
          const ct = (/content-type:\s*([^\r\n;]+)/i.exec(r.responseHeaders || '') || [])[1] || '';
          resolve({ status: r.status, ct: ct.trim().toLowerCase(), data: r.response });
        },
        onerror: () => reject(new Error('network error')),
        ontimeout: () => reject(new Error('timeout')),
      });
    });
  }

  function decode(buf, ct) {
    const m = /charset=([\w-]+)/i.exec(ct || '');
    try { return new TextDecoder(m ? m[1] : 'utf-8').decode(buf); }
    catch { return new TextDecoder('utf-8').decode(buf); }
  }

  /* ========================== runtime capture ======================== */

  let netSeq = 0;

  async function recordRuntime(rec) {
    if (!cfg.runtime || !inScope(rec.url)) return;
    if (rec.url.startsWith('blob:') || rec.url.startsWith('data:')) return;
    if (rec.status && (rec.status < 200 || rec.status >= 400)) {
      netIndex.push({ ...rec, size: 0, saved: false, t: Date.now() });
      return;
    }
    const ct = rec.contentType || '';
    const isText = TEXTISH.test(ct) || (!rec.binary && rec.text != null);
    let bytes, type = ct;

    if (isText && rec.text != null) {
      if (!rec.text.length) return;
      bytes = new TextEncoder().encode(rec.text);
      if (!type) type = 'text/plain';
      const k = kindOf(rec.url, type);
      if (k === 'doc' || k === 'code' || k === 'page') {
        if (cfg.expandJson && /json/.test(type)) parseManifest(rec.text, rec.url);
        harvestText(rec.text, rec.url, 0, k === 'code');
      }
    } else if (rec.buffer) {
      bytes = new Uint8Array(rec.buffer);
    } else return;

    const method = rec.method || 'GET';
    const key = `${method} ${rec.url}${rec.postBody ? ' #' + hash32(rec.postBody) : ''}`;
    const ok = await store(key, bytes, type, {
      prefix: '_net/', source: 'runtime',
      meta: { method, status: rec.status, kind: rec.kind, contentType: ct, truncated: !!rec.truncated },
    });
    netIndex.push({ url: rec.url, method, status: rec.status, kind: rec.kind, size: bytes.length, saved: ok, t: Date.now() });

    if (ok && cfg.captureRequests && rec.postBody) {
      const rname = uniqueName(fileNameFor(rec.url, 'application/json', '_net/').replace(/(\.[a-z0-9]+)?$/i, '__request.json'));
      await store(key + ' ::request', new TextEncoder().encode(rec.postBody), 'application/json', {
        prefix: '_net/', source: 'request', name: rname, meta: { method, url: rec.url },
      });
    }
    if (ok) log(`net ${method} ${rec.status} ${fmtBytes(bytes.length)} ${rec.url}`, '#4fc3f7');
  }

  function readBody(res, method, url, postBody) {
    const ct = res.headers.get('content-type') || '';
    if (res.status === 204 || res.status === 304) return;
    const clone = res.clone();
    clone.arrayBuffer().then((buf) => {
      if (buf.byteLength > cfg.maxBodyMB * 1048576) {
        recordRuntime({ url, method, status: res.status, contentType: ct, truncated: true, binary: true, buffer: buf.slice(0, cfg.maxBodyMB * 1048576), postBody });
        return;
      }
      if (TEXTISH.test(ct)) recordRuntime({ url, method, status: res.status, contentType: ct, text: new TextDecoder().decode(buf), postBody });
      else recordRuntime({ url, method, status: res.status, contentType: ct, binary: true, buffer: buf, postBody });
    }).catch(() => {});
  }

  function hookRuntime() {
    if (window[OWN]) return;
    window[OWN] = true;

    const origFetch = window.fetch;
    if (origFetch) {
      window.fetch = function (input, init) {
        const url = absolutize(typeof input === 'string' ? input : input?.url, location.href) || '';
        const method = ((init && init.method) || (typeof input === 'object' && input?.method) || 'GET').toUpperCase();
        let postBody = null;
        try {
          if (init?.body && typeof init.body === 'string') postBody = init.body;
          else if (typeof input === 'object' && input?.body && typeof input.body === 'string') postBody = input.body;
        } catch {}
        const p = origFetch.apply(this, arguments);
        if (!url) return p;
        return p.then((res) => { try { readBody(res, method, url, postBody); } catch {} return res; });
      };
    }

    const XHR = XMLHttpRequest.prototype;
    const oOpen = XHR.open, oSend = XHR.send;
    XHR.open = function (m, u) {
      this.__sm = { method: (m || 'GET').toUpperCase(), url: absolutize(u, location.href) || '' };
      return oOpen.apply(this, arguments);
    };
    XHR.send = function (body) {
      const info = this.__sm;
      if (info?.url) {
        this.addEventListener('load', () => {
          if (!cfg.runtime || !inScope(info.url)) return;
          const ct = this.getResponseHeader('content-type') || '';
          const base = { url: info.url, method: info.method, status: this.status, contentType: ct, kind: 'xhr' };
          if (body && typeof body === 'string') base.postBody = body;
          const rt = this.responseType;
          if (rt === '' || rt === 'text') recordRuntime({ ...base, text: String(this.responseText || '') });
          else if (rt === 'arraybuffer' && this.response) recordRuntime({ ...base, binary: true, buffer: this.response });
          else if (rt === 'blob' && this.response) {
            const fr = new FileReader();
            fr.onload = () => recordRuntime({ ...base, binary: true, buffer: fr.result });
            fr.readAsArrayBuffer(this.response);
          } else if (rt === 'json' && this.response) recordRuntime({ ...base, text: JSON.stringify(this.response) });
        });
      }
      return oSend.apply(this, arguments);
    };

    if (cfg.captureWs && window.WebSocket) {
      const OrigWS = window.WebSocket;
      const WS = function (url, protocols) {
        const ws = protocols ? new OrigWS(url, protocols) : new OrigWS(url);
        const abs = absolutize(url, location.href) || String(url);
        const id = 'ws_' + (++netSeq).toString(36);
        const frames = [];
        const flush = () => {
          if (!frames.length) return;
          const wname = uniqueName(fileNameFor(abs, 'application/json', '_net/').replace(/(\.[a-z0-9]+)?$/i, `_${id}.ws.jsonl`));
          store(`${id} ${abs}`, new TextEncoder().encode(frames.join('\n')), 'application/x-ndjson', {
            prefix: '_net/', source: 'runtime', name: wname, meta: { url: abs, kind: 'websocket' },
          });
          frames.length = 0;
        };
        ws.addEventListener('message', (e) => {
          if (!cfg.runtime) return;
          const d = typeof e.data === 'string' ? e.data : '[binary]';
          frames.push(JSON.stringify({ dir: 'in', t: Date.now(), data: d.slice(0, 20000) }));
          if (frames.length >= 25) flush();
        });
        ws.addEventListener('close', flush);
        const oSend = ws.send.bind(ws);
        ws.send = function (data) {
          if (cfg.runtime && typeof data === 'string') frames.push(JSON.stringify({ dir: 'out', t: Date.now(), data: data.slice(0, 20000) }));
          return oSend(data);
        };
        return ws;
      };
      WS.prototype = OrigWS.prototype;
      ['CONNECTING', 'OPEN', 'CLOSING', 'CLOSED'].forEach((k) => { WS[k] = OrigWS[k]; });
      window.WebSocket = WS;
    }
  }

  /* ============================ extraction ============================ */

  const URL_PATTERNS = [
    /(?:src|href|data-src|poster)\s*=\s*["']([^"'\s>]+)["']/gi,
    /srcset\s*=\s*["']([^"']+)["']/gi,
    /import\s*(?:\(\s*)?["']([^"']+)["']/g,
    /require\s*\(\s*["']([^"']+)["']/g,
    /from\s*["']([^"']+)["']/g,
    /["'`]((?:https?:\/\/|\/)[\w\-\/._~%]+\.(?:js|mjs|cjs|jsx|ts|tsx|css|json|map|wasm|rbxm|rbxmx|mesh|dds|tex|pack|lua|luau|svg|xml|webmanifest|otf|ttf|woff2?))(?:\?[^"'`]*)?["'`]/gi,
  ];

  function harvestText(text, base, depth, isCode) {
    if (!text || text.length < 8) return;
    const capped = text.length > 4e6 ? text.slice(0, 4e6) : text;
    for (const re of URL_PATTERNS) {
      re.lastIndex = 0;
      let m;
      while ((m = re.exec(capped))) {
        const raw = m[1];
        if (!raw) continue;
        if (re === URL_PATTERNS[1]) {
          for (const part of raw.split(',')) {
            const u = absolutize(part.trim().split(/\s+/)[0], base);
            if (u) enqueue(u, depth, kindOf(u));
          }
          continue;
        }
        const u = absolutize(raw, base);
        if (!u) continue;
        const k = kindOf(u);
        if (k === 'page' && (!cfg.followLinks || depth >= cfg.maxDepth)) continue;
        enqueue(u, k === 'page' ? depth + 1 : depth, k);
      }
    }
    if (isCode) {
      const sm = /[#@]\s*sourceMappingURL=([^\s'"*]+)/g;
      let m;
      while ((m = sm.exec(capped))) {
        const u = absolutize(m[1], base);
        if (u) enqueue(u, depth, 'map');
      }
    }
  }

  function parseManifest(text, base) {
    if (!cfg.expandJson || text.length > 12e6) return;
    let data;
    try { data = JSON.parse(text); } catch { return; }
    let found = 0;
    const walk = (node, d) => {
      if (found > 20000 || d > 12 || node == null) return;
      if (typeof node === 'string') {
        if (node.length < 300 && /[\/.]/.test(node) && /\.(?:json|rbxm|rbxmx|lua|luau|mesh|dds|tex|pack|js|wasm|ttf|otf|png|jpe?g|svg|xml)/i.test(node)) {
          const u = absolutize(node, base);
          if (u) { enqueue(u, 1, kindOf(u)); found++; }
        }
        return;
      }
      if (Array.isArray(node)) { for (const v of node) walk(v, d + 1); return; }
      if (typeof node === 'object') { for (const k of Object.keys(node)) walk(node[k], d + 1); }
    };
    walk(data, 0);
    if (found) log(`manifest expanded: ${found} paths from ${base}`, '#9ad17a');
  }

  function processHtml(html, base, depth) {
    let doc;
    try { doc = new DOMParser().parseFromString(html, 'text/html'); } catch { return; }
    $$('script', doc).forEach((s) => {
      if (s.src) enqueue(absolutize(s.src, base), depth, 'code');
      if (cfg.inlineCode && s.textContent.trim().length > 20) {
        store(base + '#inline-js-' + hash32(s.textContent), new TextEncoder().encode(s.textContent), 'text/javascript', {
          name: '_inline/' + new URL(base).host + '/' + hash32(s.textContent).toString(36) + '.js',
        });
        harvestText(s.textContent, base, depth, true);
      }
    });
    $$('style', doc).forEach((s) => {
      if (cfg.inlineCode && s.textContent.trim().length > 20) {
        store(base + '#inline-css-' + hash32(s.textContent), new TextEncoder().encode(s.textContent), 'text/css', {
          name: '_inline/' + new URL(base).host + '/' + hash32(s.textContent).toString(36) + '.css',
        });
      }
    });
    $$('link[href]', doc).forEach((l) => {
      const rel = (l.getAttribute('rel') || '').toLowerCase();
      if (!/stylesheet|preload|modulepreload|manifest|icon|alternate|prefetch/.test(rel)) return;
      const u = absolutize(l.getAttribute('href'), base);
      if (u) enqueue(u, depth, kindOf(u));
    });
    $$('[src], [data-src], [poster]', doc).forEach((el) => {
      const u = absolutize(el.getAttribute('src') || el.getAttribute('data-src') || el.getAttribute('poster'), base);
      if (u) enqueue(u, depth, kindOf(u));
    });
    if (cfg.followLinks && depth < cfg.maxDepth) {
      $$('a[href]', doc).forEach((a) => {
        const u = absolutize(a.getAttribute('href'), base);
        if (u) enqueue(u, depth + 1, 'page');
      });
    }
    harvestText(html, base, depth, false);
  }

  async function handle(url, depth, kind) {
    const binary = kind === 'asset';
    let res;
    try { res = await request(url, binary); }
    catch (e) { log('fail ' + url + ' — ' + e.message, '#ff7a8a'); return; }
    if (res.status >= 400) { log(res.status + ' ' + url, '#ff7a8a'); return; }

    const ct = res.ct || '';
    const k = kind === 'page' && ct && !/html/.test(ct) ? kindOf(url, ct) : kind;
    if (k === 'asset' && !cfg.assets) return;

    if (binary) {
      const bytes = new Uint8Array(res.data);
      await store(url, bytes, ct);
      log(`asset ${fmtBytes(bytes.length)} ${url}`);
      if (/^rbxmx?$/.test(extOf(url)) || /rbxmx?/.test(ct)) await extractRbx(bytes, url);
      return;
    }

    const text = typeof res.data === 'string' ? res.data : decode(new Uint8Array(res.data), ct);

    if (k === 'page') {
      await store(url, new TextEncoder().encode(text), 'text/html');
      processHtml(text, url, depth);
      log(`page ${url}`);
    } else {
      await store(url, new TextEncoder().encode(text), ct);
      if (cfg.expandJson && /json/.test(ct)) parseManifest(text, url);
      harvestText(text, url, depth, k === 'code');
      log(`code ${fmtBytes(text.length)} ${url}`);
    }

    if (k === 'code' && cfg.sourcemaps) {
      const m = /[#@]\s*sourceMappingURL=([^\s'"*]+)/.exec(text);
      const smUrl = m ? absolutize(m[1], url) : url.replace(/(\.m?js)(\?.*)?$/, '$1.map$2');
      if (smUrl) {
        try {
          const sm = await request(smUrl, false);
          if (sm.status < 400) {
            const body = typeof sm.data === 'string' ? sm.data : decode(new Uint8Array(sm.data), sm.ct);
            await store(smUrl, new TextEncoder().encode(body), 'application/json');
            extractSources(body, smUrl);
          }
        } catch {}
      }
    }
  }

  function extractSources(mapJson, mapUrl) {
    let map;
    try { map = JSON.parse(mapJson); } catch { return; }
    if (!Array.isArray(map.sources)) return;
    let host = 'src';
    try { host = new URL(mapUrl).host; } catch {}
    map.sources.forEach((src, i) => {
      const content = map.sourcesContent?.[i];
      const clean = String(src).replace(/^webpack:\/\/\/?/, '').replace(/^\.\//, '').replace(/[?#].*$/, '');
      if (typeof content === 'string') {
        const base = ('_sources/' + host + '/' + clean).replace(/[^\w.\-\/]/g, '_');
        store(mapUrl + '#src-' + i, new TextEncoder().encode(content), 'text/plain', { name: uniqueName(base) });
      } else if (/^(https?:)?\/\//.test(src) || src.startsWith('/')) {
        enqueue(absolutize(src, mapUrl), 0, 'code');
      }
    });
    log(`sourcemap expanded: ${map.sources.length} sources`);
  }

  /* ============================ rbx parsing ========================== */

  const RBXM_MAGIC = [0x3C, 0x72, 0x6F, 0x62, 0x6C, 0x6F, 0x78, 0x21, 0x89, 0xFF, 0x0D, 0x0A, 0x1A, 0x0A];
  const STRING_INTERLEAVED = new Set(['Script', 'LocalScript', 'ModuleScript']);
  const LUA_HINT = /(?:local\s+[\w_]+|function\s*\(|require\s*\(|game:GetService|Instance\.new)/m;

  async function pump(bytes, fmt) {
    const s = new Blob([bytes]).stream().pipeThrough(new DecompressionStream(fmt));
    return new Uint8Array(await new Response(s).arrayBuffer());
  }

  async function inflate(bytes) {
    try { return await pump(bytes, 'deflate'); }
    catch { return await pump(bytes, 'deflate-raw'); }
  }

  async function readRbxChunks(buf) {
    for (let i = 0; i < 14; i++) if (buf[i] !== RBXM_MAGIC[i]) throw new Error('not rbxm');
    const dv = new DataView(buf.buffer, buf.byteOffset, buf.byteLength);
    let p = 32; // magic + version + class count + instance count + reserved
    const out = [];
    while (p + 16 <= buf.length) {
      const name = String.fromCharCode(buf[p], buf[p + 1], buf[p + 2], buf[p + 3]);
      p += 4;
      const comp = dv.getUint32(p, true); p += 4;
      const raw = dv.getUint32(p, true); p += 4;
      p += 4;
      if (p + comp > buf.length) throw new Error('truncated chunk');
      const data = comp ? await inflate(buf.subarray(p, p + comp)) : buf.subarray(p, p + raw);
      p += comp;
      out.push({ name, data });
      if (name === 'END\0') break;
    }
    return out;
  }

  async function parseRbxm(buf) {
    const chunks = await readRbxChunks(buf);
    const classes = new Map(), refsByClass = new Map(), shared = new Set();
    const names = new Map(), parents = new Map(), sstr = [], sources = [];

    for (const ch of chunks) {
      const b = ch.data;
      const c = new DataView(b.buffer, b.byteOffset, b.byteLength);
      let q = 0;
      const need = (n) => { if (q + n > b.length) throw new Error('truncated'); };
      const adv = (n) => { need(n); q += n; };
      const u8 = () => { need(1); return b[q++]; };
      const u32 = () => { need(4); const v = c.getUint32(q, true); q += 4; return v; };
      const i32 = () => { need(4); const v = c.getInt32(q, true); q += 4; return v; };
      const str = () => { const n = u32(); need(n); const s = decodeBytes(b.subarray(q, q + n)); q += n; return s; };

      if (ch.name === 'INST') {
        const cid = i32();
        const cname = cid === -1 ? str() : (classes.get(cid) || 'Class' + cid);
        if (cid !== -1) classes.set(cid, cname);
        u8();
        const n = u32();
        const refs = [];
        for (let i = 0; i < n; i++) refs.push(i32());
        refsByClass.set(cid, refs);
        const inter = STRING_INTERLEAVED.has(cname);
        for (let i = 0; i < n; i++) {
          u8();
          const r = i32();
          if (inter && u8()) shared.add(r);
        }
      } else if (ch.name === 'SSTR') {
        u32();
        const n = u32();
        for (let i = 0; i < n; i++) sstr.push(str());
      } else if (ch.name === 'PRNT') {
        const n = u32();
        for (let i = 0; i < n; i++) { const child = i32(); const parent = i32(); parents.set(child, parent); }
      } else if (ch.name === 'PROP') {
        const cid = i32();
        const prop = str();
        const type = u8();
        const refs = refsByClass.get(cid) || [];
        for (const r of refs) {
          if (type === 0x01) {
            const v = shared.has(r) ? (sstr[u32()] ?? '') : str();
            if (prop === 'Name') names.set(r, v);
            else if (prop === 'Source') sources.push({ ref: r, cls: classes.get(cid) || 'Script', code: v });
            continue;
          }
          switch (type) {
            case 0x02: case 0x09: case 0x0A: adv(1); break;
            case 0x03: case 0x04: case 0x0B: case 0x0F: case 0x12: case 0x13: adv(4); break;
            case 0x05: case 0x06: case 0x17: case 0x1B: adv(8); break;
            case 0x07: case 0x11: case 0x18: adv(16); break;
            case 0x08: adv(24); break;
            case 0x0C: case 0x1A: adv(3); break;
            case 0x0D: adv(8); break;
            case 0x0E: adv(12); break;
            case 0x10: adv(48); break;
            case 0x14: adv(6); break;
            case 0x15: { const k = u32(); adv(k * 12); break; }
            case 0x16: { const k = u32(); adv(k * 7); break; }
            case 0x19: { const custom = u8(); adv(custom ? 12 : 1); break; }
            case 0x1C: adv(4); break;
            default: throw new Error('prop type 0x' + type.toString(16));
          }
        }
      }
    }

    const pathOf = (ref) => {
      const parts = [];
      let cur = ref, guard = 0;
      while (cur != null && guard++ < 64) {
        const nm = names.get(cur);
        if (nm) parts.unshift(nm);
        cur = parents.get(cur);
      }
      return parts.join('/');
    };

    return sources.map((s) => ({ class: s.cls, ref: s.ref, path: pathOf(s.ref), code: s.code }));
  }

  function parseRbxmx(xml) {
    const doc = new DOMParser().parseFromString(xml, 'text/xml');
    const out = [];
    const walk = (node, trail) => {
      for (const el of Array.from(node.children)) {
        if (el.tagName !== 'Item') continue;
        const cls = el.getAttribute('class') || 'Item';
        const nameEl = Array.from(el.children).find((c) => c.tagName === 'string' && c.getAttribute('name') === 'Name');
        const nm = nameEl ? nameEl.textContent.trim() : '';
        const next = trail.concat(nm || cls);
        for (const c of Array.from(el.children)) {
          if (c.tagName === 'ProtectedString' && c.getAttribute('name') === 'Source') {
            out.push({ class: cls, ref: out.length, path: next.join('/'), code: c.textContent });
          }
        }
        walk(el, next);
      }
    };
    walk(doc.documentElement, []);
    return out;
  }

  async function sniffRbx(buf) {
    const chunks = await readRbxChunks(buf);
    const out = [];
    for (const ch of chunks) {
      if (ch.name !== 'PROP' && ch.name !== 'SSTR') continue;
      const b = ch.data;
      for (let i = 0; i + 4 < b.length; i++) {
        const n = (b[i] | b[i + 1] << 8 | b[i + 2] << 16 | b[i + 3] << 24) >>> 0;
        if (n < 32 || n > 4e6 || i + 4 + n > b.length) continue;
        const s = decodeBytes(b.subarray(i + 4, i + 4 + n));
        if (/[\x00-\x08\x0e-\x1f]/.test(s.slice(0, 400))) continue;
        if (!LUA_HINT.test(s)) continue;
        out.push({ class: 'Sniffed', ref: out.length, path: 'sniffed_' + out.length, code: s });
        i += 3 + n;
      }
    }
    return out;
  }

  async function extractRbx(bytes, url) {
    if (!cfg.rbxLua) return;
    let host = 'x';
    try { host = new URL(url).host; } catch {}
    let items = [];
    try {
      if (extOf(url) === 'rbxmx') items = parseRbxmx(decodeBytes(bytes));
      else items = await parseRbxm(bytes);
    } catch (e) {
      log('rbx parse failed (' + e.message + ') — sniffing', '#ffb86b');
      try { items = await sniffRbx(bytes); } catch {}
    }
    if (!items.length) { log('no Lua found in ' + url, '#ffb86b'); return; }
    for (const it of items) {
      const clean = (it.path || it.class + '_' + it.ref).replace(/[^\w.\-\/]/g, '_').replace(/^\/+/, '') || 'script';
      const name = uniqueName('_rbx/' + host + '/' + clean + '.luau');
      await store(url + '#rbx-' + hash32(name), new TextEncoder().encode(it.code), 'text/plain', { name, source: 'rbx' });
    }
    log(`rbx: extracted ${items.length} Lua source(s) from ${url}`, '#d8a0ff');
  }

  /* ============================ rbx seeding =========================== */

  const ENGINE_FILES = [
    'WebClient.js', 'WebClient.js.map', 'WebClient.metadata.json', 'WebClient.wasm',
    'WebClient.worker.js', 'stub.js', 'audio-processor-fast.js', 'audio-processor.js',
    'content/configs/InExperiencePatchConfig/InExperiencePatchConfig.json',
    'content/configs/UniversalAppPatchConfig/UniversalAppPatchConfig.json',
    'content/guac/defaultConfigs/GuacDefaultPolicy-GlobalDist.json',
    'shaders/shaders_glsles3_web.pack', 'shaders/shaders_glsles2_web.pack',
    'ExtraContent/models/InExperience/InExperience.rbxm',
  ];

  function detectEngineBase() {
    const hay = document.documentElement.innerHTML + ' ' + performance.getEntriesByType('resource').map((e) => e.name).join(' ');
    const m = /https:\/\/setup\.rbxcdn\.com\/webclient\/version-[A-Za-z0-9._-]+-RobloxWebClient/.exec(hay);
    return m ? m[0] : null;
  }

  function seedTiming() {
    if (!cfg.seedTiming) return;
    let n = 0;
    performance.getEntriesByType('resource').forEach((e) => {
      if (!inScope(e.name)) return;
      enqueue(e.name, 0, kindOf(e.name));
      n++;
    });
    if (n) log(`seeded ${n} loaded resources from timing buffer`, '#9ad17a');
  }

  function seedEngine() {
    const base = detectEngineBase();
    if (!base) { log('engine base not detected — is the client loaded?', '#ffb86b'); return; }
    log('engine base: ' + base, '#9ad17a');
    ENGINE_FILES.forEach((f) => enqueue(base + '/' + f, 0, kindOf(f)));
  }

  /* ============================== worker ============================== */

  function updateStats() {
    if (!statsBox) return;
    statsBox.textContent = `${files.size} files (${runtimeCount} runtime) · ${fmtBytes(totalBytes)} · queue ${queue.length}` + (USE_OPFS ? ' · OPFS' : ' · RAM');
  }

  // drain keeps a fixed number of slots full until the queue is genuinely empty
  async function drain() {
    const inflight = new Set();
    const width = Math.max(1, Math.min(12, cfg.concurrency));
    for (;;) {
      while (!stopFlag && inflight.size < width && queue.length) {
        const job = queue.shift();
        if (!job || seen.has(job.url)) continue;
        seen.add(job.url);
        const p = handle(job.url, job.depth, job.kind)
          .catch((e) => log('error ' + job.url + ' — ' + e.message, '#ff7a8a'))
          .then(() => { inflight.delete(p); updateStats(); });
        inflight.add(p);
        if (cfg.delay) await sleep(cfg.delay);
      }
      if (!inflight.size) {
        if (!queue.length || stopFlag) break;
        await sleep(20);
        continue;
      }
      await Promise.race(inflight);
    }
    if (inflight.size) await Promise.all(inflight);
  }

  async function start() {
    if (running) return;
    running = true; stopFlag = false;
    await initOPFS();
    files.clear(); usedNames.clear(); memStore.clear(); queued.clear(); seen.clear();
    queue.length = 0; netIndex.length = 0;
    totalBytes = 0; runtimeCount = 0;
    renderFiles(); updateStats();
    log('=== harvest started: ' + location.href + ' ===');

    await store(location.href, new TextEncoder().encode('<!DOCTYPE html>\n' + document.documentElement.outerHTML), 'text/html', { source: 'seed' });
    processHtml(document.documentElement.outerHTML, location.href, 0);
    seedTiming();
    if (cfg.seedKnown) seedEngine();

    await drain();

    stopFlag = false; running = false;
    log(`=== crawl done: ${files.size} files, ${fmtBytes(totalBytes)} ===`, '#00e0a4');
    toast('Crawl done — runtime capture still live');
    renderFiles();
  }

  async function replay() {
    const reqs = [...files.entries()].filter(([, f]) => f.source === 'request');
    if (!reqs.length) return toast('No captured request bodies');
    if (running) return toast('Already running');
    running = true; stopFlag = false;
    log(`replaying ${reqs.length} captured request(s)`);
    for (const [, f] of reqs) {
      if (stopFlag) break;
      const url = f.meta?.url;
      if (!url) continue;
      try {
        const body = new TextDecoder().decode(await readFile(f.name));
        const res = await request(url, false, f.meta.method || 'POST', body);
        if (res.status < 400) {
          const text = typeof res.data === 'string' ? res.data : decode(new Uint8Array(res.data), res.ct);
          await store(url + ' #replay' + Date.now(), new TextEncoder().encode(text), res.ct || 'application/json', { prefix: '_replay/', source: 'replay' });
          parseManifest(text, url);
          log(`replayed ${res.status} ${url}`, '#4fc3f7');
        } else log(`replay ${res.status} ${url}`, '#ff7a8a');
      } catch (e) { log('replay fail ' + url + ' — ' + e.message, '#ff7a8a'); }
      await sleep(400);
    }
    running = false;
    log('replay complete', '#00e0a4');
  }

  /* ================================= zip ============================== */

  const CRC_TABLE = (() => {
    const t = new Uint32Array(256);
    for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
    return t;
  })();

  function crcUpdate(c, buf) {
    for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xFF] ^ (c >>> 8);
    return c;
  }

  function dosStamp(d) {
    return { time: (d.getHours() << 11) | (d.getMinutes() << 5) | (d.getSeconds() >> 1), date: ((d.getFullYear() - 1980) << 9) | ((d.getMonth() + 1) << 5) | d.getDate() };
  }

  function localHeader(nameBytes, crc, size, time, date) {
    const h = new Uint8Array(30 + nameBytes.length);
    const dv = new DataView(h.buffer);
    dv.setUint32(0, 0x04034b50, true); dv.setUint16(4, 20, true); dv.setUint16(6, 0x0800, true);
    dv.setUint16(8, 0, true); dv.setUint16(10, time, true); dv.setUint16(12, date, true);
    dv.setUint32(14, crc, true); dv.setUint32(18, size, true); dv.setUint32(22, size, true);
    dv.setUint16(26, nameBytes.length, true); dv.setUint16(28, 0, true);
    h.set(nameBytes, 30);
    return h;
  }

  function centralHeader(nameBytes, crc, size, offset, time, date) {
    const r = new Uint8Array(46 + nameBytes.length);
    const dv = new DataView(r.buffer);
    dv.setUint32(0, 0x02014b50, true); dv.setUint16(4, 20, true); dv.setUint16(6, 20, true);
    dv.setUint16(8, 0x0800, true); dv.setUint16(10, 0, true); dv.setUint16(12, time, true);
    dv.setUint16(14, date, true); dv.setUint32(16, crc, true); dv.setUint32(20, size, true);
    dv.setUint32(24, size, true); dv.setUint16(28, nameBytes.length, true); dv.setUint32(42, offset, true);
    r.set(nameBytes, 46);
    return r;
  }

  async function exportZip() {
    if (!files.size) return toast('Nothing captured yet');
    if (running) return toast('Stop the harvest first');
    if (!sessionDir) await initOPFS();
    toast('Building archive…');

    const manifest = { url: location.href, ua: navigator.userAgent, at: new Date().toISOString(), version: VERSION, files: [], requests: netIndex };
    for (const [k, f] of files) manifest.files.push({ key: k, ...f });
    await store('__manifest', new TextEncoder().encode(JSON.stringify(manifest, null, 2)), 'application/json', { name: uniqueName('_manifest.json'), source: 'meta' });

    // streaming: never holds more than one file in memory
    const sink = USE_OPFS ? await (await sessionDir.getFileHandle('__archive.zip', { create: true })).createWritable() : null;
    const parts = [];
    const central = [];
    const { time, date } = dosStamp(new Date());
    let offset = 0;

    for (const [, f] of files) {
      const nameBytes = new TextEncoder().encode(f.name);
      let size = f.size, crc = 0xFFFFFFFF;

      if (USE_OPFS) {
        const fh = await readFileHandle(f.name);
        const fr = await fh.getFile();
        size = fr.size;
        const reader = fr.stream().getReader();
        for (;;) {
          const { done, value } = await reader.read();
          if (done) break;
          crc = crcUpdate(crc, value);
        }
        crc = (crc ^ 0xFFFFFFFF) >>> 0;

        await sink.write(localHeader(nameBytes, crc, size, time, date));
        const reader2 = (await fh.getFile()).stream().getReader();
        for (;;) {
          const { done, value } = await reader2.read();
          if (done) break;
          await sink.write(value);
        }
      } else {
        const data = memStore.get(f.name);
        if (!data) continue;
        size = data.length;
        crc = (crcUpdate(crc, data) ^ 0xFFFFFFFF) >>> 0;
        parts.push(localHeader(nameBytes, crc, size, time, date), data);
      }

      central.push({ nameBytes, crc, size, offset });
      offset += 30 + nameBytes.length + size;
    }

    const cdStart = offset;
    for (const c of central) {
      const rec = centralHeader(c.nameBytes, c.crc, c.size, c.offset, time, date);
      if (USE_OPFS) await sink.write(rec); else parts.push(rec);
      offset += rec.length;
    }
    const cdSize = offset - cdStart;
    const eocd = new Uint8Array(22);
    const dv = new DataView(eocd.buffer);
    dv.setUint32(0, 0x06054b50, true);
    dv.setUint16(8, central.length, true); dv.setUint16(10, central.length, true);
    dv.setUint32(12, cdSize, true); dv.setUint32(16, cdStart, true);

    let blob;
    if (USE_OPFS) {
      await sink.write(eocd);
      await sink.close();
      blob = await (await sessionDir.getFileHandle('__archive.zip')).getFile();
    } else {
      parts.push(eocd);
      const total = parts.reduce((a, p) => a + p.length, 0);
      const out = new Uint8Array(total);
      let p = 0;
      for (const c of parts) { out.set(c, p); p += c.length; }
      blob = new Blob([out], { type: 'application/zip' });
    }

    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `source_${location.hostname.replace(/^www\./, '')}_${Date.now()}.zip`;
    document.body.appendChild(a); a.click();
    setTimeout(() => { URL.revokeObjectURL(url); a.remove(); }, 8000);

    log(`archive exported: ${central.length} entries, ${fmtBytes(offset)}`, '#00e0a4');
  }

  /* ================================= UI =============================== */

  function scheduleRender() {
    if (renderTimer) return;
    renderTimer = setTimeout(() => { renderTimer = null; renderFiles(); }, 250);
  }

  function renderFiles() {
    if (!fileList) return;
    const filter = ($('#f-filter')?.value || '').toLowerCase();
    const items = [...files.entries()].filter(([k, f]) => !filter || f.name.toLowerCase().includes(filter));
    fileList.innerHTML = '';
    for (const [key, f] of items.slice(-500).reverse()) {
      const row = document.createElement('div');
      row.className = 'fitem';
      const ext = (f.name.split('.').pop() || '?').toLowerCase();
      row.innerHTML = `<span class="ext e-${ext}">${ext.slice(0, 4)}</span><span class="fname"></span>` +
        (f.source === 'runtime' ? '<span class="net">NET</span>' : '') +
        (f.source === 'rbx' ? '<span class="net lua">LUA</span>' : '') +
        `<span class="fsize">${fmtBytes(f.size)}</span>`;
      row.querySelector('.fname').textContent = f.name;
      row.title = key;
      row.addEventListener('click', async () => {
        const bytes = await readFile(f.name);
        if (!bytes) return;
        window.open(URL.createObjectURL(new Blob([bytes], { type: f.type || 'application/octet-stream' })), '_blank');
      });
      fileList.appendChild(row);
    }
    if (items.length > 500) {
      const more = document.createElement('div');
      more.className = 'more';
      more.textContent = `+${items.length - 500} more`;
      fileList.appendChild(more);
    }
  }

  function buildUI() {
    const host = document.createElement('div');
    host.id = 'sourceminer-host';
    host.style.cssText = 'all:initial;position:fixed;z-index:2147483647;inset:0;pointer-events:none;';
    document.documentElement.appendChild(host);
    shadow = host.attachShadow({ mode: 'open' });

    shadow.innerHTML = `
      <style>
        :host { all: initial; }
        * { box-sizing: border-box; font-family: ui-monospace, SFMono-Regular, Menlo, Consolas, monospace; }
        #fab { pointer-events: auto; position: fixed; bottom: 18px; right: 18px; width: 46px; height: 46px;
          border-radius: 50%; background: #00b487; color: #04120d; border: 0; font-size: 19px;
          font-weight: 800; cursor: pointer; box-shadow: 0 8px 22px rgba(0,0,0,.5); }
        .panel { pointer-events: auto; position: fixed; top: 48px; right: 18px; width: 480px; max-height: 84vh;
          display: flex; flex-direction: column; background: #0e1116; color: #d7e0ea; border: 1px solid #2b3542;
          border-radius: 10px; box-shadow: 0 18px 50px rgba(0,0,0,.6); font-size: 12px; overflow: hidden; }
        header { display: flex; align-items: center; gap: 8px; padding: 8px 10px; background: #11161d;
          border-bottom: 1px solid #222b36; cursor: move; user-select: none; }
        header b { color: #00e0a4; font-size: 12px; letter-spacing: .5px; }
        header .ver { color: #566372; font-size: 10px; }
        header .sp { flex: 1; }
        .btn { background: #1a2230; color: #cfdae6; border: 1px solid #2c3a4c; border-radius: 5px;
          padding: 4px 8px; font-size: 11px; cursor: pointer; }
        .btn:hover { background: #23303f; }
        .btn.primary { background: #00b487; border-color: #00b487; color: #04120d; font-weight: 700; }
        .btn.danger { background: #3a1620; border-color: #5d2333; color: #ffb3c1; }
        .btn.live { background: #4fc3f7; border-color: #4fc3f7; color: #04120d; }
        nav { display: flex; border-bottom: 1px solid #222b36; background: #10151c; }
        nav button { flex: 1; background: none; border: 0; border-bottom: 2px solid transparent;
          color: #7b8899; padding: 7px 4px; font-size: 11px; cursor: pointer; }
        nav button.on { color: #00e0a4; border-bottom-color: #00e0a4; background: #131a23; }
        .body { padding: 10px; overflow: auto; }
        .tab { display: none; } .tab.on { display: block; }
        label.chk { display: flex; align-items: center; gap: 6px; padding: 3px 0; color: #a8b6c6; cursor: pointer; }
        .grid2 { display: grid; grid-template-columns: 1fr 1fr; gap: 0 10px; }
        input[type=text], input[type=number], select { width: 100%; background: #0a0e13; color: #d7e0ea;
          border: 1px solid #2b3542; border-radius: 5px; padding: 5px 7px; font-size: 11px; }
        .row { display: flex; gap: 6px; margin: 7px 0; align-items: center; }
        .row > * { min-width: 0; }
        .hint { color: #5f6d7d; font-size: 10px; line-height: 1.5; margin: 4px 0 8px; }
        .fieldset { border: 1px solid #222b36; border-radius: 7px; padding: 8px; margin: 8px 0; }
        .fieldset h4 { margin: 0 0 6px; font-size: 11px; color: #8fa0b3; font-weight: 600; }
        #stats { font-size: 11px; color: #00e0a4; padding: 4px 0; }
        #f-list { max-height: 340px; overflow: auto; border: 1px solid #1d2530; border-radius: 5px; margin-top: 6px; }
        .fitem { display: flex; gap: 6px; align-items: center; padding: 3px 5px; border-bottom: 1px solid #151d26; cursor: pointer; }
        .fitem:hover { background: #131a23; }
        .fname { flex: 1; color: #9fb2c6; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; font-size: 10px; }
        .fsize { color: #566372; font-size: 10px; }
        .net { color: #04120d; background: #4fc3f7; border-radius: 3px; padding: 1px 3px; font-size: 8px; font-weight: 700; }
        .net.lua { background: #d8a0ff; }
        .ext { color: #04120d; background: #4a5a6b; border-radius: 3px; padding: 1px 4px; font-size: 9px; text-transform: uppercase; }
        .e-js, .e-mjs { background: #f0d049; } .e-css { background: #4fa3ff; } .e-html { background: #ff8f5e; }
        .e-json, .e-map { background: #9ad17a; } .e-lua, .e-luau { background: #7fb3ff; }
        .e-rbxm, .e-rbxmx, .e-mesh, .e-pack { background: #d8a0ff; } .e-wasm { background: #ff7a8a; }
        .more { padding: 5px; color: #566372; font-size: 10px; text-align: center; }
        #log { font-size: 10px; color: #7b8899; max-height: 340px; overflow: auto; line-height: 1.5; }
        .toast { pointer-events: none; position: fixed; bottom: 24px; left: 50%; transform: translateX(-50%);
          background: #00b487; color: #04120d; padding: 7px 14px; border-radius: 20px; font-size: 12px;
          font-weight: 700; box-shadow: 0 8px 24px rgba(0,0,0,.5); }
        .hidden { display: none !important; }
      </style>
      <button id="fab" title="SourceMiner (Alt+Shift+S)">⛏</button>
      <div class="panel hidden">
        <header id="head"><b>SOURCEMINER</b><span class="ver">v${VERSION}</span><span class="sp"></span>
          <button class="btn" id="min">—</button></header>
        <nav>
          <button data-tab="run" class="on">Harvest</button>
          <button data-tab="files">Files</button>
          <button data-tab="opts">Options</button>
          <button data-tab="log">Log</button>
        </nav>
        <div class="body">
          <div class="tab on" id="tab-run">
            <div class="hint">Files spool to disk as they arrive, so a crash no longer costs you the session. Seed, play, export.</div>
            <div id="stats">0 files · 0 B · queue 0</div>
            <div class="row">
              <button class="btn primary" id="go">Start harvest</button>
              <button class="btn" id="cap">Runtime: on</button>
              <button class="btn danger" id="stop">Stop</button>
            </div>
            <div class="row">
              <button class="btn" id="seed">Seed engine files</button>
              <button class="btn" id="replay">Replay POSTs</button>
            </div>
            <div class="row">
              <button class="btn" id="zip">Download ZIP</button>
              <button class="btn" id="sessions">Recover session</button>
              <button class="btn" id="wipe">Reset</button>
            </div>
          </div>
          <div class="tab" id="tab-files">
            <input type="text" id="f-filter" placeholder="filter files by name">
            <div id="f-list"></div>
          </div>
          <div class="tab" id="tab-opts">
            <div class="fieldset">
              <h4>Scope</h4>
              <select id="o-scope">
                <option value="all">Everything reachable</option>
                <option value="hosts">Roblox hosts + origin</option>
                <option value="origin">Same origin only</option>
              </select>
              <label class="chk"><input type="checkbox" id="o-follow"> Follow page links</label>
              <label class="chk"><input type="checkbox" id="o-inline"> Capture inline code</label>
              <label class="chk"><input type="checkbox" id="o-maps"> Follow sourcemaps</label>
              <label class="chk"><input type="checkbox" id="o-assets"> Include binary assets</label>
              <label class="chk"><input type="checkbox" id="o-rbx"> Extract Lua from .rbxm</label>
              <label class="chk"><input type="checkbox" id="o-timing"> Seed from resource timing</label>
              <label class="chk"><input type="checkbox" id="o-known"> Seed known engine paths</label>
              <label class="chk"><input type="checkbox" id="o-json"> Expand JSON manifests</label>
            </div>
            <div class="fieldset">
              <h4>Runtime capture</h4>
              <label class="chk"><input type="checkbox" id="o-rt"> Capture fetch / XHR / WS</label>
              <label class="chk"><input type="checkbox" id="o-req"> Save request payloads</label>
              <label class="chk"><input type="checkbox" id="o-ws"> Capture WebSocket frames</label>
            </div>
            <div class="fieldset">
              <h4>Limits</h4>
              <div class="grid2">
                <label>Depth <input type="number" id="o-depth" min="0" max="8"></label>
                <label>Max files <input type="number" id="o-files" min="1" max="1000000"></label>
                <label>Max MB (0=off) <input type="number" id="o-mb" min="0"></label>
                <label>Max body MB <input type="number" id="o-body" min="1" max="2048"></label>
                <label>Parallel <input type="number" id="o-conc" min="1" max="12"></label>
                <label>Delay ms <input type="number" id="o-delay" min="0" step="50"></label>
              </div>
              <label>Exclude regex <input type="text" id="o-exclude"></label>
            </div>
          </div>
          <div class="tab" id="tab-log">
            <div class="row"><button class="btn danger" id="logclear">Clear</button></div>
            <div id="log"></div>
          </div>
        </div>
      </div>
    `;

    logBox = $('#log'); statsBox = $('#stats'); fileList = $('#f-list'); panel = $('.panel');

    $$('nav button').forEach((b) => b.addEventListener('click', () => {
      $$('nav button').forEach((x) => x.classList.toggle('on', x === b));
      $$('.tab').forEach((t) => t.classList.toggle('on', t.id === 'tab-' + b.dataset.tab));
    }));

    $('#fab').addEventListener('click', () => panel.classList.toggle('hidden'));
    $('#min').addEventListener('click', () => panel.classList.add('hidden'));

    const head = $('#head');
    let drag = null;
    head.addEventListener('mousedown', (e) => {
      if (e.target.tagName === 'BUTTON') return;
      drag = { x: e.clientX, y: e.clientY, r: panel.getBoundingClientRect() };
      e.preventDefault();
    });
    window.addEventListener('mousemove', (e) => {
      if (!drag) return;
      panel.style.left = drag.r.left + (e.clientX - drag.x) + 'px';
      panel.style.top = drag.r.top + (e.clientY - drag.y) + 'px';
      panel.style.right = 'auto';
    });
    window.addEventListener('mouseup', () => { drag = null; });

    capToggle = $('#cap');
    const paintCap = () => {
      capToggle.textContent = 'Runtime: ' + (cfg.runtime ? 'on' : 'off');
      capToggle.classList.toggle('live', cfg.runtime);
    };
    paintCap();
    capToggle.addEventListener('click', () => { cfg.runtime = !cfg.runtime; saveCfg(); paintCap(); });

    $('#go').addEventListener('click', start);
    $('#stop').addEventListener('click', () => { stopFlag = true; log('stop requested', '#ffb86b'); });
    $('#zip').addEventListener('click', exportZip);
    $('#seed').addEventListener('click', seedEngine);
    $('#replay').addEventListener('click', replay);
    $('#sessions').addEventListener('click', async () => {
      const list = await listSessions();
      if (!list.length) return toast('No stored sessions');
      const pick = prompt('Session to recover:\n\n' + list.slice(0, 20).join('\n'), list[0]);
      if (!pick) return;
      try { await initOPFS(); await adoptSession(pick); toast('Recovered'); }
      catch (e) { toast('Recovery failed: ' + e.message); }
    });
    $('#wipe').addEventListener('click', () => {
      files.clear(); usedNames.clear(); memStore.clear(); queued.clear(); seen.clear();
      queue.length = 0; netIndex.length = 0; totalBytes = 0; runtimeCount = 0;
      renderFiles(); updateStats(); log('reset');
    });
    $('#logclear').addEventListener('click', () => { logBox.innerHTML = ''; });
    $('#f-filter').addEventListener('input', renderFiles);

    const bind = (id, key, num) => {
      const el = $('#' + id);
      if (el.type === 'checkbox') { el.checked = cfg[key]; el.addEventListener('change', () => { cfg[key] = el.checked; saveCfg(); }); }
      else { el.value = cfg[key]; el.addEventListener('change', () => { cfg[key] = num ? +el.value : el.value; saveCfg(); }); }
    };
    bind('o-scope', 'scope'); bind('o-follow', 'followLinks'); bind('o-inline', 'inlineCode');
    bind('o-maps', 'sourcemaps'); bind('o-assets', 'assets'); bind('o-rbx', 'rbxLua');
    bind('o-timing', 'seedTiming'); bind('o-known', 'seedKnown'); bind('o-json', 'expandJson');
    bind('o-rt', 'runtime'); bind('o-req', 'captureRequests'); bind('o-ws', 'captureWs');
    bind('o-depth', 'maxDepth', true); bind('o-files', 'maxFiles', true); bind('o-mb', 'maxMB', true);
    bind('o-body', 'maxBodyMB', true); bind('o-conc', 'concurrency', true); bind('o-delay', 'delay', true);
    bind('o-exclude', 'exclude');

    GM_registerMenuCommand('Toggle SourceMiner', () => panel.classList.toggle('hidden'));
    log('ready — hooks installed on ' + location.hostname);
  }

  /* ================================ boot ============================== */

  hookRuntime();

  async function boot() {
    if (document.getElementById('sourceminer-host')) return;
    if (!document.documentElement) return setTimeout(boot, 30);
    buildUI();          // before initOPFS so quota/fallback lines have a log target
    await initOPFS();
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', boot, { once: true });
  else boot();
})();