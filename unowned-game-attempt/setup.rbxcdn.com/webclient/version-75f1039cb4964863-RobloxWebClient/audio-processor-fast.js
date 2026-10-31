class AudioProcessor extends AudioWorkletProcessor {
    constructor(options) {
        super();
        this.ready = false;
        this.bufferFlag = 0;
        this.bufferIndex = 0;
        this.bufferSize = 0;
        this.halfFloats = 0;
        this.channelCount = options.outputChannelCount;
        this.outputView = null;
        this.syncView = null;
        this.port.onmessage = (event) => {
            const { data } = event;
            if (data && data.heapBuffer) {
                this.bufferSize = data.bufferSize;
                this.halfFloats = data.bufferSize * data.channelCount;
                this.outputView = new Float32Array(data.heapBuffer, data.dataOffset, this.halfFloats * 2);
                this.syncView = new Int32Array(data.heapBuffer, data.syncOffset, 1);
                this.ready = true;
            } else {
                this.ready = false;
            }
        };
    }
    process(inputs, outputs, parameters) {
        const output = outputs[0];
        if (!this.ready) {
            return true;
        }
        if (this.bufferIndex === 0) {
            // Slot encoding: 1 = fill half 0, 2 = fill half 1. 0 = idle (futex_wait target).
            Atomics.store(this.syncView, 0, (this.bufferFlag ^ 1) + 1);
            Atomics.notify(this.syncView, 0, 1);
        }
        const bufferSliceEnd = this.bufferSize / output[0].length;
        const sliceOffset = output[0].length * this.bufferIndex + this.halfFloats * this.bufferFlag;
        for (let channel = 0; channel < output.length; ++channel) {
            const outputChannel = output[channel];
            const indexOffset = this.bufferSize * channel + sliceOffset;
            outputChannel.set(this.outputView.subarray(indexOffset, indexOffset + outputChannel.length));
        }
        this.bufferIndex++;
        if (this.bufferIndex === bufferSliceEnd) {
            this.bufferIndex = 0;
            this.bufferFlag ^= 1;
        }
        return true;
    }
}
registerProcessor('audio-processor', AudioProcessor);
