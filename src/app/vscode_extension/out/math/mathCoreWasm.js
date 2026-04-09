"use strict";
var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));
var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});
var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();
Object.defineProperty(exports, "__esModule", { value: true });
exports.MathCoreWasmBridge = void 0;
const vscode = __importStar(require("vscode"));
const MATH_CORE_WASM_PATH = 'wasm/math-core.wasm';
class MathCoreWasmBridge {
    constructor() {
        this.status = 'uninitialized';
    }
    async initialize(extensionUri) {
        if (this.status !== 'uninitialized') {
            return;
        }
        const wasmUri = vscode.Uri.joinPath(extensionUri, MATH_CORE_WASM_PATH);
        let wasmBytes;
        try {
            wasmBytes = await vscode.workspace.fs.readFile(wasmUri);
        }
        catch {
            this.markUnavailable(`Math core WASM not found at ${wasmUri.toString()}`);
            return;
        }
        if (this.isSmfArtifact(wasmBytes)) {
            this.markUnavailable('Math core artifact is an SMF container, not a raw WebAssembly module. ' +
                'The current compiler path fell back to SMF output for this entrypoint, ' +
                'so the extension cannot instantiate it as standalone WASM yet.');
            return;
        }
        try {
            const webAssemblyModuleApi = WebAssembly;
            const compiledModule = await webAssemblyModuleApi.compile(wasmBytes);
            const moduleImports = webAssemblyModuleApi.Module.imports(compiledModule);
            if (moduleImports.length > 0) {
                const importList = moduleImports
                    .map((entry) => `${entry.module}.${entry.name}`)
                    .join(', ');
                this.markUnavailable('Math core WASM requires unresolved runtime imports (' +
                    `${importList}). Standalone math-core loading is not wired for env-backed runtime symbols yet.`);
                return;
            }
            const webAssemblyApi = WebAssembly;
            const result = await webAssemblyApi.instantiate(wasmBytes, {});
            const exports = result.instance.exports;
            const renderFn = this.resolveRenderFunction(exports);
            const allocFn = this.resolveAllocFunction(exports);
            if (!exports.memory || !renderFn || !allocFn) {
                const exportList = webAssemblyModuleApi.Module.exports(compiledModule)
                    .map((entry) => entry.name)
                    .join(', ');
                this.markUnavailable('Math core WASM artifact is present but does not expose the expected ABI ' +
                    '(memory + render_math_core_json/render_math_json + malloc/alloc/rt_alloc). ' +
                    `Exports found: ${exportList || 'none'}.`);
                return;
            }
            this.exports = exports;
            this.renderFunction = renderFn;
            this.allocFunction = allocFn;
            this.freeFunction = this.resolveFreeFunction(exports);
            this.status = 'ready';
        }
        catch (error) {
            const message = error instanceof Error ? error.message : String(error);
            this.markUnavailable(`Failed to instantiate math core WASM: ${message}`);
        }
    }
    isReady() {
        return this.status === 'ready';
    }
    getUnavailableReason() {
        return this.unavailableReason;
    }
    async render(source) {
        if (this.status !== 'ready' || !this.exports || !this.renderFunction || !this.allocFunction) {
            return undefined;
        }
        const wasmMemory = this.exports.memory;
        if (!wasmMemory) {
            return undefined;
        }
        const encoder = new TextEncoder();
        const bytes = encoder.encode(source);
        const inputPtr = this.allocFunction(bytes.length);
        if (!inputPtr) {
            return undefined;
        }
        let memory = new Uint8Array(wasmMemory.buffer);
        memory.set(bytes, inputPtr);
        let outLenPtr;
        let resultPtr = 0;
        let resultLen = 0;
        try {
            if (this.usesSizedOutput(this.renderFunction)) {
                outLenPtr = this.allocFunction(8);
                if (!outLenPtr) {
                    return undefined;
                }
                resultPtr = this.renderFunction(inputPtr, bytes.length, outLenPtr);
                if (!resultPtr) {
                    return undefined;
                }
                resultLen = this.readLength(outLenPtr, wasmMemory);
                if (resultLen <= 0) {
                    return undefined;
                }
                memory = new Uint8Array(wasmMemory.buffer);
            }
            else {
                resultPtr = this.renderFunction(inputPtr, bytes.length);
                if (!resultPtr) {
                    return undefined;
                }
            }
            if (!resultPtr) {
                return undefined;
            }
            const json = resultLen > 0
                ? this.readFixedLengthString(resultPtr, resultLen, wasmMemory)
                : this.readNullTerminatedString(resultPtr, wasmMemory);
            if (!json) {
                return undefined;
            }
            return JSON.parse(json);
        }
        catch {
            return undefined;
        }
        finally {
            this.freeBuffer(resultPtr, resultLen);
            if (outLenPtr) {
                this.freeBuffer(outLenPtr, 8);
            }
            this.freeBuffer(inputPtr, bytes.length);
        }
    }
    markUnavailable(reason) {
        this.status = 'unavailable';
        this.unavailableReason = reason;
    }
    resolveRenderFunction(exports) {
        return exports.render_math_core_json ?? exports.render_math_json;
    }
    resolveAllocFunction(exports) {
        return exports.malloc ?? exports.alloc ?? exports.rt_alloc;
    }
    resolveFreeFunction(exports) {
        if (exports.free) {
            return { kind: 'legacy', free: exports.free };
        }
        if (exports.rt_free) {
            return { kind: 'sized', free: exports.rt_free };
        }
        return undefined;
    }
    usesSizedOutput(renderFunction) {
        return renderFunction.length >= 3;
    }
    isSmfArtifact(bytes) {
        return bytes.length >= 4
            && bytes[0] === 0x53
            && bytes[1] === 0x4d
            && bytes[2] === 0x46
            && bytes[3] === 0x00;
    }
    freeBuffer(ptr, size) {
        if (!ptr || !this.freeFunction) {
            return;
        }
        if (this.freeFunction.kind === 'legacy') {
            this.freeFunction.free(ptr);
            return;
        }
        if (size > 0) {
            this.freeFunction.free(ptr, size);
        }
    }
    readLength(ptr, memory) {
        const view = new DataView(memory.buffer, ptr, 8);
        const low = view.getUint32(0, true);
        const high = view.getUint32(4, true);
        return high === 0 ? low : Number((BigInt(high) << 32n) | BigInt(low));
    }
    readFixedLengthString(ptr, len, memory) {
        const view = new Uint8Array(memory.buffer, ptr, len);
        return new TextDecoder().decode(view);
    }
    readNullTerminatedString(ptr, memory) {
        const view = new Uint8Array(memory.buffer);
        let end = ptr;
        while (end < view.length && view[end] !== 0) {
            end += 1;
        }
        return new TextDecoder().decode(view.slice(ptr, end));
    }
}
exports.MathCoreWasmBridge = MathCoreWasmBridge;
//# sourceMappingURL=mathCoreWasm.js.map