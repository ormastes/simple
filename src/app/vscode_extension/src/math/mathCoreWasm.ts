import * as vscode from 'vscode';

const MATH_CORE_WASM_PATH = 'wasm/math-core.wasm';
type WasmBinary = ArrayBuffer | Uint8Array;

interface WasmMathCoreExports {
    memory?: WebAssembly.Memory;
    render_math_core_json?: (ptr: number, len: number, outLenPtr?: number) => number;
    render_math_json?: (ptr: number, len: number, outLenPtr?: number) => number;
    malloc?: (size: number) => number;
    alloc?: (size: number) => number;
    rt_alloc?: (size: number) => number;
    free?: (ptr: number) => void;
    rt_free?: (ptr: number, size: number) => void;
}

export interface MathCoreRenderResult {
    latex?: string;
    pretty?: string;
    text?: string;
    debug?: string;
    svg?: string;
    html?: string;
}

type BridgeStatus = 'uninitialized' | 'ready' | 'unavailable';
type WasmRenderFunction = NonNullable<WasmMathCoreExports['render_math_core_json']>;

type WasmFreeFunction =
    | { kind: 'legacy'; free: (ptr: number) => void }
    | { kind: 'sized'; free: (ptr: number, size: number) => void };

export class MathCoreWasmBridge {
    private status: BridgeStatus = 'uninitialized';
    private exports: WasmMathCoreExports | undefined;
    private renderFunction: WasmRenderFunction | undefined;
    private allocFunction: ((size: number) => number) | undefined;
    private freeFunction: WasmFreeFunction | undefined;
    private unavailableReason: string | undefined;

    public async initialize(extensionUri: vscode.Uri): Promise<void> {
        if (this.status !== 'uninitialized') {
            return;
        }

        const wasmUri = vscode.Uri.joinPath(extensionUri, MATH_CORE_WASM_PATH);

        let wasmBytes: Uint8Array;
        try {
            wasmBytes = await vscode.workspace.fs.readFile(wasmUri);
        } catch {
            this.markUnavailable(`Math core WASM not found at ${wasmUri.toString()}`);
            return;
        }

        if (this.isSmfArtifact(wasmBytes)) {
            this.markUnavailable(
                'Math core artifact is an SMF container, not a raw WebAssembly module. ' +
                'The current compiler path fell back to SMF output for this entrypoint, ' +
                'so the extension cannot instantiate it as standalone WASM yet.'
            );
            return;
        }

        try {
            const webAssemblyModuleApi = WebAssembly as unknown as {
                compile: (bytes: WasmBinary) => Promise<unknown>;
                Module: {
                    imports: (module: unknown) => Array<{ module: string; name: string; kind: string }>;
                    exports: (module: unknown) => Array<{ name: string; kind: string }>;
                };
            };
            const compiledModule = await webAssemblyModuleApi.compile(wasmBytes as WasmBinary);
            const moduleImports = webAssemblyModuleApi.Module.imports(compiledModule);
            if (moduleImports.length > 0) {
                const importList = moduleImports
                    .map((entry) => `${entry.module}.${entry.name}`)
                    .join(', ');
                this.markUnavailable(
                    'Math core WASM requires unresolved runtime imports (' +
                    `${importList}). Standalone math-core loading is not wired for env-backed runtime symbols yet.`
                );
                return;
            }

            const webAssemblyApi = WebAssembly as unknown as {
                instantiate: (
                    bytes: WasmBinary,
                    imports: Record<string, Record<string, unknown>>
                ) => Promise<{ instance: { exports: Record<string, unknown> } }>;
            };
            const result = await webAssemblyApi.instantiate(wasmBytes as WasmBinary, {});
            const exports = result.instance.exports as WasmMathCoreExports;
            const renderFn = this.resolveRenderFunction(exports);
            const allocFn = this.resolveAllocFunction(exports);

            if (!exports.memory || !renderFn || !allocFn) {
                const exportList = webAssemblyModuleApi.Module.exports(compiledModule)
                    .map((entry) => entry.name)
                    .join(', ');
                this.markUnavailable(
                    'Math core WASM artifact is present but does not expose the expected ABI ' +
                    '(memory + render_math_core_json/render_math_json + malloc/alloc/rt_alloc). ' +
                    `Exports found: ${exportList || 'none'}.`
                );
                return;
            }

            this.exports = exports;
            this.renderFunction = renderFn;
            this.allocFunction = allocFn;
            this.freeFunction = this.resolveFreeFunction(exports);
            this.status = 'ready';
        } catch (error: unknown) {
            const message = error instanceof Error ? error.message : String(error);
            this.markUnavailable(`Failed to instantiate math core WASM: ${message}`);
        }
    }

    public isReady(): boolean {
        return this.status === 'ready';
    }

    public getUnavailableReason(): string | undefined {
        return this.unavailableReason;
    }

    public async render(source: string): Promise<MathCoreRenderResult | undefined> {
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

        let outLenPtr: number | undefined;
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
            } else {
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

            return JSON.parse(json) as MathCoreRenderResult;
        } catch {
            return undefined;
        } finally {
            this.freeBuffer(resultPtr, resultLen);
            if (outLenPtr) {
                this.freeBuffer(outLenPtr, 8);
            }
            this.freeBuffer(inputPtr, bytes.length);
        }
    }

    private markUnavailable(reason: string): void {
        this.status = 'unavailable';
        this.unavailableReason = reason;
    }

    private resolveRenderFunction(exports: WasmMathCoreExports) {
        return exports.render_math_core_json ?? exports.render_math_json;
    }

    private resolveAllocFunction(exports: WasmMathCoreExports) {
        return exports.malloc ?? exports.alloc ?? exports.rt_alloc;
    }

    private resolveFreeFunction(exports: WasmMathCoreExports) {
        if (exports.free) {
            return { kind: 'legacy', free: exports.free } as const;
        }
        if (exports.rt_free) {
            return { kind: 'sized', free: exports.rt_free } as const;
        }
        return undefined;
    }

    private usesSizedOutput(renderFunction: WasmRenderFunction): boolean {
        return renderFunction.length >= 3;
    }

    private isSmfArtifact(bytes: Uint8Array): boolean {
        return bytes.length >= 4
            && bytes[0] === 0x53
            && bytes[1] === 0x4d
            && bytes[2] === 0x46
            && bytes[3] === 0x00;
    }

    private freeBuffer(ptr: number, size: number): void {
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

    private readLength(ptr: number, memory: WebAssembly.Memory): number {
        const view = new DataView(memory.buffer, ptr, 8);
        const low = view.getUint32(0, true);
        const high = view.getUint32(4, true);
        return high === 0 ? low : Number((BigInt(high) << 32n) | BigInt(low));
    }

    private readFixedLengthString(ptr: number, len: number, memory: WebAssembly.Memory): string {
        const view = new Uint8Array(memory.buffer, ptr, len);
        return new TextDecoder().decode(view);
    }

    private readNullTerminatedString(ptr: number, memory: WebAssembly.Memory): string {
        const view = new Uint8Array(memory.buffer);
        let end = ptr;
        while (end < view.length && view[end] !== 0) {
            end += 1;
        }
        return new TextDecoder().decode(view.slice(ptr, end));
    }
}
