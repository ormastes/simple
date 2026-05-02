import * as vscode from 'vscode';

const MATH_CORE_WASM_PATH = 'wasm/math-core.wasm';
const NIL_VALUE = 3;
const SUPPORTED_RUNTIME_IMPORTS = new Set([
    'env.rt_alloc',
    'env.rt_string_new',
    'env.rt_string_data',
    'env.rt_string_len',
    'env.rt_mem_write_i64',
    'env.rt_native_eq',
    'env.rt_native_neq',
    'env.rt_array_new',
    'env.rt_array_len',
    'env.rt_array_push',
    'env.rt_array_clear',
    'env.rt_index_get',
    'env.rt_index_set',
    'env.rt_len',
    'env.rt_string_concat',
    'env.rt_string_join',
    'env.rt_function_not_found',
    'env.rt_interp_call',
]);

interface WasmMathCoreExports {
    memory?: WebAssembly.Memory;
    __heap_base?: { value: number };
    render_math_core_json?: (ptr: number, len: number, outLenPtr?: number) => number;
    render_math_json?: (ptr: number, len: number, outLenPtr?: number) => number;
    malloc?: (size: number) => number;
    alloc?: (size: number) => number;
    rt_alloc?: (size: number) => number;
    free?: (ptr: number) => void;
    rt_free?: (ptr: number, size: number) => void;
    [key: string]: unknown;
}

interface SimpleRuntimeHandle {
    kind: 'string' | 'array';
    value: string | number[];
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

class SimpleMathRuntimeHost {
    private readonly textEncoder = new TextEncoder();
    private memory: WebAssembly.Memory | undefined;
    private exports: WasmMathCoreExports | undefined;
    private heapPtr = 0;
    private nextHandle = 1;
    private readonly handles = new Map<number, SimpleRuntimeHandle>();

    public bind(exports: WasmMathCoreExports): void {
        this.exports = exports;
        this.memory = exports.memory;
        if (!this.memory) {
            return;
        }
        const heapBase = exports.__heap_base?.value;
        const base = typeof heapBase === 'number' ? heapBase : this.memory.buffer.byteLength;
        this.heapPtr = Math.max(base, this.memory.buffer.byteLength);
    }

    public imports(): Record<string, (...args: number[]) => number | void> {
        return {
            rt_alloc: (size) => this.alloc(size),
            rt_string_new: (ptr, len) => this.newString(this.readUtf8(ptr, len)),
            rt_string_data: (value) => {
                const stringHandle = this.getStringHandle(value);
                if (!stringHandle) {
                    return 0;
                }
                const encoded = this.textEncoder.encode(stringHandle.value);
                const ptr = this.alloc(encoded.length);
                this.memoryBytes().set(encoded, ptr);
                return ptr;
            },
            rt_string_len: (value) => {
                const stringHandle = this.getStringHandle(value);
                if (stringHandle) {
                    return this.textEncoder.encode(stringHandle.value).length;
                }
                return this.isNil(value) ? 0 : -1;
            },
            rt_mem_write_i64: (ptr, value) => {
                this.memoryView().setBigInt64(ptr, BigInt(value), true);
            },
            rt_native_eq: (a, b) => this.nativeEq(a, b),
            rt_native_neq: (a, b) => this.nativeEq(a, b) ? 0 : 1,
            rt_array_new: () => this.newArray(),
            rt_array_len: (arr) => {
                const arrayHandle = this.getArrayHandle(arr);
                return arrayHandle ? arrayHandle.value.length : -1;
            },
            rt_array_push: (arr, value) => {
                const arrayHandle = this.getArrayHandle(arr);
                if (!arrayHandle) {
                    return 0;
                }
                arrayHandle.value.push(value);
                return 1;
            },
            rt_array_clear: (arr) => {
                const arrayHandle = this.getArrayHandle(arr);
                if (!arrayHandle) {
                    return 0;
                }
                arrayHandle.value.length = 0;
                return 1;
            },
            rt_index_get: (collection, index) => {
                const arrayHandle = this.getArrayHandle(collection);
                if (arrayHandle) {
                    const resolvedIndex = this.unboxMaybeInt(index);
                    return arrayHandle.value[resolvedIndex] ?? NIL_VALUE;
                }
                const stringHandle = this.getStringHandle(collection);
                if (!stringHandle) {
                    return NIL_VALUE;
                }
                const resolvedIndex = this.unboxMaybeInt(index);
                const chars = [...stringHandle.value];
                return resolvedIndex >= 0 && resolvedIndex < chars.length
                    ? this.newString(chars[resolvedIndex])
                    : NIL_VALUE;
            },
            rt_index_set: (collection, index, value) => {
                const arrayHandle = this.getArrayHandle(collection);
                const resolvedIndex = this.unboxMaybeInt(index);
                if (!arrayHandle || resolvedIndex < 0) {
                    return 0;
                }
                while (arrayHandle.value.length <= resolvedIndex) {
                    arrayHandle.value.push(NIL_VALUE);
                }
                arrayHandle.value[resolvedIndex] = value;
                return 1;
            },
            rt_len: (value) => {
                const handle = this.getHandle(value);
                if (!handle) {
                    return -1;
                }
                return handle.kind === 'array' ? handle.value.length : [...handle.value].length;
            },
            rt_string_concat: (a, b) => {
                const left = this.getStringValue(a);
                const right = this.getStringValue(b);
                return this.newString(left + right);
            },
            rt_string_join: (arr, sep) => {
                const arrayHandle = this.getArrayHandle(arr);
                if (!arrayHandle) {
                    return this.newString('');
                }
                const separator = this.getStringValue(sep);
                const joined = arrayHandle.value
                    .map((value) => {
                        const stringHandle = this.getStringHandle(value);
                        if (stringHandle) {
                            return stringHandle.value;
                        }
                        if (this.isNil(value)) {
                            return '';
                        }
                        return String(this.unboxMaybeInt(value));
                    })
                    .join(separator);
                return this.newString(joined);
            },
            rt_function_not_found: () => NIL_VALUE,
            rt_interp_call: (namePtr, nameLen, argc, argvPtr) => {
                const exports = this.exports;
                if (!exports) {
                    return NIL_VALUE;
                }
                const name = this.readUtf8(namePtr, nameLen);
                const target = exports[name];
                if (typeof target !== 'function') {
                    return NIL_VALUE;
                }
                const args: number[] = [];
                for (let i = 0; i < argc; i += 1) {
                    args.push(this.memoryView().getInt32(argvPtr + (i * 4), true));
                }
                const result = target(...args);
                return typeof result === 'number' ? result : NIL_VALUE;
            },
        };
    }

    private alloc(size: number): number {
        const memory = this.requireMemory();
        const needed = this.align8(size);
        let ptr = this.heapPtr;
        if (ptr === 0) {
            ptr = memory.buffer.byteLength;
        }
        while (ptr + needed > memory.buffer.byteLength) {
            memory.grow(1);
        }
        this.heapPtr = this.align8(ptr + needed);
        return ptr;
    }

    private align8(value: number): number {
        return (value + 7) & ~7;
    }

    private requireMemory(): WebAssembly.Memory {
        if (!this.memory) {
            throw new Error('Math core WASM memory is not initialized');
        }
        return this.memory;
    }

    private memoryBytes(): Uint8Array {
        return new Uint8Array(this.requireMemory().buffer);
    }

    private memoryView(): DataView {
        return new DataView(this.requireMemory().buffer);
    }

    private readUtf8(ptr: number, len: number): string {
        return new TextDecoder().decode(this.memoryBytes().subarray(ptr, ptr + len));
    }

    private newString(value: string): number {
        const id = this.nextHandle;
        this.nextHandle += 1;
        this.handles.set(id, { kind: 'string', value });
        return (id << 3) | 1;
    }

    private newArray(): number {
        const id = this.nextHandle;
        this.nextHandle += 1;
        this.handles.set(id, { kind: 'array', value: [] });
        return (id << 3) | 1;
    }

    private getHandle(value: number): SimpleRuntimeHandle | undefined {
        if (!this.isHeap(value)) {
            return undefined;
        }
        return this.handles.get(value >>> 3);
    }

    private getStringHandle(value: number): { kind: 'string'; value: string } | undefined {
        const handle = this.getHandle(value);
        return handle?.kind === 'string'
            ? (handle as { kind: 'string'; value: string })
            : undefined;
    }

    private getArrayHandle(value: number): { kind: 'array'; value: number[] } | undefined {
        const handle = this.getHandle(value);
        return handle?.kind === 'array'
            ? (handle as { kind: 'array'; value: number[] })
            : undefined;
    }

    private getStringValue(value: number): string {
        return this.getStringHandle(value)?.value ?? '';
    }

    private isHeap(value: number): boolean {
        return (value & 0b111) === 0b001;
    }

    private isNil(value: number): boolean {
        return value === 0 || value === NIL_VALUE;
    }

    private unboxMaybeInt(value: number): number {
        return (value & 0b111) === 0 ? (value >> 3) : value;
    }

    private nativeEq(a: number, b: number): number {
        if (a === b) {
            return 1;
        }
        const left = this.getStringHandle(a);
        const right = this.getStringHandle(b);
        if (left && right) {
            return left.value === right.value ? 1 : 0;
        }
        return 0;
    }
}

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
                'The current compiler path fell back to SMF output for this entrypoint.'
            );
            return;
        }

        const runtimeHost = new SimpleMathRuntimeHost();

        try {
            const webAssemblyApi = WebAssembly as unknown as {
                compile: (bytes: Uint8Array) => Promise<unknown>;
                instantiate: (
                    module: unknown,
                    imports: Record<string, Record<string, unknown>>
                ) => Promise<{ exports: Record<string, unknown> }>;
                Module: {
                    imports: (module: unknown) => Array<{ module: string; name: string; kind: string }>;
                    exports: (module: unknown) => Array<{ name: string; kind: string }>;
                };
            };
            const compiledModule = await webAssemblyApi.compile(wasmBytes);
            const moduleImports = webAssemblyApi.Module.imports(compiledModule);
            const unsupportedImports = moduleImports
                .map((entry) => `${entry.module}.${entry.name}`)
                .filter((entry) => !SUPPORTED_RUNTIME_IMPORTS.has(entry));

            if (unsupportedImports.length > 0) {
                this.markUnavailable(
                    'Math core WASM requires unsupported runtime imports: ' +
                    unsupportedImports.join(', ')
                );
                return;
            }

            const result = await webAssemblyApi.instantiate(compiledModule, {
                env: runtimeHost.imports(),
            });
            const exports = result.exports as WasmMathCoreExports;
            runtimeHost.bind(exports);

            const renderFn = this.resolveRenderFunction(exports);
            const allocFn = this.resolveAllocFunction(exports);

            if (!exports.memory || !renderFn || !allocFn) {
                const exportList = webAssemblyApi.Module.exports(compiledModule)
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
