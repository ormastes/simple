# std.io CUDA SFFI externs match the runtime ABI

> Reproduce for the 2026-08-25 io/cuda_sffi.spl defect: the file declared 17

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.io CUDA SFFI externs match the runtime ABI

Reproduce for the 2026-08-25 io/cuda_sffi.spl defect: the file declared 17

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/cuda_io_sffi_extern_abi_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

Reproduce for the 2026-08-25 io/cuda_sffi.spl defect: the file declared 17
rt_cuda_* externs that exist nowhere in the runtime (rt_cuda_stream_*,
rt_cuda_compile_ptx, rt_cuda_get_function, rt_cuda_synchronize, ...) and a
rt_cuda_launch_kernel with the wrong arity/first parameter, so every launch
through CudaFunc/CudaStream silently returned nil. The device-free cases pin
the declarations against src/compiler_rust/runtime/src/cuda_runtime.rs; the
hardware cases (SIMPLE_CUDA_TEST=1) run a real parameterised kernel.

## Scenarios

### std.io CUDA SFFI extern declarations

#### declares only rt_cuda_* externs the runtime defines

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val runtime_src = read_file(RUNTIME_OWNER)
val decls = declared_externs(IO_OWNER)
expect(decls.len()).to_be_greater_than(0)
var missing: [text] = []
for line in decls:
    val name = extern_name(line)
    if not runtime_defines(runtime_src, name):
        missing.push(name)
expect(missing).to_equal([])
```

</details>

#### declares rt_cuda_launch_kernel with the (module, func_name, dims, args_ptr) shape

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var launch = ""
for line in declared_externs(IO_OWNER):
    if extern_name(line) == "rt_cuda_launch_kernel":
        launch = line
expect(launch).to_contain("(module: i64, func_name: text,")
expect(launch).to_contain("args_ptr: i64) -> i64")
expect(launch.contains("shared_mem")).to_equal(false)
```

</details>

#### keeps the async facade export list resolvable against the owner

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val owner = read_file(IO_OWNER)
val facade = read_file("src/lib/nogc_async_mut/io/cuda_sffi.spl")
val start = facade.index_of("io.cuda_sffi.{")
expect(start >= 0).to_equal(true)
val body = facade.substring(start + 14, facade.len())
val names = body.split("}")[0].replace("\n", " ").split(",")
var unresolved: [text] = []
for raw in names:
    val name = raw.trim()
    if name == "":
        continue
    if not (owner.contains("fn " + name + "(") or owner.contains("struct " + name + ":")):
        unresolved.push(name)
expect(unresolved).to_equal([])
```

</details>

### std.io CUDA kernel launch on hardware

#### env_skip: CUDA not available

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### launches a parameterised kernel and reads the result back

<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(cuda_available()).to_equal(true)
expect(cuda_driver_init()).to_equal(true)
# The test-runner process has no current context until one is made
# explicitly (the run lane's default context is not established here).
expect(cuda_set_device(0)).to_equal(true)
val n = 100
val module = cuda_compile(PTX)
expect(module.is_valid).to_equal(true)
val kernel = cuda_get_kernel(module, "square_idx")
expect(kernel.is_valid).to_equal(true)
val out = cuda_alloc(n * 8)
expect(out.is_valid).to_equal(true)
expect(cuda_memset(out, 0)).to_equal(true)
expect(cuda_run_1d(kernel, n, 32, [out.ptr, n])).to_equal(true)
val bytes = cuda_copy_from_device(out, n * 8)
expect(bytes.len()).to_equal(n * 8)
var mismatches = 0
for i in 0..n:
    var v = 0
    for b in 0..8:
        v = v + ((bytes[i * 8 + b] as i64) << (8 * b))
    if v != i * i:
        mismatches = mismatches + 1
expect(mismatches).to_equal(0)
expect(cuda_free(out)).to_equal(true)
expect(cuda_unload(module)).to_equal(true)
```

</details>

#### round-trips host bytes through device memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val data = [7, 0, 255, 42, 1] as [u8]
val mem = cuda_alloc_from_host(data)
expect(mem.is_valid).to_equal(true)
expect(cuda_copy_from_device(mem, 5)).to_equal(data)
expect(cuda_free(mem)).to_equal(true)
```

</details>

#### exposes the default stream and can synchronise it

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stream = cuda_stream_create()
expect(stream.is_valid).to_equal(true)
expect(stream.handle).to_equal(0)
expect(cuda_stream_sync(stream)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
