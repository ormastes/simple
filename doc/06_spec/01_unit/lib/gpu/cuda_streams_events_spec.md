# CUDA streams, events and async copies (plan E2)

> Device-free half: every stream/event/async extern that std.cuda declares must

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA streams, events and async copies (plan E2)

Device-free half: every stream/event/async extern that std.cuda declares must

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/cuda_streams_events_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Device-free half: every stream/event/async extern that std.cuda declares must
have a same-arity definition in the Rust runtime owner, so a declaration can
never silently return nil again (the 2026-08-25 io/cuda_sffi.spl defect class).
The runtime root defaults to the repo copy; SIMPLE_CUDA_RUNTIME_SRC overrides
it so the spec can be pointed at a private build tree before the seed lands.

Hardware half (SIMPLE_CUDA_TEST=1): two real streams each async-upload a buffer
and run a kernel via cuda_launch_on, events bracket the work, elapsed_ms is
non-negative, results are correct, everything is destroyed.

Plan: doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md row E2.

## Scenarios

### std.cuda stream/event externs match the runtime ABI (device-free)

#### declares every E2 extern with the runtime's arity

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares every E2 extern with the runtime's arity
   - Expected: mismatches equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declares every E2 extern with the runtime's arity")
val runtime_src = read_file(runtime_owner_path())
expect(runtime_src.len()).to_be_greater_than(0)
var mismatches: [text] = []
for name in E2_EXTERNS:
    val decl = declared_extern(CUDA_OWNER, name)
    if decl == "":
        mismatches.push(name + ": not declared in std.cuda")
        continue
    val want = runtime_param_count(runtime_src, name)
    val have = param_count(decl)
    if want < 0:
        mismatches.push(name + ": not defined in runtime")
    elif want != have:
        mismatches.push("{name}: decl {have} params, runtime {want}")
expect(mismatches).to_equal([])
```

</details>

#### declares rt_cuda_launch_kernel_ex identically in std.cuda and std.io

- declares rt_cuda_launch_kernel_ex identically in std.cuda and std.io
   - Expected: param_count(a) equals `11`
   - Expected: param_count(b) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("declares rt_cuda_launch_kernel_ex identically in std.cuda and std.io")
val a = declared_extern(CUDA_OWNER, "rt_cuda_launch_kernel_ex")
val b = declared_extern(IO_OWNER, "rt_cuda_launch_kernel_ex")
expect(a).to_contain("shared_bytes: i64, stream: i64, args_ptr: i64) -> i64")
expect(param_count(a)).to_equal(11)
expect(param_count(b)).to_equal(11)
```

</details>

#### keeps handle 0 as the always-valid default stream

- keeps handle 0 as the always-valid default stream
   - Expected: s.handle equals `0`
   - Expected: s.is_valid equals `cuda_available()`
   - Expected: cuda_stream_destroy(s) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps handle 0 as the always-valid default stream")
val s = cuda_default_stream()
expect(s.handle).to_equal(0)
expect(s.is_valid).to_equal(cuda_available())
expect(cuda_stream_destroy(s)).to_equal(true)
```

</details>

### std.cuda streams and events on hardware

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### overlaps two async uploads + kernels on two streams, timed by events

- overlaps two async uploads + kernels on two streams, timed by events
   - Expected: cuda_available() is true
   - Expected: cuda_init() equals `0`
   - Expected: cuda_ctx_create(cuda_device_get(0)) > 0 is true
   - Expected: module.is_valid is true
   - Expected: kernel.is_valid is true
   - Expected: s1.is_valid is true
   - Expected: s2.is_valid is true
   - Expected: s1.handle != s2.handle is true
   - Expected: start.is_valid() is true
   - Expected: stop.is_valid() is true
   - Expected: d1 > 0 is true
   - Expected: d2 > 0 is true
   - Expected: start.record(s1) is true
   - Expected: cuda_memcpy_htod_async(d1, h1, n * 8, s1.handle) equals `0`
   - Expected: cuda_memcpy_htod_async(d2, h2, n * 8, s2.handle) equals `0`
   - Expected: cuda_launch_on(kernel, cfg, s1.handle, 0, [d1, n]) is true
   - Expected: cuda_launch_on(kernel, cfg, s2.handle, 0, [d2, n]) is true
   - Expected: cuda_memcpy_dtoh_async(out1, d1, n * 8, s1.handle) equals `0`
   - Expected: cuda_memcpy_dtoh_async(out2, d2, n * 8, s2.handle) equals `0`
   - Expected: stop.record(s1) is true
   - Expected: cuda_stream_sync(s1) is true
   - Expected: cuda_stream_sync(s2) is true
   - Expected: stop.synchronize() is true
   - Expected: ms >= 0.0 is true
   - Expected: mismatches equals `0`
   - Expected: cuda_mem_free(d1) equals `0`
   - Expected: cuda_mem_free(d2) equals `0`
   - Expected: start.destroy() is true
   - Expected: stop.destroy() is true
   - Expected: cuda_stream_destroy(s1) is true
   - Expected: cuda_stream_destroy(s2) is true
   - Expected: cuda_unload(module) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 73 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overlaps two async uploads + kernels on two streams, timed by events")
expect(cuda_available()).to_equal(true)
expect(cuda_init()).to_equal(0)
expect(cuda_ctx_create(cuda_device_get(0)) > 0).to_equal(true)
val n = 64
val module = cuda_compile(PTX)
expect(module.is_valid).to_equal(true)
val kernel = cuda_get_kernel(module, "square_idx")
expect(kernel.is_valid).to_equal(true)

val s1 = cuda_stream_create()
val s2 = cuda_stream_create()
expect(s1.is_valid).to_equal(true)
expect(s2.is_valid).to_equal(true)
expect(s1.handle != s2.handle).to_equal(true)

val start = cuda_event_create()
val stop = cuda_event_create()
expect(start.is_valid()).to_equal(true)
expect(stop.is_valid()).to_equal(true)

# Two device buffers, each pre-filled from a host block on its own stream
# (with a poison value the kernel must overwrite), then squared in place.
var seed1: [i64] = []
var seed2: [i64] = []
for i in 0..n:
    seed1.push(-1)
    seed2.push(-1)
val h1 = host_block(seed1)
val h2 = host_block(seed2)
val d1 = cuda_mem_alloc(n * 8)
val d2 = cuda_mem_alloc(n * 8)
expect(d1 > 0).to_equal(true)
expect(d2 > 0).to_equal(true)

expect(start.record(s1)).to_equal(true)
expect(cuda_memcpy_htod_async(d1, h1, n * 8, s1.handle)).to_equal(0)
expect(cuda_memcpy_htod_async(d2, h2, n * 8, s2.handle)).to_equal(0)
val cfg = cuda_launch_config_1d(2, 32)
expect(cuda_launch_on(kernel, cfg, s1.handle, 0, [d1, n])).to_equal(true)
expect(cuda_launch_on(kernel, cfg, s2.handle, 0, [d2, n])).to_equal(true)
val out1 = rt_alloc(n * 8)
val out2 = rt_alloc(n * 8)
expect(cuda_memcpy_dtoh_async(out1, d1, n * 8, s1.handle)).to_equal(0)
expect(cuda_memcpy_dtoh_async(out2, d2, n * 8, s2.handle)).to_equal(0)
expect(stop.record(s1)).to_equal(true)

expect(cuda_stream_sync(s1)).to_equal(true)
expect(cuda_stream_sync(s2)).to_equal(true)
expect(stop.synchronize()).to_equal(true)
val ms = start.elapsed_ms(stop)
expect(ms >= 0.0).to_equal(true)

var mismatches = 0
for i in 0..n:
    if rt_ptr_read_i64(out1, i * 8) != i * i:
        mismatches = mismatches + 1
    if rt_ptr_read_i64(out2, i * 8) != i * i:
        mismatches = mismatches + 1
expect(mismatches).to_equal(0)

rt_free(out1)
rt_free(out2)
rt_free(h1)
rt_free(h2)
expect(cuda_mem_free(d1)).to_equal(0)
expect(cuda_mem_free(d2)).to_equal(0)
expect(start.destroy()).to_equal(true)
expect(stop.destroy()).to_equal(true)
expect(cuda_stream_destroy(s1)).to_equal(true)
expect(cuda_stream_destroy(s2)).to_equal(true)
expect(cuda_unload(module)).to_equal(true)
```

</details>

#### creates a non-blocking stream and a launch on the default stream still works

- creates a non-blocking stream and a launch on the default stream still works
   - Expected: s.is_valid is true
   - Expected: cuda_stream_sync(s) is true
   - Expected: cuda_stream_destroy(s) is true
   - Expected: cuda_memset(d, 0, 8 * 8) equals `0`
   - Expected: cuda_launch_on(kernel, cuda_launch_config_1d(1, 8), 0, 0, [d, 8]) is true
   - Expected: cuda_stream_sync(cuda_default_stream()) is true
   - Expected: cuda_memcpy_dtoh_async(out, d, 8 * 8, 0) equals `0`
   - Expected: cuda_stream_sync(cuda_default_stream()) is true
   - Expected: rt_ptr_read_i64(out, 7 * 8) equals `49`
   - Expected: cuda_mem_free(d) equals `0`
   - Expected: cuda_unload(module) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates a non-blocking stream and a launch on the default stream still works")
val s = cuda_stream_create_flags(CUDA_STREAM_NON_BLOCKING)
expect(s.is_valid).to_equal(true)
expect(cuda_stream_sync(s)).to_equal(true)
expect(cuda_stream_destroy(s)).to_equal(true)
val module = cuda_compile(PTX)
val kernel = cuda_get_kernel(module, "square_idx")
val d = cuda_mem_alloc(8 * 8)
expect(cuda_memset(d, 0, 8 * 8)).to_equal(0)
expect(cuda_launch_on(kernel, cuda_launch_config_1d(1, 8), 0, 0, [d, 8])).to_equal(true)
expect(cuda_stream_sync(cuda_default_stream())).to_equal(true)
val out = rt_alloc(8 * 8)
expect(cuda_memcpy_dtoh_async(out, d, 8 * 8, 0)).to_equal(0)
expect(cuda_stream_sync(cuda_default_stream())).to_equal(true)
expect(rt_ptr_read_i64(out, 7 * 8)).to_equal(49)
rt_free(out)
expect(cuda_mem_free(d)).to_equal(0)
expect(cuda_unload(module)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b2ea34e6b0cdc3be258a9742d2fb02e85dd0705e0e3429032b1eaf95b36e3ab8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b2ea34e6b0cdc3be258a9742d2fb02e85dd0705e0e3429032b1eaf95b36e3ab8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b2ea34e6b0cdc3be258a9742d2fb02e85dd0705e0e3429032b1eaf95b36e3ab8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gpu/cuda_streams_events_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/cuda_streams_events_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/cuda_streams_events_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/cuda_streams_events_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/cuda_streams_events_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/cuda_streams_events_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares every E2 extern with the runtime's arity' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/cuda_streams_events_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares rt_cuda_launch_kernel_ex identically in std.cuda and std.io' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/cuda_streams_events_spec.spl:117:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps handle 0 as the always-valid default stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
