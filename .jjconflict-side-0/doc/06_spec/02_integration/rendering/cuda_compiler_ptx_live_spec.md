# cuda_compiler_ptx_live_spec

> Live launch/readback of PTX emitted by the Simple CUDA compiler.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_compiler_ptx_live_spec

Live launch/readback of PTX emitted by the Simple CUDA compiler.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Live launch/readback of PTX emitted by the Simple CUDA compiler.

@tag: integration, rendering, cuda, hardware, strict

## Scenarios

### compiler-produced CUDA PTX live qualification

#### launches the compiled fill kernel and reads exact device values

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launches the compiled fill kernel and reads exact device values
   - Expected: hir_lowering.errors.len() equals `0`
   - Expected: mir_lowering.errors.len() equals `0`
   - Expected: compiled.is_ok() is true
   - Expected: init_status equals `CUDA_SUCCESS`
   - Expected: session.launch_kernel_args("fill", 1, 1, 1, 32, 1, 1, args) equals `CUDA_SUCCESS`
   - Expected: session.sync() equals `CUDA_SUCCESS`
   - Expected: cuda_memcpy_dtoh(host_output, output, bytes) equals `CUDA_SUCCESS`
   - Expected: rt_ptr_read_i32(host_output, index * 4) as i64 equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("launches the compiled fill kernel and reads exact device values")
val source = "@gpu(\"cuda\")\n" +
    "fn fill(mut output: [u32], n: u32) -> ():\n" +
    "    val i = gpu_global_id(0)\n" +
    "    if i < n:\n" +
    "        output[i] = 42u32\n"
val parsed = parse_full_frontend(source, "cuda_compiler_ptx_live.spl", "cuda_compiler_ptx_live", Logger(level: 0))
var hir_lowering = HirLowering.with_filename("cuda_compiler_ptx_live.spl")
val hir = hir_lowering.lower_module(parsed)
expect(hir_lowering.errors.len()).to_equal(0)
var mir_lowering = MirLowering.new(hir.symbols)
val mir = mir_lowering.lower_module(hir)
expect(mir_lowering.errors.len()).to_equal(0)
val compiled = CudaBackend.create((8, 6)).compile(mir)
expect(compiled.is_ok()).to_equal(true)

var session = CudaSession.create()
val init_status = session.init()
expect(init_status).to_equal(CUDA_SUCCESS)
if init_status == CUDA_SUCCESS:
    val ptx = compiled.unwrap().ptx
    expect(ptx).to_contain(".visible .entry fill")
    expect(session.load_module(ptx)).to_be_greater_than(0)
    val count: i64 = 8
    val bytes = count * 4
    val host_output = rt_alloc(bytes)
    val values = rt_alloc(16)
    val args = rt_alloc(16)
    val output = session.alloc(bytes)
    expect(host_output).to_be_greater_than(0)
    expect(values).to_be_greater_than(0)
    expect(args).to_be_greater_than(0)
    expect(output).to_be_greater_than(0)
    if host_output > 0 and values > 0 and args > 0 and output > 0:
        write_fill_args(values, args, output, count)
        expect(session.launch_kernel_args("fill", 1, 1, 1, 32, 1, 1, args)).to_equal(CUDA_SUCCESS)
        expect(session.sync()).to_equal(CUDA_SUCCESS)
        expect(cuda_memcpy_dtoh(host_output, output, bytes)).to_equal(CUDA_SUCCESS)
        var index: i64 = 0
        while index < count:
            expect(rt_ptr_read_i32(host_output, index * 4) as i64).to_equal(42)
            index = index + 1
    if output > 0:
        session.free(output)
    if host_output > 0:
        rt_free(host_output)
    if values > 0:
        rt_free(values)
    if args > 0:
        rt_free(args)
    session.shutdown()
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b59e49c299ff4feec29a79b86c16345a014417937668736f6acf25aa6e8a6b81`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b59e49c299ff4feec29a79b86c16345a014417937668736f6acf25aa6e8a6b81`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b59e49c299ff4feec29a79b86c16345a014417937668736f6acf25aa6e8a6b81`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl
mirror: doc/06_spec/02_integration/rendering/cuda_compiler_ptx_live_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/rendering/cuda_compiler_ptx_live_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/rendering/cuda_compiler_ptx_live_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/rendering/cuda_compiler_ptx_live_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches the compiled fill kernel and reads exact device values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
