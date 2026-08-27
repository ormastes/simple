# CUDA Backend

> Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CUDA Backend

Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | Active |
| Source | `test/feature/usage/cuda_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Real CUDA backend checks through the Simple `std.nogc_async_mut.cuda` surface.
These tests run against the compiled runtime rather than stub helpers.

## Scenarios

### CUDA runtime surface

#### env_skip: CUDA not available

- env_skip: CUDA not available


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("env_skip: CUDA not available")
val reason = test_env_gate_skip("SIMPLE_CUDA_TEST")
expect(reason).to_contain("Skipped")
```

</details>

#### reports an internally consistent availability state

- reports an internally consistent availability state
   - Expected: count equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports an internally consistent availability state")
val available = cuda.cuda_available()
val count = cuda.cuda_device_count()

if available:
    expect(count).to_be_greater_than(0)
else:
    expect(count).to_equal(0)
```

</details>

#### returns a stable init result

- returns a stable init result
   - Expected: init_rc equals `cuda.CUDA_SUCCESS`
   - Expected: count equals `0`
   - Expected: init_rc == cuda.CUDA_SUCCESS or init_rc == cuda.CUDA_ERROR_NOT_INITIALIZED or init_rc == cuda.CUDA_ERROR_NO_DEVICE is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("returns a stable init result")
val init_rc = cuda.cuda_init()
val available = cuda.cuda_available()
val count = cuda.cuda_device_count()

if available:
    expect(init_rc).to_equal(cuda.CUDA_SUCCESS)
    expect(count).to_be_greater_than(0)
else:
    expect(count).to_equal(0)
    expect(init_rc == cuda.CUDA_SUCCESS or init_rc == cuda.CUDA_ERROR_NOT_INITIALIZED or init_rc == cuda.CUDA_ERROR_NO_DEVICE).to_equal(true)
```

</details>

#### reports device metadata when CUDA is available

- reports device metadata when CUDA is available
   - Expected: cuda.cuda_device_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reports device metadata when CUDA is available")
if cuda.cuda_available():
    val device = cuda.cuda_device_get(0)
    val name = cuda.cuda_device_name(device)
    val cc = cuda.cuda_device_compute_capability(device)
    expect(device).to_be_greater_than(-1)
    expect(name.len()).to_be_greater_than(0)
    expect(cc).to_be_greater_than(0)
else:
    expect(cuda.cuda_device_count()).to_equal(0)
```

</details>

#### maps known error codes to text

- maps known error codes to text
   - Expected: has_info is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("maps known error codes to text")
val msg = cuda.cuda_get_error_string(cuda.CUDA_ERROR_NOT_INITIALIZED)
# When CUDA is compiled in, the message contains "NOT_INITIALIZED".
# When CUDA support is disabled in the runtime, the stub returns a
# fixed "CUDA support disabled" string instead.
val has_info = msg.contains("NOT_INITIALIZED") or msg.contains("CUDA support disabled")
expect(has_info).to_equal(true)
```

</details>

#### rejects invalid PTX when CUDA is available

- rejects invalid PTX when CUDA is available
   - Expected: module equals `cuda.CUDA_ERROR_NOT_INITIALIZED`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("rejects invalid PTX when CUDA is available")
val module = cuda.cuda_module_load_data(invalid_ptx())
if cuda.cuda_available():
    expect(module).to_be_less_than(0)
else:
    expect(module).to_equal(cuda.CUDA_ERROR_NOT_INITIALIZED)
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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bb71cf83dd21371007bfd17f9de684fc3b394179d119a417f9dde72f8a093de5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bb71cf83dd21371007bfd17f9de684fc3b394179d119a417f9dde72f8a093de5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bb71cf83dd21371007bfd17f9de684fc3b394179d119a417f9dde72f8a093de5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/feature/usage/cuda_spec.spl
mirror: doc/06_spec/feature/usage/cuda_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/cuda_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/cuda_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/cuda_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/feature/usage/cuda_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'env_skip: CUDA not available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cuda_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports an internally consistent availability state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/cuda_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a stable init result' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
