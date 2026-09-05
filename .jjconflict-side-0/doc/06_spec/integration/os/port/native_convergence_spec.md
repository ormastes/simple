# native_convergence_spec

> Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# native_convergence_spec

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/integration/os/port/native_convergence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Documents `verify_native_convergence(stage2, stage3) -> Result<(), text>`
    exported by `src/os/port/bootstrap_native_verify.spl`.

    Wave-3 byte-equality. Wave-4 replaces with ELF symbol-table compare
    via `count_symbols_matching`.

## Scenarios

### IF-09 native-convergence contract

#### identical stage2 and stage3 blobs converge

- identical stage2 and stage3 blobs converge


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("identical stage2 and stage3 blobs converge")
"""
IF-09 happy path: byte-identical inputs must return Ok(()).
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
write_text("/tmp/if09_stage2_same.bin", "stage2-blob")
val result = verify_native_convergence("/tmp/if09_stage2_same.bin", "/tmp/if09_stage2_same.bin")
assert_true(result.is_ok())
```

</details>

#### same-path arguments converge without reading the filesystem

- same-path arguments converge without reading the filesystem


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("same-path arguments converge without reading the filesystem")
"""
IF-09 short-circuit: identical path arguments must return Ok(())
before any filesystem access, so unreadable paths still converge
when they are literally the same file. Byte-divergence Err paths
need in-guest fs.read_bytes and stay with wave-4 QEMU coverage.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
val result = verify_native_convergence("/build/stage2/not-present.bin", "/build/stage2/not-present.bin")
assert_true(result.is_ok())
```

</details>

#### verifier is callable without side effects

- verifier is callable without side effects


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("verifier is callable without side effects")
"""
Pure: same inputs always produce same Result. Wave-4 tightens
to no fs reads and no time-based branches.
"""
val sr = simpleos_runtime()
if sr == "":
    return "skip: SIMPLEOS_RUNTIME not set"
write_text("/tmp/if09_stage2_pure.bin", "pure-blob")
val first = verify_native_convergence("/tmp/if09_stage2_pure.bin", "/tmp/if09_stage2_pure.bin")
val second = verify_native_convergence("/tmp/if09_stage2_pure.bin", "/tmp/if09_stage2_pure.bin")
assert_true(first.is_ok() and second.is_ok())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `74204ff918ee3a50636afffefc03b1735fa24387e9b816840b98b6a4ffdfe0f1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `74204ff918ee3a50636afffefc03b1735fa24387e9b816840b98b6a4ffdfe0f1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `74204ff918ee3a50636afffefc03b1735fa24387e9b816840b98b6a4ffdfe0f1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/integration/os/port/native_convergence_spec.spl
mirror: doc/06_spec/integration/os/port/native_convergence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/os/port/native_convergence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/os/port/native_convergence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/os/port/native_convergence_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'identical stage2 and stage3 blobs converge' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/native_convergence_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'same-path arguments converge without reading the filesystem' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/os/port/native_convergence_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'verifier is callable without side effects' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
