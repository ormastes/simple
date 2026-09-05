# Sha1 Rfc3174 Jit Specification

> Tests covering SHA-1 digests and erased-list element reads on the run path.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha1 Rfc3174 Jit Specification

## Scenarios

### SHA-1 digests and erased-list element reads on the run path

#### matches the RFC 3174 vectors under the cranelift JIT

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the RFC 3174 vectors under the cranelift JIT
- Run the run-path probe under SIMPLE_EXECUTION_MODE=jit — the engine the wrong digest lived in
- The probe must actually have started, so an empty capture cannot read as a pass
- RFC 3174 §7.3: 'abc' hashes to a9993e36…, the empty string to da39a3ee…
- The sibling `[i64]`-typed implementation must agree with the same published vectors
- The aggregate verdict line is the authoritative result


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches the RFC 3174 vectors under the cranelift JIT")
step("Run the run-path probe under SIMPLE_EXECUTION_MODE=jit — the engine the wrong digest lived in")
val jit = run_probe_in_mode("jit")

step("The probe must actually have started, so an empty capture cannot read as a pass")
expect(jit).to_contain("SHA1 RFC 3174 PROBE START")

step("RFC 3174 §7.3: 'abc' hashes to a9993e36…, the empty string to da39a3ee…")
expect(jit).to_contain("PASS common_sha1_abc")
expect(jit).to_contain("PASS common_sha1_empty")
expect(jit).to_contain("PASS common_sha1_two_block")
expect(jit).to_contain("PASS common_sha1_a")

step("The sibling `[i64]`-typed implementation must agree with the same published vectors")
expect(jit).to_contain("PASS crypto_sha1_abc")
expect(jit).to_contain("PASS crypto_sha1_empty")

step("The aggregate verdict line is the authoritative result")
expect(jit).to_contain("SHA1 RFC 3174 PROBE: ALL PASS")
```

</details>

#### reads elements of an erased `list` return at every consumer form

- reads elements of an erased `list` return at every consumer form
- Run the probe under the JIT
- A function declared `-> list` returns Array<Any>; each consumer of an element must unbox it
- `.len()` was always correct — it is the control that proves the array itself was never damaged


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("reads elements of an erased `list` return at every consumer form")
step("Run the probe under the JIT")
val jit = run_probe_in_mode("jit")

step("A function declared `-> list` returns Array<Any>; each consumer of an element must unbox it")
expect(jit).to_contain("PASS list_elem_typed_let")
expect(jit).to_contain("PASS list_elem_call_arg")
expect(jit).to_contain("PASS list_elem_method_get")
expect(jit).to_contain("PASS list_elem_assign")
expect(jit).to_contain("PASS list_elem_interpolated")

step("`.len()` was always correct — it is the control that proves the array itself was never damaged")
expect(jit).to_contain("PASS list_len")
```

</details>

#### gives the interpreter the identical published answers

- gives the interpreter the identical published answers
- The interpreter was the correct arm throughout this bug, so a red here means the probe is broken rather than the engine


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("gives the interpreter the identical published answers")
step("The interpreter was the correct arm throughout this bug, so a red here means the probe is broken rather than the engine")
val interp = run_probe_in_mode("interpreter")
expect(interp).to_contain("SHA1 RFC 3174 PROBE: ALL PASS")
```

</details>

#### shows no tag-confusion signature under either engine

- shows no tag-confusion signature under either engine
- Collect both engines' output
- A raw word re-read through the tag decoder renders as nil or as a leaked tagged word
   - Expected: jit does not contain `nil`
   - Expected: jit does not contain `<value:0x`
- No check may have failed under either engine
   - Expected: jit does not contain `FAIL `
   - Expected: interp does not contain `FAIL `


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("shows no tag-confusion signature under either engine")
step("Collect both engines' output")
val jit = run_probe_in_mode("jit")
val interp = run_probe_in_mode("interpreter")

step("A raw word re-read through the tag decoder renders as nil or as a leaked tagged word")
expect(jit.contains("nil")).to_equal(false)
expect(jit.contains("<value:0x")).to_equal(false)

step("No check may have failed under either engine")
expect(jit.contains("FAIL ")).to_equal(false)
expect(interp.contains("FAIL ")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-1 digests and erased-list element reads on the run path.
- SHA-1 digests and erased-list element reads on the run path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dc431a4d45c5ef86fb226223cf817512ddad94d64820b23932aac652e0897274`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dc431a4d45c5ef86fb226223cf817512ddad94d64820b23932aac652e0897274`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dc431a4d45c5ef86fb226223cf817512ddad94d64820b23932aac652e0897274`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.spl
mirror: doc/06_spec/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the RFC 3174 vectors under the cranelift JIT' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads elements of an erased `list` return at every consumer form' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/codegen/sha1_rfc3174_jit_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'gives the interpreter the identical published answers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
