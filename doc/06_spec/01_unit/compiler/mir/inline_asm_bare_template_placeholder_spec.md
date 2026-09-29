# Inline Asm Bare Template Placeholder Specification

> Tests covering Bare asm templates carry no unbound placeholders.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Inline Asm Bare Template Placeholder Specification

## Scenarios

### Bare asm templates carry no unbound placeholders

#### reads every listed asm-bearing file (non-vacuity control)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads every listed asm-bearing file (non-vacuity control)


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads every listed asm-bearing file (non-vacuity control)")
# A renamed or deleted path would otherwise silently shrink the scan to
# nothing and report green.
for path in ASM_BEARING:
    val src = read_file_text(path)
    expect(src.len() > 200).to_be(true)
    expect(src.contains("asm")).to_be(true)
```

</details>

#### detects the two known offenders (detector is not inert)

- detects the two known offenders (detector is not inert)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects the two known offenders (detector is not inert)")
# If this goes green-by-emptiness the detector has stopped working, and
# the "no new offenders" example below would be worthless.
expect(offends("src/os/kernel/arch/x86_64/timer.spl")).to_be(true)
expect(offends("src/os/kernel/arch/x86_64/topology.spl")).to_be(true)
```

</details>

#### clears bare asm that legitimately has no placeholders

- clears bare asm that legitimately has no placeholders


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears bare asm that legitimately has no placeholders")
# `cli` / `hlt` with no operands — correct, and must not be flagged.
expect(offends(
    "src/lib/nogc_async_mut_noalloc/baremetal/x86/serial_test_kernel.spl"
)).to_be(false)
```

</details>

#### clears the files already rerouted to SFFI volatile ops

- clears the files already rerouted to SFFI volatile ops


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clears the files already rerouted to SFFI volatile ops")
expect(offends(
    "src/lib/nogc_async_mut_noalloc/baremetal/semihost_transport.spl"
)).to_be(false)
expect(offends(
    "src/lib/nogc_async_mut_noalloc/baremetal/system_api.spl"
)).to_be(false)
```

</details>

#### admits no offender outside the shrink-only allowlist

- admits no offender outside the shrink-only allowlist


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits no offender outside the shrink-only allowlist")
for path in ASM_BEARING:
    if offends(path):
        expect(ALLOWED_OFFENDERS.contains(path)).to_be(true)
```

</details>

#### keeps the allowlist non-stale

- keeps the allowlist non-stale


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the allowlist non-stale")
# Every allowlisted path must still actually offend. Fix a file and this
# fails until its entry is deleted.
for path in ALLOWED_OFFENDERS:
    expect(offends(path)).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Bare asm templates carry no unbound placeholders.
- Bare asm templates carry no unbound placeholders

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `dfc1831016a972fff1f071b8fcf911bbec9acf6f62791634af551db7b9565d4d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `dfc1831016a972fff1f071b8fcf911bbec9acf6f62791634af551db7b9565d4d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `dfc1831016a972fff1f071b8fcf911bbec9acf6f62791634af551db7b9565d4d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.spl:89:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads every listed asm-bearing file (non-vacuity control)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the two known offenders (detector is not inert)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/inline_asm_bare_template_placeholder_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'clears bare asm that legitimately has no placeholders' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
