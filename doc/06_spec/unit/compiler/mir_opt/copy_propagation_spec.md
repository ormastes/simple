# CopyPropagation Specification

> Validates the CopyPropagation pass which promotes copy-to-move when the source register has no subsequent uses, and propagates through chains of copies back to the original source.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# CopyPropagation Specification

Validates the CopyPropagation pass which promotes copy-to-move when the source register has no subsequent uses, and propagates through chains of copies back to the original source.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #web-server-optimizer-complete |
| Category | Compiler / MIR Optimization |
| Difficulty | 2/5 |
| Status | Draft |
| Source | `test/unit/compiler/mir_opt/copy_propagation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Validates the CopyPropagation pass which promotes copy-to-move when the
source register has no subsequent uses, and propagates through chains of
copies back to the original source.

## Behavior

- Source with no subsequent uses → copy promoted to move
- Source used after the copy → copy preserved
- Chain of copies resolved to original source
- Pass statistics count every promoted copy

## Scenarios

### CopyPropagation

### copy-to-move promotion

#### promotes copy to move when source has no subsequent uses

- promotes copy to move when source has no subsequent uses
   - Expected: should_promote is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("promotes copy to move when source has no subsequent uses")
# %src is defined at pos 0, copied at pos 5, never used after pos 5.
val src_uses = [0, 5]
val copy_pos = 5
val uses_after = use_count_after(src_uses, copy_pos)
val should_promote = can_promote_to_move(uses_after)
expect(should_promote).to_equal(true)
```

</details>

#### preserves copy when source is used after copy

- preserves copy when source is used after copy
   - Expected: should_promote is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves copy when source is used after copy")
# %src is used at pos 7, copied at pos 5 — use comes after copy.
val src_uses = [0, 5, 7]
val copy_pos = 5
val uses_after = use_count_after(src_uses, copy_pos)
val should_promote = can_promote_to_move(uses_after)
expect(should_promote).to_equal(false)
```

</details>

### chain propagation

#### handles chain of copies — propagates through to original source

- handles chain of copies — propagates through to original source
   - Expected: original equals `%a`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles chain of copies — propagates through to original source")
# %a → %b → %c → %d: original source is %a
val chain = ["%a", "%b", "%c", "%d"]
val original = resolve_copy_chain(chain)
expect(original).to_equal("%a")
```

</details>

#### returns sole element as source for length-1 chain

- returns sole element as source for length-1 chain
   - Expected: original equals `%x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns sole element as source for length-1 chain")
val chain = ["%x"]
val original = resolve_copy_chain(chain)
expect(original).to_equal("%x")
```

</details>

### pass statistics

#### counts promoted copies in pass statistics

- counts promoted copies in pass statistics
   - Expected: promoted equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts promoted copies in pass statistics")
# 4 copies: first 3 promotable, last one is not.
val copies = ["%a", "%b", "%c", "%d"]
val moveable = [true, true, true, false]
val promoted = simulate_copy_promotion(copies, moveable)
expect(promoted).to_equal(3)
expect(promoted).to_be_greater_than(0)
```

</details>

#### reports zero promoted copies when none qualify

- reports zero promoted copies when none qualify
   - Expected: promoted equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports zero promoted copies when none qualify")
val copies = ["%x", "%y"]
val moveable = [false, false]
val promoted = simulate_copy_promotion(copies, moveable)
expect(promoted).to_equal(0)
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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `21ab835703e3aabd524284cb8c92510106104faa53f8c32134d280d1337479a4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21ab835703e3aabd524284cb8c92510106104faa53f8c32134d280d1337479a4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21ab835703e3aabd524284cb8c92510106104faa53f8c32134d280d1337479a4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/compiler/mir_opt/copy_propagation_spec.spl
mirror: doc/06_spec/unit/compiler/mir_opt/copy_propagation_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/mir_opt/copy_propagation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/mir_opt/copy_propagation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/mir_opt/copy_propagation_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/compiler/mir_opt/copy_propagation_spec.spl:77:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'promotes copy to move when source has no subsequent uses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/copy_propagation_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves copy when source is used after copy' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/mir_opt/copy_propagation_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles chain of copies — propagates through to original source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
