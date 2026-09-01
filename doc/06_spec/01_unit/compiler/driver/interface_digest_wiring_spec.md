# Interface Digest Wiring Specification

> Contract of the textual interface digest (`interface_digest_of_source`): deterministic; sensitive to declaration-header (signature) edits; insensitive to body-only edits. Plus the three typed verdicts of `smf_manifest_entry_iface_verdict` (match / mismatch / absent) and the additive manifest round-trip (old rows parse with an absent digest).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Interface Digest Wiring Specification

Contract of the textual interface digest (`interface_digest_of_source`): deterministic; sensitive to declaration-header (signature) edits; insensitive to body-only edits. Plus the three typed verdicts of `smf_manifest_entry_iface_verdict` (match / mismatch / absent) and the additive manifest round-trip (old rows parse with an absent digest).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/driver/interface_digest_wiring_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Contract of the textual interface digest (`interface_digest_of_source`):
deterministic; sensitive to declaration-header (signature) edits; insensitive
to body-only edits. Plus the three typed verdicts of
`smf_manifest_entry_iface_verdict` (match / mismatch / absent) and the
additive manifest round-trip (old rows parse with an absent digest).

Honest limits of the textual v1 extractor are asserted, not hidden: struct
FIELD lines are not part of the digest (documented in action_key.spl).

## Scenarios

### interface_digest_of_source contract

#### is deterministic for the same source

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- is deterministic for the same source
   - Expected: interface_digest_of_source(SRC_A) equals `interface_digest_of_source(SRC_A)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is deterministic for the same source")
expect(interface_digest_of_source(SRC_A)).to_equal(interface_digest_of_source(SRC_A))
```

</details>

#### changes when a fn signature changes

- changes when a fn signature changes
   - Expected: interface_digest_of_source(SRC_A) == interface_digest_of_source(SRC_A_SIG_EDIT) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("changes when a fn signature changes")
expect(interface_digest_of_source(SRC_A) == interface_digest_of_source(SRC_A_SIG_EDIT)).to_equal(false)
```

</details>

#### is unchanged when only a fn body changes

- is unchanged when only a fn body changes
   - Expected: interface_digest_of_source(SRC_A) equals `interface_digest_of_source(SRC_A_BODY_EDIT)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is unchanged when only a fn body changes")
expect(interface_digest_of_source(SRC_A)).to_equal(interface_digest_of_source(SRC_A_BODY_EDIT))
```

</details>

#### extracts only declaration headers as parts

- extracts only declaration headers as parts
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `fn add(a: i64, b: i64) -> i64:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("extracts only declaration headers as parts")
val parts = source_interface_parts(SRC_A)
expect(parts.len()).to_equal(2)
expect(parts[0]).to_equal("fn add(a: i64, b: i64) -> i64:")
```

</details>

#### matches interface_digest_of over the extracted parts

- matches interface_digest_of over the extracted parts
   - Expected: interface_digest_of_source(SRC_A) equals `interface_digest_of(source_interface_parts(SRC_A))`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("matches interface_digest_of over the extracted parts")
expect(interface_digest_of_source(SRC_A)).to_equal(interface_digest_of(source_interface_parts(SRC_A)))
```

</details>

### smf_manifest_entry_iface_verdict

#### returns match when recorded digest equals recomputed

- returns match when recorded digest equals recomputed
   - Expected: iface_digest_verdict_text(v) equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns match when recorded digest equals recomputed")
val v = smf_manifest_entry_iface_verdict(entry_with(interface_digest_of_source(SRC_A)), SRC_A)
expect(iface_digest_verdict_text(v)).to_equal("match")
```

</details>

#### returns mismatch when the interface changed since compile

- returns mismatch when the interface changed since compile
   - Expected: iface_digest_verdict_text(v) equals `mismatch`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns mismatch when the interface changed since compile")
val v = smf_manifest_entry_iface_verdict(entry_with(interface_digest_of_source(SRC_A)), SRC_A_SIG_EDIT)
expect(iface_digest_verdict_text(v)).to_equal("mismatch")
```

</details>

#### still matches when only a body changed (that is the point)

- still matches when only a body changed (that is the point)
   - Expected: iface_digest_verdict_text(v) equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("still matches when only a body changed (that is the point)")
val v = smf_manifest_entry_iface_verdict(entry_with(interface_digest_of_source(SRC_A)), SRC_A_BODY_EDIT)
expect(iface_digest_verdict_text(v)).to_equal("match")
```

</details>

#### returns absent for an old row with no recorded digest

- returns absent for an old row with no recorded digest
   - Expected: iface_digest_verdict_text(v) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns absent for an old row with no recorded digest")
val v = smf_manifest_entry_iface_verdict(entry_with(""), SRC_A)
expect(iface_digest_verdict_text(v)).to_equal("absent")
```

</details>

#### returns absent when the live source is unreadable (fail closed on evidence)

- returns absent when the live source is unreadable (fail closed on evidence)
   - Expected: iface_digest_verdict_text(v) equals `absent`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns absent when the live source is unreadable (fail closed on evidence)")
val v = smf_manifest_entry_iface_verdict(entry_with(interface_digest_of_source(SRC_A)), "")
expect(iface_digest_verdict_text(v)).to_equal("absent")
```

</details>

### manifest round-trip carries the digest additively

#### serializes and re-parses iface_digest

- serializes and re-parses iface_digest
   - Expected: e.iface_digest equals `d`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("serializes and re-parses iface_digest")
val d = interface_digest_of_source(SRC_A)
var m = smf_manifest_new()
m = smf_manifest_update(m, entry_with(d))
val m2 = smf_manifest_from_sdn(smf_manifest_to_sdn(m))
match smf_manifest_find(m2, "/tmp/x.spl"):
    case Some(e):
        expect(e.iface_digest).to_equal(d)
    case nil:
        expect(true).to_equal(false)
```

</details>

#### parses an old 11-column row with an absent digest (never breaks old readers)

- parses an old 11-column row with an absent digest (never breaks old readers)
   - Expected: e.iface_digest equals ``
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("parses an old 11-column row with an absent digest (never breaks old readers)")
val old_row = "entries |source_path, smf_path, source_hash, compiled_at, backend, opt_level, release, debug_info, gc_off, profile, allowed_families|\n    \"/tmp/y.spl\", \"/tmp/y.smf\", 5, 1, \"cranelift\", 0, 0, 1, 0, \"dev\", \"\""
val m = smf_manifest_from_sdn("smf_manifest:\n  version: 3\n  updated_at: 1\n\n" + old_row)
match smf_manifest_find(m, "/tmp/y.spl"):
    case Some(e):
        expect(e.iface_digest).to_equal("")
    case nil:
        expect(true).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `52c7193e76147aadae4f70dcd6bc5070e5204e4caad0678424918200392415da`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `52c7193e76147aadae4f70dcd6bc5070e5204e4caad0678424918200392415da`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `52c7193e76147aadae4f70dcd6bc5070e5204e4caad0678424918200392415da`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler/driver/interface_digest_wiring_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/interface_digest_wiring_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/interface_digest_wiring_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/interface_digest_wiring_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/interface_digest_wiring_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/driver/interface_digest_wiring_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is deterministic for the same source' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/interface_digest_wiring_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes when a fn signature changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/interface_digest_wiring_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is unchanged when only a fn body changes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
