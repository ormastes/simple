# Bitfield Runtime Compatibility

> Tests that real bitfield syntax is accepted and parsed correctly in the feature test path. Validates a basic bitfield declaration with a u8 backing type, including ready, mode, and reserved fields.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bitfield Runtime Compatibility

Tests that real bitfield syntax is accepted and parsed correctly in the feature test path. Validates a basic bitfield declaration with a u8 backing type, including ready, mode, and reserved fields.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Language Features |
| Status | In Progress |
| Source | `test/03_system/feature/usage/bitfield_runtime_compat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests that real bitfield syntax is accepted and parsed correctly in the feature test path.
Validates a basic bitfield declaration with a u8 backing type, including ready, mode,
and reserved fields.

## Scenarios

### Bitfield Runtime Compatibility

#### accepts real bitfield syntax in feature test path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts real bitfield syntax in feature test path
   - Expected: flags.ready equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("accepts real bitfield syntax in feature test path")
var flags: CompatFlags = CompatFlags.new(0)
expect(flags.ready).to_equal(0)
```

</details>

#### round-trips field writes through Flags.new packed runtime values

- round-trips field writes through Flags.new packed runtime values
   - Expected: f.a equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("round-trips field writes through Flags.new packed runtime values")
var f: Flags = Flags.new(0)
f.a = 3
expect(f.a).to_equal(3)
```

</details>

#### preserves adjacent fields when writing one packed bitfield field

- preserves adjacent fields when writing one packed bitfield field
   - Expected: f.a equals `3`
   - Expected: f.b equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("preserves adjacent fields when writing one packed bitfield field")
var f: Flags = Flags.new(0)
f.a = 3
f.b = 5
expect(f.a).to_equal(3)
expect(f.b).to_equal(5)
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2dad1bfa5274c65168c443f156c2852fb76edd8ad981184a91eb030aaa5ddff8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2dad1bfa5274c65168c443f156c2852fb76edd8ad981184a91eb030aaa5ddff8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2dad1bfa5274c65168c443f156c2852fb76edd8ad981184a91eb030aaa5ddff8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/feature/usage/bitfield_runtime_compat_spec.spl
mirror: doc/06_spec/03_system/feature/usage/bitfield_runtime_compat_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/bitfield_runtime_compat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/bitfield_runtime_compat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/bitfield_runtime_compat_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/feature/usage/bitfield_runtime_compat_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts real bitfield syntax in feature test path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/bitfield_runtime_compat_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips field writes through Flags.new packed runtime values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/bitfield_runtime_compat_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves adjacent fields when writing one packed bitfield field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
