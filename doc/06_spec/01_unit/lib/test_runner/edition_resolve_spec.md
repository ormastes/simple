# edition_resolve_spec

> Purpose: Prove that resolve_edition() -- decision-free manifest slice (no semantics gated).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# edition_resolve_spec

Purpose: Prove that resolve_edition() -- decision-free manifest slice (no semantics gated).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/test_runner/edition_resolve_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that resolve_edition() -- decision-free manifest slice (no semantics gated).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### resolve_edition() -- decision-free manifest slice (no semantics gated)

#### defaults to \

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to \
   - Expected: resolve_edition() equals `2026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to \")
# This repo's cwd during `bin/simple test` has no simple.sdn at the
# root (verified by profile_aware_execution_spec.spl's own comment),
# so the [package] tier of resolution yields "" and resolve_edition
# falls through to the documented implicit current edition.
expect(resolve_edition()).to_equal("2026")
```

</details>

#### EDITION_DEFAULT is the one currently-defined edition value

- EDITION_DEFAULT is the one currently-defined edition value
- Verify: EDITION_DEFAULT is the one currently-defined edition value
   - Expected: EDITION_DEFAULT equals `2026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EDITION_DEFAULT is the one currently-defined edition value")
step("Verify: EDITION_DEFAULT is the one currently-defined edition value")
# @req: REQ-LIB-TEST-RUNNER-001
expect(EDITION_DEFAULT).to_equal("2026")
```

</details>

### resolve_edition_from_value() -- the pure resolution step

#### resolves the one defined value, \

- resolves the one defined value, \
   - Expected: resolve_edition_from_value("2026") equals `2026`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves the one defined value, \")
expect(resolve_edition_from_value("2026")).to_equal("2026")
```

</details>

#### resolves an empty/absent value to the default

- resolves an empty/absent value to the default
- Verify: resolves an empty/absent value to the default
   - Expected: resolve_edition_from_value("") equals `EDITION_DEFAULT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resolves an empty/absent value to the default")
step("Verify: resolves an empty/absent value to the default")
expect(resolve_edition_from_value("")).to_equal(EDITION_DEFAULT)
```

</details>

#### falls back to the default for an unknown value, warning exactly once

- falls back to the default for an unknown value, warning exactly once
- Verify: falls back to the default for an unknown value, warning exactly once
   - Expected: before equals `0`
   - Expected: resolved equals `EDITION_DEFAULT`
   - Expected: after equals `1`
   - Expected: resolved_again equals `EDITION_DEFAULT`
   - Expected: edition_unknown_warn_count("not-a-real-edition-xyz") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to the default for an unknown value, warning exactly once")
step("Verify: falls back to the default for an unknown value, warning exactly once")
val before = edition_unknown_warn_count("not-a-real-edition-xyz")
expect(before).to_equal(0)  # oracle: 0 — named expected value from the requirement

val resolved = resolve_edition_from_value("not-a-real-edition-xyz")
expect(resolved).to_equal(EDITION_DEFAULT)

val after = edition_unknown_warn_count("not-a-real-edition-xyz")
expect(after).to_equal(1)  # oracle: 1 — named expected value from the requirement

# Calling again with the same bad value must not warn twice --
# edition_unknown_warn_count stays at 1 (mirrors the profile
# precedent's warn-once contract).
val resolved_again = resolve_edition_from_value("not-a-real-edition-xyz")
expect(resolved_again).to_equal(EDITION_DEFAULT)
expect(edition_unknown_warn_count("not-a-real-edition-xyz")).to_equal(1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-TEST-RUNNER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `07e36f42977b39e5669bdd45a09aebff7416ce67f447e2052fd6ad32bccacaeb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `07e36f42977b39e5669bdd45a09aebff7416ce67f447e2052fd6ad32bccacaeb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `07e36f42977b39e5669bdd45a09aebff7416ce67f447e2052fd6ad32bccacaeb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/test_runner/edition_resolve_spec.spl
mirror: doc/06_spec/01_unit/lib/test_runner/edition_resolve_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/test_runner/edition_resolve_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/test_runner/edition_resolve_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/test_runner/edition_resolve_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/test_runner/edition_resolve_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/edition_resolve_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'EDITION_DEFAULT is the one currently-defined edition value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/test_runner/edition_resolve_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'resolves the one defined value, \' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
