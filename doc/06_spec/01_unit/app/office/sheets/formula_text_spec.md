# formula_text_spec

> Calc text functions spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# formula_text_spec

Calc text functions spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/sheets/formula_text_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Calc text functions spec.

CONCAT/UPPER/LOWER/TRIM/LEN/LEFT/RIGHT/MID/EXACT over cell refs and string
literals. Text cells keep their text (no numeric coercion); MID is 1-based;
out-of-range counts clamp.

## Scenarios

### Calc text functions

#### CONCAT joins refs and string literals

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- CONCAT joins refs and string literals
   - Expected: _eval("=CONCAT(A1, \" \", A2)") equals `hello World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("CONCAT joins refs and string literals")
expect(_eval("=CONCAT(A1, \" \", A2)")).to_equal("hello World")
```

</details>

#### UPPER/LOWER/TRIM transform case and whitespace

- UPPER/LOWER/TRIM transform case and whitespace
   - Expected: _eval("=UPPER(A1)") equals `HELLO`
   - Expected: _eval("=LOWER(A2)") equals `world`
   - Expected: _eval("=TRIM(\"  x  \")") equals `x`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("UPPER/LOWER/TRIM transform case and whitespace")
expect(_eval("=UPPER(A1)")).to_equal("HELLO")
expect(_eval("=LOWER(A2)")).to_equal("world")
expect(_eval("=TRIM(\"  x  \")")).to_equal("x")
```

</details>

#### LEN counts characters of a text cell

- LEN counts characters of a text cell
   - Expected: _eval("=LEN(A1)") equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LEN counts characters of a text cell")
expect(_eval("=LEN(A1)")).to_equal("5")
```

</details>

#### LEFT/RIGHT/MID slice with 1-based MID and clamped counts

- LEFT/RIGHT/MID slice with 1-based MID and clamped counts
   - Expected: _eval("=LEFT(A2, 3)") equals `Wor`
   - Expected: _eval("=RIGHT(A2, 2)") equals `ld`
   - Expected: _eval("=MID(A2, 2, 3)") equals `orl`
   - Expected: _eval("=LEFT(A2, 99)") equals `World`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("LEFT/RIGHT/MID slice with 1-based MID and clamped counts")
expect(_eval("=LEFT(A2, 3)")).to_equal("Wor")
expect(_eval("=RIGHT(A2, 2)")).to_equal("ld")
expect(_eval("=MID(A2, 2, 3)")).to_equal("orl")
expect(_eval("=LEFT(A2, 99)")).to_equal("World")
```

</details>

#### EXACT compares case-sensitively

- EXACT compares case-sensitively
   - Expected: _eval("=EXACT(A1, \"hello\")") equals `TRUE`
   - Expected: _eval("=EXACT(A1, \"Hello\")") equals `FALSE`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("EXACT compares case-sensitively")
expect(_eval("=EXACT(A1, \"hello\")")).to_equal("TRUE")
expect(_eval("=EXACT(A1, \"Hello\")")).to_equal("FALSE")
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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d6b3b59a989b60f1e798f2ae581616e1090240cc4e98d7e34d6794ce73b6774`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d6b3b59a989b60f1e798f2ae581616e1090240cc4e98d7e34d6794ce73b6774`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d6b3b59a989b60f1e798f2ae581616e1090240cc4e98d7e34d6794ce73b6774`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/sheets/formula_text_spec.spl
mirror: doc/06_spec/01_unit/app/office/sheets/formula_text_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/sheets/formula_text_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/sheets/formula_text_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/sheets/formula_text_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'CONCAT joins refs and string literals' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'UPPER/LOWER/TRIM transform case and whitespace' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/sheets/formula_text_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'LEN counts characters of a text cell' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
