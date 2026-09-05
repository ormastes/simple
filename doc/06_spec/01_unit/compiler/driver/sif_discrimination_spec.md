# SIF Body/Signature Discrimination and Fail-Closed Sabotage

> invalidates) or secretly source-hash-like (always invalidates) is worthless.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SIF Body/Signature Discrimination and Fail-Closed Sabotage

invalidates) or secretly source-hash-like (always invalidates) is worthless.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Active |
| Source | `test/01_unit/compiler/driver/sif_discrimination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

**Defect class:** an interface artifact that is secretly constant (never
invalidates) or secretly source-hash-like (always invalidates) is worthless.
This spec carries a POSITIVE CONTROL on both sides:
- a BODY-only edit leaves the SIF byte-identical (so it is not a source hash);
- a SIGNATURE edit changes both the SIF text and its iface-digest (so it is
  not a constant).
Plus sabotage cases: truncation, tampered part, tampered digest, wrong
version, unknown lines, non-canonical order, empty input — every one must
FAIL CLOSED (validate != "", accessors empty).

## Scenarios

### SIF body vs signature discrimination

#### body-only edit leaves the SIF byte-identical (positive control 1)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- body-only edit leaves the SIF byte-identical (positive control 1)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("body-only edit leaves the SIF byte-identical (positive control 1)")
val a = sif_of_source("m", "lang1", [], SRC_V1)
val b = sif_of_source("m", "lang1", [], SRC_BODY_EDIT)
assert_equal(sif_validate(a), "")
assert_equal(a, b)
assert_equal(sif_iface_digest(a), sif_iface_digest(b))
```

</details>

#### signature edit changes SIF text and digest (positive control 2)

- signature edit changes SIF text and digest (positive control 2)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("signature edit changes SIF text and digest (positive control 2)")
val a = sif_of_source("m", "lang1", [], SRC_V1)
val c = sif_of_source("m", "lang1", [], SRC_SIG_EDIT)
assert_false(a == c)
assert_false(sif_iface_digest(a) == sif_iface_digest(c))
```

</details>

### SIF fail-closed sabotage

#### rejects truncation (last line, half the file, lost newline)

- rejects truncation (last line, half the file, lost newline)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects truncation (last line, half the file, lost newline)")
val s = sif_of_source("m", "lang1", ["d=x"], SRC_V1)
val lines = s.split("\n")
# Drop the content-digest line entirely.
var no_digest = ""
var i = 0
while i < lines.len() - 2:
    no_digest = no_digest + lines[i] + "\n"
    i = i + 1
assert_fails_closed(no_digest)
# Cut mid-file.
assert_fails_closed(s.substring(0, s.len() / 2))
# Lose only the trailing newline.
assert_fails_closed(s.substring(0, s.len() - 1))
```

</details>

#### rejects a tampered part (content-digest and iface-digest mismatch)

- rejects a tampered part (content-digest and iface-digest mismatch)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a tampered part (content-digest and iface-digest mismatch)")
val s = sif_of_source("m", "lang1", [], SRC_V1)
val tampered = s.replace("part: fn add(a: i64, b: i64) -> i64:", "part: fn add(a: i64, b: i64) -> f64:")
assert_false(s == tampered)
assert_fails_closed(tampered)
```

</details>

#### rejects a wrong version line

- rejects a wrong version line


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a wrong version line")
val s = sif_of_source("m", "lang1", [], SRC_V1)
assert_fails_closed(s.replace("sif-version: 1", "sif-version: 2"))
```

</details>

#### rejects unknown lines and non-canonical section order

- rejects unknown lines and non-canonical section order


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects unknown lines and non-canonical section order")
val s = sif_of_source("m", "lang1", [], SRC_V1)
assert_fails_closed(s.replace("lang: lang1", "lang: lang1\nbogus: x"))
# Non-canonical: unsorted parts must not validate even if digests are
# recomputed to match — build one manually.
val good = sif_serialize_parts("m", "lang1", [], ["a_part", "b_part"])
val swapped = good.replace("part: a_part\npart: b_part", "part: b_part\npart: a_part")
assert_false(good == swapped)
assert_fails_closed(swapped)
```

</details>

#### rejects empty and garbage input

- rejects empty and garbage input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects empty and garbage input")
assert_fails_closed("")
assert_fails_closed("garbage\n")
assert_fails_closed("sif-version: 1\n")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `4fbaabf1b31bb4dcce731d0b5372425b032a84e7c2717f65d54ae9b5ed9a72c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fbaabf1b31bb4dcce731d0b5372425b032a84e7c2717f65d54ae9b5ed9a72c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fbaabf1b31bb4dcce731d0b5372425b032a84e7c2717f65d54ae9b5ed9a72c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/sif_discrimination_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/sif_discrimination_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/sif_discrimination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/sif_discrimination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/sif_discrimination_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'body-only edit leaves the SIF byte-identical (positive control 1)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/sif_discrimination_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'signature edit changes SIF text and digest (positive control 2)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/sif_discrimination_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects truncation (last line, half the file, lost newline)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
