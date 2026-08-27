# Scv Incremental Parse Specification

> Tests covering scv true incremental parse session (SCV-IMPL-P-03).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Scv Incremental Parse Specification

## Scenarios

### scv true incremental parse session (SCV-IMPL-P-03)

#### TSInputEdit: exact bytes and row,col points for a mid-line replacement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- TSInputEdit: exact bytes and row,col points for a mid-line replacement


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("TSInputEdit: exact bytes and row,col points for a mid-line replacement")
val old_src = "alpha\nbeta\ngamma\n"
# replace "beta" (bytes 6..10) with "BETAX"
val new_src = "alpha\nBETAX\ngamma\n"
val rec = scv_input_edit_record(old_src, new_src, 6, 10, "BETAX")
expect(rec).to_contain("start_byte=6")
expect(rec).to_contain("old_end_byte=10")
expect(rec).to_contain("new_end_byte=11")
expect(rec).to_contain("start_point=1,0")
expect(rec).to_contain("old_end_point=1,4")
expect(rec).to_contain("new_end_point=1,5")
```

</details>

#### TSInputEdit: points cross newlines correctly

- TSInputEdit: points cross newlines correctly
   - Expected: r0 equals `0`
   - Expected: c0 equals `0`
   - Expected: r1 equals `1`
   - Expected: c1 equals `1`
   - Expected: r2 equals `2`
   - Expected: c2 equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("TSInputEdit: points cross newlines correctly")
val (r0, c0) = scv_point_at("ab\ncd\nef", 0)
expect(r0).to_equal(0)
expect(c0).to_equal(0)
val (r1, c1) = scv_point_at("ab\ncd\nef", 4)
expect(r1).to_equal(1)
expect(c1).to_equal(1)
val (r2, c2) = scv_point_at("ab\ncd\nef", 8)
expect(r2).to_equal(2)
expect(c2).to_equal(2)
# insertion of a newline moves the new_end point to the next row
val rec = scv_input_edit_record("ab", "a\nb", 1, 1, "\n")
expect(rec).to_contain("new_end_byte=2")
expect(rec).to_contain("new_end_point=1,0")
```

</details>

#### session open retains a parse tree and reports honest fallback mode

- session open retains a parse tree and reports honest fallback mode
   - Expected: scv_session_tree_root(s) == "" is false
   - Expected: scv_session_mode(s) equals `fallback-full-reparse`
   - Expected: scv_session_edit_count(s) equals `0`
   - Expected: scv_session_source(s) equals `one\ntwo\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("session open retains a parse tree and reports honest fallback mode")
val root = _fresh_root()
val s = scv_parser_session_open(root, "text", "fallback", "0", "none",
                                "one\ntwo\n")
expect(scv_session_tree_root(s) == "").to_equal(false)
expect(scv_session_mode(s)).to_equal("fallback-full-reparse")
expect(scv_session_edit_count(s)).to_equal(0)
expect(scv_session_source(s)).to_equal("one\ntwo\n")
```

</details>

#### apply_edit splices source, logs the exact TSInputEdit, reparses

- apply_edit splices source, logs the exact TSInputEdit, reparses
   - Expected: scv_session_source(s1) equals `one\n2\nthree\n`
   - Expected: scv_session_edit_count(s1) equals `1`
   - Expected: scv_session_tree_root(s1) == scv_session_tree_root(s0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("apply_edit splices source, logs the exact TSInputEdit, reparses")
val root = _fresh_root()
val s0 = scv_parser_session_open(root, "text", "fallback", "0", "none",
                                 "one\ntwo\nthree\n")
# replace "two" (bytes 4..7) with "2"
val s1 = scv_parser_session_apply_edit(root, s0, 4, 7, "2")
expect(scv_session_source(s1)).to_equal("one\n2\nthree\n")
expect(scv_session_edit_count(s1)).to_equal(1)
expect(scv_session_last_edit(s1)).to_contain("start_byte=4")
expect(scv_session_last_edit(s1)).to_contain("old_end_byte=7")
expect(scv_session_last_edit(s1)).to_contain("new_end_byte=5")
expect(scv_session_tree_root(s1) == scv_session_tree_root(s0)).to_equal(false)
```

</details>

#### out-of-bounds edits are refused, session unchanged

- out-of-bounds edits are refused, session unchanged
   - Expected: scv_parser_session_apply_edit(root, s0, -1, 2, "x") equals `s0`
   - Expected: scv_parser_session_apply_edit(root, s0, 2, 1, "x") equals `s0`
   - Expected: scv_parser_session_apply_edit(root, s0, 0, 99, "x") equals `s0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("out-of-bounds edits are refused, session unchanged")
val root = _fresh_root()
val s0 = scv_parser_session_open(root, "text", "fallback", "0", "none", "abc")
expect(scv_parser_session_apply_edit(root, s0, -1, 2, "x")).to_equal(s0)
expect(scv_parser_session_apply_edit(root, s0, 2, 1, "x")).to_equal(s0)
expect(scv_parser_session_apply_edit(root, s0, 0, 99, "x")).to_equal(s0)
```

</details>

#### differential equivalence: session tree == full reparse tree after every edit

- differential equivalence: session tree == full reparse tree after every edit
   - Expected: err equals ``
   - Expected: scv_session_tree_root(s) equals `full_root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("differential equivalence: session tree == full reparse tree after every edit")
val root = _fresh_root()
var s = scv_parser_session_open(root, "text", "fallback", "0", "none",
                                "aaa\nbbb\nccc\n")
# (start, old_end, replacement) sequence
val edits = [(4, 7, "BB"), (0, 3, "A"), (5, 5, "zz\n")]
var i = 0
while i < edits.len():
    val (st, oe, tx) = edits[i]
    s = scv_parser_session_apply_edit(root, s, st, oe, tx)
    val (full_root, err) = scv_wasm_parse(root, "text", "fallback", "0",
                                          "none", scv_session_source(s))
    expect(err).to_equal("")
    expect(scv_session_tree_root(s)).to_equal(full_root)
    i = i + 1
```

</details>

#### fuzzed edit sequence: session source tracks a reference splice model

- fuzzed edit sequence: session source tracks a reference splice model
   - Expected: scv_session_source(s) equals `reference`
   - Expected: scv_session_edit_count(s) equals `12`
   - Expected: scv_session_tree_root(s) equals `full_root`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("fuzzed edit sequence: session source tracks a reference splice model")
val root = _fresh_root()
var reference = "line0\nline1\nline2\nline3\n"
var s = scv_parser_session_open(root, "text", "fallback", "0", "none", reference)
# deterministic pseudo-random edit generator (LCG seed 42)
var seed: i64 = 42
var k = 0
while k < 12:
    seed = (seed * 1103515245 + 12345) % 2147483648
    val len = reference.len()
    val st = if len == 0: 0 else: seed % len
    seed = (seed * 1103515245 + 12345) % 2147483648
    val span = seed % 4
    val oe = if st + span > len: len else: st + span
    val tx = "x{k}\n"
    reference = reference.slice(0, st) + tx + reference.slice(oe, reference.len())
    s = scv_parser_session_apply_edit(root, s, st, oe, tx)
    expect(scv_session_source(s)).to_equal(reference)
    k = k + 1
expect(scv_session_edit_count(s)).to_equal(12)
# final tree agrees with a from-scratch parse of the reference text
val (full_root, _e) = scv_wasm_parse(root, "text", "fallback", "0",
                                     "none", reference)
expect(scv_session_tree_root(s)).to_equal(full_root)
```

</details>

#### changed_ranges names the edited bytes, not the whole file

- changed_ranges names the edited bytes, not the whole file
   - Expected: ranges == "" is false
   - Expected: ranges does not contain `0..3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("changed_ranges names the edited bytes, not the whole file")
val root = _fresh_root()
val s0 = scv_parser_session_open(root, "text", "fallback", "0", "none",
                                 "one\ntwo\nthree\n")
val s1 = scv_parser_session_apply_edit(root, s0, 4, 7, "2")
val ranges = scv_parser_session_changed_ranges(root, s1)
expect(ranges == "").to_equal(false)
expect(ranges).to_contain("4..5")
# unchanged first line's range is not reported
expect(ranges.contains("0..3")).to_equal(false)
```

</details>

#### checkpoint persists session state and is content-addressed

- checkpoint persists session state and is content-addressed
   - Expected: ck1 == "" is false
   - Expected: file_exists(scv_object_path(root, "session", ck1)) is true
   - Expected: scv_parser_session_checkpoint(root, s0) equals `ck1`
   - Expected: scv_parser_session_checkpoint(root, s1) == ck1 is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("checkpoint persists session state and is content-addressed")
val root = _fresh_root()
val s0 = scv_parser_session_open(root, "text", "fallback", "0", "none",
                                 "one\ntwo\n")
val ck1 = scv_parser_session_checkpoint(root, s0)
expect(ck1 == "").to_equal(false)
expect(file_exists(scv_object_path(root, "session", ck1))).to_equal(true)
# same state => same checkpoint id; different state => different id
expect(scv_parser_session_checkpoint(root, s0)).to_equal(ck1)
val s1 = scv_parser_session_apply_edit(root, s0, 0, 3, "ONE")
expect(scv_parser_session_checkpoint(root, s1) == ck1).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/integration/app/scv_incremental_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering scv true incremental parse session (SCV-IMPL-P-03).
- scv true incremental parse session (SCV-IMPL-P-03)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `5c35de636144011fc6cb11cce279afabe233e1f756856cdd77f848f10ad95b7c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5c35de636144011fc6cb11cce279afabe233e1f756856cdd77f848f10ad95b7c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5c35de636144011fc6cb11cce279afabe233e1f756856cdd77f848f10ad95b7c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/integration/app/scv_incremental_parse_spec.spl
mirror: doc/06_spec/integration/app/scv_incremental_parse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/integration/app/scv_incremental_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/integration/app/scv_incremental_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/integration/app/scv_incremental_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 9 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/integration/app/scv_incremental_parse_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TSInputEdit: exact bytes and row,col points for a mid-line replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_incremental_parse_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'TSInputEdit: points cross newlines correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/integration/app/scv_incremental_parse_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'session open retains a parse tree and reports honest fallback mode' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
