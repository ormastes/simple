# Dict Contains Pure Crosslang Specification

> Tests covering dict_has_key_text — pure-Simple vs C-backed oracle (rt_dict_contains).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dict Contains Pure Crosslang Specification

## Scenarios

### dict_has_key_text — pure-Simple vs C-backed oracle (rt_dict_contains)

#### matches the oracle on ordinary KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary KATs")
val d: {text: i64} = {"a": 1, "b": 2, "c": 3}
assert_equal(dict_has_key_text(d, "a"), true)
assert_equal(dict_has_key_text(d, "a"), rt_dict_contains(d, "a"))
assert_equal(dict_has_key_text(d, "z"), false)
assert_equal(dict_has_key_text(d, "z"), rt_dict_contains(d, "z"))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 47 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# Empty dict, empty key.
val empty: {text: i64} = {}
assert_equal(dict_has_key_text(empty, ""), false)
assert_equal(dict_has_key_text(empty, ""), rt_dict_contains(empty, ""))

# Empty dict, non-empty key.
assert_equal(dict_has_key_text(empty, "x"), false)
assert_equal(dict_has_key_text(empty, "x"), rt_dict_contains(empty, "x"))

# Single-entry dict, empty-string key present.
val with_empty_key: {text: i64} = {"": 42}
assert_equal(dict_has_key_text(with_empty_key, ""), true)
assert_equal(dict_has_key_text(with_empty_key, ""), rt_dict_contains(with_empty_key, ""))

# Single-entry dict, single-char key match and mismatch.
val one: {text: i64} = {"k": 7}
assert_equal(dict_has_key_text(one, "k"), true)
assert_equal(dict_has_key_text(one, "k"), rt_dict_contains(one, "k"))
assert_equal(dict_has_key_text(one, "j"), false)
assert_equal(dict_has_key_text(one, "j"), rt_dict_contains(one, "j"))

# Key that is a prefix of a real key, and a real key plus suffix
# (both absent -- boundary against substring-style false positives).
val prefixed: {text: i64} = {"hello": 1}
assert_equal(dict_has_key_text(prefixed, "hell"), false)
assert_equal(dict_has_key_text(prefixed, "hell"), rt_dict_contains(prefixed, "hell"))
assert_equal(dict_has_key_text(prefixed, "hello!"), false)
assert_equal(dict_has_key_text(prefixed, "hello!"), rt_dict_contains(prefixed, "hello!"))

# Multibyte UTF-8 key, matching and not matching (whole-key
# equality only -- no byte/codepoint offset indexing involved).
val multibyte: {text: i64} = {"caf\u{e9}": 9, "\u{65e5}\u{672c}\u{8a9e}": 3}
assert_equal(dict_has_key_text(multibyte, "caf\u{e9}"), true)
assert_equal(dict_has_key_text(multibyte, "caf\u{e9}"), rt_dict_contains(multibyte, "caf\u{e9}"))
assert_equal(dict_has_key_text(multibyte, "\u{65e5}\u{672c}\u{8a9e}"), true)
assert_equal(dict_has_key_text(multibyte, "\u{65e5}\u{672c}\u{8a9e}"), rt_dict_contains(multibyte, "\u{65e5}\u{672c}\u{8a9e}"))
assert_equal(dict_has_key_text(multibyte, "cafe"), false)
assert_equal(dict_has_key_text(multibyte, "cafe"), rt_dict_contains(multibyte, "cafe"))

# NUL (0x00) and DEL (0x7f) byte-class boundary keys.
val boundary: {text: i64} = {"x\u{0}": 1, "x\u{7f}": 2}
assert_equal(dict_has_key_text(boundary, "x\u{0}"), true)
assert_equal(dict_has_key_text(boundary, "x\u{0}"), rt_dict_contains(boundary, "x\u{0}"))
assert_equal(dict_has_key_text(boundary, "x\u{7f}"), true)
assert_equal(dict_has_key_text(boundary, "x\u{7f}"), rt_dict_contains(boundary, "x\u{7f}"))
```

</details>

#### single-char key change flips the result (discrimination)

- single-char key change flips the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char key change flips the result (discrimination)")
val d: {text: i64} = {"abc": 1}
assert_true(dict_has_key_text(d, "abc") != dict_has_key_text(d, "abd"))
assert_true(rt_dict_contains(d, "abc") != rt_dict_contains(d, "abd"))
```

</details>

#### is deterministic on both sides

- is deterministic on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic on both sides")
val d: {text: i64} = {"a": 1, "b": 2}
assert_equal(dict_has_key_text(d, "a"), dict_has_key_text(d, "a"))
assert_equal(rt_dict_contains(d, "a"), rt_dict_contains(d, "a"))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val d: {text: i64} = {
    "hello": 1, "world": 2, "": 3, "a": 4,
    "caf\u{e9}": 5, "\u{65e5}\u{672c}\u{8a9e}": 6, "x\u{0}": 7, "zzz": 8
}
val probe_keys = ["hello", "world", "missing", "a", "caf\u{e9}", "\u{65e5}\u{672c}\u{8a9e}", "x\u{0}", "notthere"]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val key = probe_keys[seed % 8]

    val t0 = time_now_unix_micros()
    val sr = dict_has_key_text(d, key)
    val t1 = time_now_unix_micros()
    val cr = rt_dict_contains(d, key)
    val t2 = time_now_unix_micros()
    simple_us = simple_us + (t1 - t0)
    c_us = c_us + (t2 - t1)
    assert_equal(sr, cr)
    i = i + 1
print("perf_evidence: shared_corpus=100 simple_us={simple_us} c_us={c_us}")
assert_true(simple_us >= 0 and c_us >= 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering dict_has_key_text — pure-Simple vs C-backed oracle (rt_dict_contains).
- dict_has_key_text — pure-Simple vs C-backed oracle (rt_dict_contains)

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
- `REQ-C-MIG-DICT-CONTAINS`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `febe0117fc08b5a4e30e345a5438691d3438ba4eeedc09b5f5cc65503354d41a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `febe0117fc08b5a4e30e345a5438691d3438ba4eeedc09b5f5cc65503354d41a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `febe0117fc08b5a4e30e345a5438691d3438ba4eeedc09b5f5cc65503354d41a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/dict_contains_pure_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/dict_contains_pure_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/dict_contains_pure_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl:71:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/dict_contains_pure_crosslang_spec.spl:129:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char key change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
