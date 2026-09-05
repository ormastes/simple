# std.path: `rfind` not-found must mean "no separator/dot", not index -1

> `text.rfind` returns a RAW i64 sentinel (`-1` when not found), it does NOT return an `Optional`. `std.path` nevertheless matched it as one:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# std.path: `rfind` not-found must mean "no separator/dot", not index -1

`text.rfind` returns a RAW i64 sentinel (`-1` when not found), it does NOT return an `Optional`. `std.path` nevertheless matched it as one:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`text.rfind` returns a RAW i64 sentinel (`-1` when not found), it does NOT
return an `Optional`. `std.path` nevertheless matched it as one:

```simple
use std.spec.step

val sep_idx = match clean_path.rfind("/"):
    Some(idx): idx
    nil: return "."
```

The `Some` arm always won and bound `idx = -1`, so the `nil` arm was dead and
`dirname("foo.txt")` fell through to `substring(0, -1)` -- the empty string --
instead of `"."`. `extension` had the mirror defect: `substring(-1 + 1)` handed
back the whole name.

Observed before the fix (bin/simple run):

```
dirname(foo.txt)=[]        extension(README)=[README]     stem(README)=[]
```

TODO-DB row 559.

## Scenarios

### std.path rfind sentinel not-found

#### dirname of a separator-less path is \

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
```

</details>

#### extension of a dot-less name is empty, not the whole name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(path.extension("README"), "")
assert_equal(path.extension("Makefile"), "")
```

</details>

#### stem of a dot-less name is the name itself

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(path.stem("README"), "README")
```

</details>

#### still resolves paths that DO contain a separator and a dot

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
assert_equal(path.dirname("a/b"), "a")
assert_equal(path.dirname("/usr/lib/x.so"), "/usr/lib")
assert_equal(path.extension("a.txt"), "txt")
assert_equal(path.stem("a.txt"), "a")
assert_equal(path.basename("/usr/lib/x.so"), "x.so")
```

</details>

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9f0b31cc560694e331e4e356f9703409f2150975c546d552fc7230c199b4cc0a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9f0b31cc560694e331e4e356f9703409f2150975c546d552fc7230c199b4cc0a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9f0b31cc560694e331e4e356f9703409f2150975c546d552fc7230c199b4cc0a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl
mirror: doc/06_spec/01_unit/lib/path/path_rfind_sentinel_not_found_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=60 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/path/path_rfind_sentinel_not_found_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/path/path_rfind_sentinel_not_found_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl:39:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'dirname of a separator-less path is \' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl:45:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'extension of a dot-less name is empty, not the whole name' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl:49:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'stem of a dot-less name is the name itself' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/lib/path/path_rfind_sentinel_not_found_spec.spl:54:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'still resolves paths that DO contain a separator and a dot' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
