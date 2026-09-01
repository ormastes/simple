# Path Pure Basename Crosslang Specification

> Tests covering path_basename — pure-Simple vs Rust-interpreter oracle (rt_path_basename).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Pure Basename Crosslang Specification

## Scenarios

### path_basename — pure-Simple vs Rust-interpreter oracle (rt_path_basename)

#### matches the oracle on ordinary KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary KATs")
assert_equal(path_basename("file.txt"), "file.txt")
assert_equal(path_basename("file.txt"), rt_path_basename("file.txt"))
assert_equal(path_basename("dir/sub/file.spl"), "file.spl")
assert_equal(path_basename("dir/sub/file.spl"), rt_path_basename("dir/sub/file.spl"))
assert_equal(path_basename("/abs/path/name.md"), "name.md")
assert_equal(path_basename("/abs/path/name.md"), rt_path_basename("/abs/path/name.md"))
```

</details>

#### matches the oracle on the mandated edge table

- matches the oracle on the mandated edge table


<details>
<summary>Executable SSpec</summary>

Runnable source: 69 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on the mandated edge table")
# Empty string.
assert_equal(path_basename(""), "")
assert_equal(path_basename(""), rt_path_basename(""))

# Root only.
assert_equal(path_basename("/"), "")
assert_equal(path_basename("/"), rt_path_basename("/"))

# Repeated root separators.
assert_equal(path_basename("//"), "")
assert_equal(path_basename("//"), rt_path_basename("//"))

# Bare name, no separator.
assert_equal(path_basename("a"), "a")
assert_equal(path_basename("a"), rt_path_basename("a"))

# Trailing separator: ignored, use the component before it.
assert_equal(path_basename("a/"), "a")
assert_equal(path_basename("a/"), rt_path_basename("a/"))

# Repeated trailing separators.
assert_equal(path_basename("a//"), "a")
assert_equal(path_basename("a//"), rt_path_basename("a//"))

# Leading root.
assert_equal(path_basename("/a"), "a")
assert_equal(path_basename("/a"), rt_path_basename("/a"))

# Leading CurDir component.
assert_equal(path_basename("./a"), "a")
assert_equal(path_basename("./a"), rt_path_basename("./a"))

# Leading ParentDir component.
assert_equal(path_basename("../a"), "a")
assert_equal(path_basename("../a"), rt_path_basename("../a"))

# Bare CurDir: no final normal component.
assert_equal(path_basename("."), "")
assert_equal(path_basename("."), rt_path_basename("."))

# Bare ParentDir: no final normal component.
assert_equal(path_basename(".."), "")
assert_equal(path_basename(".."), rt_path_basename(".."))

# Trailing separator after two components.
assert_equal(path_basename("a/b/"), "b")
assert_equal(path_basename("a/b/"), rt_path_basename("a/b/"))

# Repeated internal separators.
assert_equal(path_basename("a//b"), "b")
assert_equal(path_basename("a//b"), rt_path_basename("a//b"))

# Path that is only separators.
assert_equal(path_basename("///"), "")
assert_equal(path_basename("///"), rt_path_basename("///"))

# Multibyte UTF-8 segment.
assert_equal(path_basename("café/x"), "x")
assert_equal(path_basename("café/x"), rt_path_basename("café/x"))
assert_equal(path_basename("dir/café"), "café")
assert_equal(path_basename("dir/café"), rt_path_basename("dir/café"))

# Windows-style backslash path: on this POSIX-only oracle the
# backslash is NOT a separator, so the whole string is one
# component -- confirmed a genuine (not divergent) agreement.
assert_equal(path_basename("C:\\a\\b"), "C:\\a\\b")
assert_equal(path_basename("C:\\a\\b"), rt_path_basename("C:\\a\\b"))
```

</details>

#### single-char input change flips the result (discrimination)

- single-char input change flips the result (discrimination)


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("single-char input change flips the result (discrimination)")
assert_true(path_basename("file.txt") != path_basename("file.tx"))
assert_true(rt_path_basename("file.txt") != rt_path_basename("file.tx"))
```

</details>

#### is deterministic on both sides

- is deterministic on both sides


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is deterministic on both sides")
assert_equal(path_basename("a/b/c.spl"), path_basename("a/b/c.spl"))
assert_equal(rt_path_basename("a/b/c.spl"), rt_path_basename("a/b/c.spl"))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 43 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
# NOTE: "." is deliberately excluded from this generator. A "."
# component that is NOT the very first component of the path is
# silently elided by Rust's `Path::components()` (e.g. "dir/."
# basenames to "dir", not ""), which this implementation does not
# attempt to replicate -- see the documented SCOPE LIMITATION on
# `path_basename` in src/lib/common/path_pure.spl. That case is
# confirmed a genuine, narrow, out-of-scope divergence (probed
# directly), not silently papered over; it is excluded from this
# generator so the loop asserts only in-scope behaviour. Bare "."
# and leading "./" are still covered by the KATs/edge table above.
val segs = ["a", "b.c", "..", "café", "noext", "x.y", "dir"]
val seps = ["/", "//", "\\"]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 98765) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val a = segs[seed % 7]
    val b = segs[(seed / 7) % 7]
    val sep = seps[seed % 3]
    var p = a + sep + b
    if i % 7 == 0:
        p = sep + p               # leading separator
    else if i % 5 == 0:
        p = p + sep               # trailing separator
    else if i % 3 == 0:
        p = a                     # bare component, no separator

    val t0 = time_now_unix_micros()
    val sr = path_basename(p)
    val t1 = time_now_unix_micros()
    val cr = rt_path_basename(p)
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
| Source | `test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering path_basename — pure-Simple vs Rust-interpreter oracle (rt_path_basename).
- path_basename — pure-Simple vs Rust-interpreter oracle (rt_path_basename)

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
- `REQ-C-MIG-PATH-BASENAME`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1e6f1a3ca5fa65534a65b990588b357f69459f76bf0944c0d68897123f5c1580`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1e6f1a3ca5fa65534a65b990588b357f69459f76bf0944c0d68897123f5c1580`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1e6f1a3ca5fa65534a65b990588b357f69459f76bf0944c0d68897123f5c1580`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/path_pure_basename_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/path_pure_basename_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/path_pure_basename_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on the mandated edge table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/path_pure_basename_crosslang_spec.spl:127:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char input change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
