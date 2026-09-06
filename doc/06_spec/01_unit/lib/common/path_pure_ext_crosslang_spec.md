# Path Pure Ext Crosslang Specification

> Tests covering path_ext — pure-Simple vs Rust-interpreter oracle (rt_path_ext).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Pure Ext Crosslang Specification

## Scenarios

### path_ext — pure-Simple vs Rust-interpreter oracle (rt_path_ext)

#### matches the oracle on ordinary KATs

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- matches the oracle on ordinary KATs


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on ordinary KATs")
assert_equal(path_ext("file.txt"), "txt")
assert_equal(path_ext("file.txt"), rt_path_ext("file.txt"))
assert_equal(path_ext("archive.tar.gz"), "gz")
assert_equal(path_ext("archive.tar.gz"), rt_path_ext("archive.tar.gz"))
assert_equal(path_ext("dir/sub/file.spl"), "spl")
assert_equal(path_ext("dir/sub/file.spl"), rt_path_ext("dir/sub/file.spl"))
assert_equal(path_ext("/abs/path/name.md"), "md")
assert_equal(path_ext("/abs/path/name.md"), rt_path_ext("/abs/path/name.md"))
```

</details>

#### matches the oracle on edge cases

- matches the oracle on edge cases


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on edge cases")
# Empty string.
assert_equal(path_ext(""), "")
assert_equal(path_ext(""), rt_path_ext(""))

# Single char, no dot.
assert_equal(path_ext("a"), "")
assert_equal(path_ext("a"), rt_path_ext("a"))

# No extension at all.
assert_equal(path_ext("Makefile"), "")
assert_equal(path_ext("Makefile"), rt_path_ext("Makefile"))

# Dotfile with no further dot: NO extension (leading dot is not a
# separator).
assert_equal(path_ext(".bashrc"), "")
assert_equal(path_ext(".bashrc"), rt_path_ext(".bashrc"))

# Dotfile WITH a further dot: extension is after the LAST dot.
assert_equal(path_ext(".tar.gz"), "gz")
assert_equal(path_ext(".tar.gz"), rt_path_ext(".tar.gz"))

# "." and ".." components: no extension.
assert_equal(path_ext("."), "")
assert_equal(path_ext("."), rt_path_ext("."))
assert_equal(path_ext(".."), "")
assert_equal(path_ext(".."), rt_path_ext(".."))

# Trailing separator: Path::file_name()/extension() ignore it and
# use the component before it (Rust semantics, confirmed against
# the oracle) -- "dir/" has no dot in "dir" so still no extension,
# but "a.b/" (probed separately below) DOES report "b".
assert_equal(path_ext("dir/"), "")
assert_equal(path_ext("dir/"), rt_path_ext("dir/"))
assert_equal(path_ext("a.b/"), "b")
assert_equal(path_ext("a.b/"), rt_path_ext("a.b/"))

# Path that is only separators: no final component at all.
assert_equal(path_ext("/"), "")
assert_equal(path_ext("/"), rt_path_ext("/"))

# Repeated separators before the final component.
assert_equal(path_ext("dir//file.txt"), "txt")
assert_equal(path_ext("dir//file.txt"), rt_path_ext("dir//file.txt"))

# Trailing dot with nothing after it.
assert_equal(path_ext("name."), "")
assert_equal(path_ext("name."), rt_path_ext("name."))

# Path with no separator at all (bare filename).
assert_equal(path_ext("readme.md"), "md")
assert_equal(path_ext("readme.md"), rt_path_ext("readme.md"))

# Dot as the very first character of a non-leading directory
# component (dotfile nested in a directory).
assert_equal(path_ext("a/.hidden"), "")
assert_equal(path_ext("a/.hidden"), rt_path_ext("a/.hidden"))
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
assert_true(path_ext("file.txt") != path_ext("file.tx"))
assert_true(rt_path_ext("file.txt") != rt_path_ext("file.tx"))
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
assert_equal(path_ext("a/b/c.spl"), path_ext("a/b/c.spl"))
assert_equal(rt_path_ext("a/b/c.spl"), rt_path_ext("a/b/c.spl"))
```

</details>

#### matches the oracle on 100 shared branch-covering vectors, with perf evidence

- matches the oracle on 100 shared branch-covering vectors, with perf evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("matches the oracle on 100 shared branch-covering vectors, with perf evidence")
use std.io_runtime.{time_now_unix_micros}
val names = ["file", "a.b", ".hidden", "..", ".", "a.tar.gz", "noext", "x.", "dir/f.rs"]
var simple_us = 0
var c_us = 0
var i = 0
while i < 100:
    var seed = (i * 2654435761 + 12345) % 4294967296
    seed = (seed * 1103515245 + 12345) % 2147483648
    val base = names[seed % 9]
    var p = base
    if i % 7 == 0:
        p = "dir/" + base            # add a leading directory
    else if i % 5 == 0:
        p = base + "/"               # trailing separator
    else if i % 3 == 0:
        p = "a/b//" + base            # repeated separators

    val t0 = time_now_unix_micros()
    val sr = path_ext(p)
    val t1 = time_now_unix_micros()
    val cr = rt_path_ext(p)
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
| Source | `test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering path_ext — pure-Simple vs Rust-interpreter oracle (rt_path_ext).
- path_ext — pure-Simple vs Rust-interpreter oracle (rt_path_ext)

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
- `REQ-C-MIG-PATH-EXT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e3d0068f318ecbfee658d9d7bcf6b9844bc4c40fe8257c1fa5f323891a0591f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3d0068f318ecbfee658d9d7bcf6b9844bc4c40fe8257c1fa5f323891a0591f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3d0068f318ecbfee658d9d7bcf6b9844bc4c40fe8257c1fa5f323891a0591f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl
mirror: doc/06_spec/01_unit/lib/common/path_pure_ext_crosslang_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/path_pure_ext_crosslang_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/path_pure_ext_crosslang_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on ordinary KATs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'matches the oracle on edge cases' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/path_pure_ext_crosslang_spec.spl:138:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'single-char input change flips the result (discrimination)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
