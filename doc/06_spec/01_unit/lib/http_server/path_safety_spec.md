# Path Safety Specification

> Tests covering path_is_safe — dot-dot traversal rejection, path_is_safe — encoded traversal rejection, path_is_safe — backslash traversal rejection, path_is_safe — double-slash rejection, path_is_safe — null byte rejection, path_is_safe — valid paths accepted, path_is_safe — encoded-slash traversal rejection, path_is_safe — decoded-form false positives stay allowed.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 30 | 30 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Path Safety Specification

## Scenarios

### path_is_safe — dot-dot traversal rejection

#### rejects /../ in middle of path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects /../ in middle of path
   - Expected: path_is_safe("/../etc/passwd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects /../ in middle of path")
expect(path_is_safe("/../etc/passwd")).to_equal(false)
```

</details>

#### rejects /.. at end of path

- rejects /.. at end of path
   - Expected: path_is_safe("/api/..") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects /.. at end of path")
expect(path_is_safe("/api/..")).to_equal(false)
```

</details>

#### rejects ../ at start

- rejects ../ at start
   - Expected: path_is_safe("../secret") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ../ at start")
expect(path_is_safe("../secret")).to_equal(false)
```

</details>

#### rejects bare ..

- rejects bare ..
   - Expected: path_is_safe("..") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare ..")
expect(path_is_safe("..")).to_equal(false)
```

</details>

#### rejects nested traversal

- rejects nested traversal
   - Expected: path_is_safe("/a/b/../../etc/shadow") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects nested traversal")
expect(path_is_safe("/a/b/../../etc/shadow")).to_equal(false)
```

</details>

### path_is_safe — encoded traversal rejection

#### rejects %2e%2e (both dots encoded)

- rejects %2e%2e (both dots encoded)
   - Expected: path_is_safe("/%2e%2e/etc/passwd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects %2e%2e (both dots encoded)")
expect(path_is_safe("/%2e%2e/etc/passwd")).to_equal(false)
```

</details>

#### rejects .%2e (second dot encoded)

- rejects .%2e (second dot encoded)
   - Expected: path_is_safe("/.%2e/secret") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects .%2e (second dot encoded)")
expect(path_is_safe("/.%2e/secret")).to_equal(false)
```

</details>

#### rejects %2e. (first dot encoded)

- rejects %2e. (first dot encoded)
   - Expected: path_is_safe("/%2e./secret") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects %2e. (first dot encoded)")
expect(path_is_safe("/%2e./secret")).to_equal(false)
```

</details>

#### rejects uppercase %2E%2E

- rejects uppercase %2E%2E
   - Expected: path_is_safe("/%2E%2E/private") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects uppercase %2E%2E")
expect(path_is_safe("/%2E%2E/private")).to_equal(false)
```

</details>

### path_is_safe — backslash traversal rejection

#### rejects backslash-dot-dot prefix

- rejects backslash-dot-dot prefix
   - Expected: path_is_safe("\\..\\windows") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects backslash-dot-dot prefix")
expect(path_is_safe("\\..\\windows")).to_equal(false)
```

</details>

#### rejects dot-dot-backslash

- rejects dot-dot-backslash
   - Expected: path_is_safe("..\\etc") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects dot-dot-backslash")
expect(path_is_safe("..\\etc")).to_equal(false)
```

</details>

### path_is_safe — double-slash rejection

#### rejects // at start

- rejects // at start
   - Expected: path_is_safe("//etc/passwd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects // at start")
expect(path_is_safe("//etc/passwd")).to_equal(false)
```

</details>

#### rejects // in middle

- rejects // in middle
   - Expected: path_is_safe("/api//secret") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects // in middle")
expect(path_is_safe("/api//secret")).to_equal(false)
```

</details>

### path_is_safe — null byte rejection

#### rejects literal null byte

- rejects literal null byte
   - Expected: path_is_safe(p) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects literal null byte")
val p = "/file\0.txt"
expect(path_is_safe(p)).to_equal(false)
```

</details>

#### rejects %00 encoded null

- rejects %00 encoded null
   - Expected: path_is_safe("/file%00.txt") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects %00 encoded null")
expect(path_is_safe("/file%00.txt")).to_equal(false)
```

</details>

### path_is_safe — valid paths accepted

#### accepts root

- accepts root
   - Expected: path_is_safe("/") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts root")
expect(path_is_safe("/")).to_equal(true)
```

</details>

#### accepts normal file path

- accepts normal file path
   - Expected: path_is_safe("/static/style.css") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts normal file path")
expect(path_is_safe("/static/style.css")).to_equal(true)
```

</details>

#### accepts path with dots in filename

- accepts path with dots in filename
   - Expected: path_is_safe("/js/app.min.js") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with dots in filename")
expect(path_is_safe("/js/app.min.js")).to_equal(true)
```

</details>

#### accepts path with numbers

- accepts path with numbers
   - Expected: path_is_safe("/api/v2/users/42") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with numbers")
expect(path_is_safe("/api/v2/users/42")).to_equal(true)
```

</details>

#### accepts path with query-like segment

- accepts path with query-like segment
   - Expected: path_is_safe("/search?q=hello") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts path with query-like segment")
expect(path_is_safe("/search?q=hello")).to_equal(true)
```

</details>

#### accepts single dot segment (current directory reference)

- accepts single dot segment (current directory reference)
   - Expected: path_is_safe("/./safe") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts single dot segment (current directory reference)")
expect(path_is_safe("/./safe")).to_equal(true)
```

</details>

### path_is_safe — encoded-slash traversal rejection

#### rejects ..%2f prefix (encoded slash, literal dots)

- rejects ..%2f prefix (encoded slash, literal dots)
   - Expected: path_is_safe("..%2fetc%2fpasswd") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects ..%2f prefix (encoded slash, literal dots)")
expect(path_is_safe("..%2fetc%2fpasswd")).to_equal(false)
```

</details>

#### rejects bare ..%2f

- rejects bare ..%2f
   - Expected: path_is_safe("..%2f") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bare ..%2f")
expect(path_is_safe("..%2f")).to_equal(false)
```

</details>

#### rejects %2f.. at end

- rejects %2f.. at end
   - Expected: path_is_safe("/files%2f..") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects %2f.. at end")
expect(path_is_safe("/files%2f..")).to_equal(false)
```

</details>

#### rejects embedded a%2f..%2fb traversal

- rejects embedded a%2f..%2fb traversal
   - Expected: path_is_safe("/a%2f..%2fb") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects embedded a%2f..%2fb traversal")
expect(path_is_safe("/a%2f..%2fb")).to_equal(false)
```

</details>

#### rejects encoded backslash traversal ..%5c

- rejects encoded backslash traversal ..%5c
   - Expected: path_is_safe("..%5cwindows") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects encoded backslash traversal ..%5c")
expect(path_is_safe("..%5cwindows")).to_equal(false)
```

</details>

#### rejects fully-encoded %2e%2e%2f

- rejects fully-encoded %2e%2e%2f
   - Expected: path_is_safe("%2e%2e%2fsecret") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects fully-encoded %2e%2e%2f")
expect(path_is_safe("%2e%2e%2fsecret")).to_equal(false)
```

</details>

### path_is_safe — decoded-form false positives stay allowed

#### accepts filename with encoded dot between literal dots

- accepts filename with encoded dot between literal dots
   - Expected: path_is_safe("/foo.%2ebar") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts filename with encoded dot between literal dots")
expect(path_is_safe("/foo.%2ebar")).to_equal(true)
```

</details>

#### accepts filename containing double dots without separator

- accepts filename containing double dots without separator
   - Expected: path_is_safe("/docs/file..txt") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts filename containing double dots without separator")
expect(path_is_safe("/docs/file..txt")).to_equal(true)
```

</details>

#### accepts version-like segment a..b

- accepts version-like segment a..b
   - Expected: path_is_safe("/range/v1..v2") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts version-like segment a..b")
expect(path_is_safe("/range/v1..v2")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/path_safety_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering path_is_safe — dot-dot traversal rejection, path_is_safe — encoded traversal rejection, path_is_safe — backslash traversal rejection, path_is_safe — double-slash rejection, path_is_safe — null byte rejection, path_is_safe — valid paths accepted, path_is_safe — encoded-slash traversal rejection, path_is_safe — decoded-form false positives stay allowed.
- path_is_safe — dot-dot traversal rejection
- path_is_safe — encoded traversal rejection
- path_is_safe — backslash traversal rejection
- path_is_safe — double-slash rejection
- path_is_safe — null byte rejection
- path_is_safe — valid paths accepted
- path_is_safe — encoded-slash traversal rejection
- path_is_safe — decoded-form false positives stay allowed

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 30 |
| Active scenarios | 30 |
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

- Canonical SPipe generation for source `5e14b61a5fe196e2ef736fc3d122fa697410f1884afe630ffefdee525b93fd39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e14b61a5fe196e2ef736fc3d122fa697410f1884afe630ffefdee525b93fd39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e14b61a5fe196e2ef736fc3d122fa697410f1884afe630ffefdee525b93fd39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/http_server/path_safety_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/path_safety_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/path_safety_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/path_safety_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/path_safety_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects /../ in middle of path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/path_safety_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects /.. at end of path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/path_safety_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects ../ at start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
