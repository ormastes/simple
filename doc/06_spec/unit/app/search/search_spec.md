# Search Specification

> Tests covering Text Search, Pattern Search, Symbol Search, Search Results.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 19 | 19 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Search Specification

## Scenarios

### Text Search

#### exact match

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- exact match


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exact match")
val text = "hello world"
check(text.contains("hello"))
```

</details>

#### case sensitive match

- case sensitive match


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("case sensitive match")
val text = "Hello"
check(text != "hello")
```

</details>

#### case insensitive match

- case insensitive match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("case insensitive match")
val text = "Hello"
val lower = "hello"
check(text.len() == lower.len())
```

</details>

#### no match returns empty

- no match returns empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("no match returns empty")
val text = "hello"
check(not text.contains("xyz"))
```

</details>

#### match at start

- match at start


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match at start")
val text = "hello world"
check(text.starts_with("hello"))
```

</details>

#### match at end

- match at end


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("match at end")
val text = "hello world"
check(text.ends_with("world"))
```

</details>

### Pattern Search

#### wildcard pattern

- wildcard pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wildcard pattern")
val pattern = "*.spl"
check(pattern.contains("*"))
```

</details>

#### recursive pattern

- recursive pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("recursive pattern")
val pattern = "**/*.spl"
check(pattern.contains("**"))
```

</details>

#### directory filter

- directory filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("directory filter")
val dir = "src/"
check(dir.ends_with("/"))
```

</details>

#### extension filter

- extension filter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extension filter")
val ext = ".spl"
check(ext.starts_with("."))
```

</details>

### Symbol Search

#### find function by name

- find function by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find function by name")
val query = "fn main"
check(query.starts_with("fn"))
```

</details>

#### find class by name

- find class by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find class by name")
val query = "class Point"
check(query.starts_with("class"))
```

</details>

#### find trait by name

- find trait by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find trait by name")
val query = "trait Display"
check(query.starts_with("trait"))
```

</details>

#### find enum by name

- find enum by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find enum by name")
val query = "enum Color"
check(query.starts_with("enum"))
```

</details>

### Search Results

#### result has file path

- result has file path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result has file path")
val path = "src/main.spl"
check(path.ends_with(".spl"))
```

</details>

#### result has line number

- result has line number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result has line number")
val line = 42
check(line > 0)
```

</details>

#### result has column number

- result has column number


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result has column number")
val col = 10
check(col > 0)
```

</details>

#### result has context

- result has context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("result has context")
val context = "fn main():"
check(context.len() > 0)
```

</details>

#### results are sorted by relevance

- results are sorted by relevance


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("results are sorted by relevance")
val scores = [100, 80, 60, 40]
check(scores[0] > scores[1])
check(scores[1] > scores[2])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/search/search_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Text Search, Pattern Search, Symbol Search, Search Results.
- Text Search
- Pattern Search
- Symbol Search
- Search Results

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 19 |
| Active scenarios | 19 |
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

- Canonical SPipe generation for source `08fe721fa4aba7ab432fa39ff7197ae5b7b615eec95bf649ace4e790661e8d5b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `08fe721fa4aba7ab432fa39ff7197ae5b7b615eec95bf649ace4e790661e8d5b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `08fe721fa4aba7ab432fa39ff7197ae5b7b615eec95bf649ace4e790661e8d5b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/search/search_spec.spl
mirror: doc/06_spec/unit/app/search/search_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/search/search_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/search/search_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/search/search_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exact match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/search/search_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case sensitive match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/search/search_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'case insensitive match' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
