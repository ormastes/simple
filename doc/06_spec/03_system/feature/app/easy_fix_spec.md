# EasyFix Auto-Fix System

> Tests the EasyFix automatic code repair system that suggests and applies fixes for common compiler errors. Verifies that fix suggestions are accurate, that dry-run mode previews changes correctly, and that applied fixes resolve the errors.

<!-- sdn-diagram:id=easy_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=easy_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

easy_fix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=easy_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 50 | 50 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# EasyFix Auto-Fix System

Tests the EasyFix automatic code repair system that suggests and applies fixes for common compiler errors. Verifies that fix suggestions are accurate, that dry-run mode previews changes correctly, and that applied fixes resolve the errors.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/easy_fix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the EasyFix automatic code repair system that suggests and applies fixes
for common compiler errors. Verifies that fix suggestions are accurate, that
dry-run mode previews changes correctly, and that applied fixes resolve the errors.

## Scenarios

### EasyFix Data Structures

#### FixConfidence enum

#### has Safe level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = FixConfidence.Safe
expect c == FixConfidence.Safe
```

</details>

#### has Likely level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = FixConfidence.Likely
expect c == FixConfidence.Likely
```

</details>

#### has Uncertain level

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val c = FixConfidence.Uncertain
expect c == FixConfidence.Uncertain
```

</details>

#### Safe != Likely

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect FixConfidence.Safe != FixConfidence.Likely
```

</details>

#### Safe != Uncertain

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect FixConfidence.Safe != FixConfidence.Uncertain
```

</details>

#### Likely != Uncertain

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect FixConfidence.Likely != FixConfidence.Uncertain
```

</details>

#### Replacement creation

#### creates a replacement with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Replacement.create(
    file: "test.spl",
    start: 10,
    end: 15,
    line: 2,
    column: 5,
    new_text: "new_value"
)
expect rep.file == "test.spl"
expect rep.start == 10
expect rep.end == 15
expect rep.line == 2
expect rep.column == 5
expect rep.new_text == "new_value"
```

</details>

#### creates a zero-length insertion

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Replacement.create(
    file: "test.spl",
    start: 10,
    end: 10,
    line: 1,
    column: 11,
    new_text: "inserted "
)
expect rep.start == rep.end
expect rep.new_text == "inserted "
```

</details>

#### creates a deletion (empty new_text)

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Replacement.create(
    file: "test.spl",
    start: 5,
    end: 10,
    line: 1,
    column: 6,
    new_text: ""
)
expect rep.new_text == ""
expect rep.end - rep.start == 5
```

</details>

#### formats for display

1. expect formatted contains
2. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val rep = Replacement.create(
    file: "src/main.spl",
    start: 0,
    end: 5,
    line: 1,
    column: 1,
    new_text: "hello"
)
val formatted = rep.format()
expect formatted.contains("src/main.spl")
expect formatted.contains("hello")
```

</details>

#### EasyFix creation

#### creates an empty fix

1. expect fix replacements len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = EasyFix.create(
    id: "L:test:1",
    description: "test fix",
    confidence: FixConfidence.Safe
)
expect fix.id == "L:test:1"
expect fix.description == "test fix"
expect fix.replacements.len() == 0
```

</details>

#### adds replacements

1. expect fix replacements len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fix = EasyFix.create(
    id: "L:test:1",
    description: "test fix",
    confidence: FixConfidence.Safe
)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 5, line: 1, column: 1, new_text: "hello"
))
expect fix.replacements.len() == 1
```

</details>

#### adds multiple replacements

1. expect fix replacements len


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fix = EasyFix.create(
    id: "L:test:1",
    description: "multi-replacement fix",
    confidence: FixConfidence.Likely
)
fix.add_replacement(Replacement.create(
    file: "a.spl", start: 0, end: 3, line: 1, column: 1, new_text: "xxx"
))
fix.add_replacement(Replacement.create(
    file: "b.spl", start: 10, end: 15, line: 2, column: 1, new_text: "yyy"
))
expect fix.replacements.len() == 2
```

</details>

#### reports safe confidence

1. expect fix is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
expect fix.is_safe() == true
```

</details>

#### reports non-safe for Likely

1. expect fix is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Likely)
expect fix.is_safe() == false
```

</details>

#### reports non-safe for Uncertain

1. expect fix is safe


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Uncertain)
expect fix.is_safe() == false
```

</details>

#### formats confidence as string

1. expect safe confidence str
2. expect likely confidence str
3. expect uncertain confidence str


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "f3", description: "d", confidence: FixConfidence.Uncertain)
expect safe.confidence_str() == "safe"
expect likely.confidence_str() == "likely"
expect uncertain.confidence_str() == "uncertain"
```

</details>

### FixApplicator Engine

#### single replacement

#### replaces text at the beginning

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello world"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 5, line: 1, column: 1, new_text: "goodbye"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "goodbye world"
    case Err(e):
        expect false
```

</details>

#### replaces text at the end

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello world"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 6, end: 11, line: 1, column: 7, new_text: "earth"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "hello earth"
    case Err(e):
        expect false
```

</details>

#### replaces text in the middle

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "aaa bbb ccc"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 4, end: 7, line: 1, column: 5, new_text: "xxx"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "aaa xxx ccc"
    case Err(e):
        expect false
```

</details>

#### inserts text (zero-length span)

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello world"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 5, end: 5, line: 1, column: 6, new_text: " beautiful"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "hello beautiful world"
    case Err(e):
        expect false
```

</details>

#### deletes text (empty new_text)

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello beautiful world"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 5, end: 15, line: 1, column: 6, new_text: ""
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "hello world"
    case Err(e):
        expect false
```

</details>

#### multiple non-overlapping replacements

#### applies two fixes in same file

1. var fix1 = EasyFix create
2. var fix2 = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "aaa bbb ccc"

var fix1 = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix1.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 3, line: 1, column: 1, new_text: "xxx"
))

var fix2 = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Safe)
fix2.add_replacement(Replacement.create(
    file: "test.spl", start: 8, end: 11, line: 1, column: 9, new_text: "zzz"
))

val result = FixApplicator.apply([fix1, fix2], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "xxx bbb zzz"
    case Err(e):
        expect false
```

</details>

#### applies three fixes preserving order

1. var fix1 = EasyFix create
2. var fix2 = EasyFix create
3. var fix3 = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "111 222 333 444"

var fix1 = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix1.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 3, line: 1, column: 1, new_text: "aaa"
))
var fix2 = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Safe)
fix2.add_replacement(Replacement.create(
    file: "test.spl", start: 4, end: 7, line: 1, column: 5, new_text: "bbb"
))
var fix3 = EasyFix.create(id: "f3", description: "d", confidence: FixConfidence.Safe)
fix3.add_replacement(Replacement.create(
    file: "test.spl", start: 12, end: 15, line: 1, column: 13, new_text: "ddd"
))

val result = FixApplicator.apply([fix1, fix2, fix3], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "aaa bbb 333 ddd"
    case Err(e):
        expect false
```

</details>

#### conflicting replacements

#### detects overlapping spans

1. var fix1 = EasyFix create
2. var fix2 = EasyFix create
3. expect e contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello world"

var fix1 = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix1.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 8, line: 1, column: 1, new_text: "xxx"
))
var fix2 = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Safe)
fix2.add_replacement(Replacement.create(
    file: "test.spl", start: 5, end: 11, line: 1, column: 6, new_text: "yyy"
))

val result = FixApplicator.apply([fix1, fix2], sources)
match result:
    case Ok(_):
        expect false  # Should have failed
    case Err(e):
        expect e.contains("overlap") or e.contains("Conflicting")
```

</details>

#### multi-file fixes

#### applies fixes to different files

1. var fix1 = EasyFix create
2. var fix2 = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["a.spl"] = "file_a content"
sources["b.spl"] = "file_b content"

var fix1 = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix1.add_replacement(Replacement.create(
    file: "a.spl", start: 0, end: 6, line: 1, column: 1, new_text: "alpha"
))
var fix2 = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Safe)
fix2.add_replacement(Replacement.create(
    file: "b.spl", start: 0, end: 6, line: 1, column: 1, new_text: "beta"
))

val result = FixApplicator.apply([fix1, fix2], sources)
match result:
    case Ok(new_sources):
        expect new_sources["a.spl"] == "alpha content"
        expect new_sources["b.spl"] == "beta content"
    case Err(e):
        expect false
```

</details>

#### missing file

#### returns error for missing file

1. var fix = EasyFix create
2. expect e contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["exists.spl"] = "content"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "missing.spl", start: 0, end: 5, line: 1, column: 1, new_text: "x"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(_):
        expect false
    case Err(e):
        expect e.contains("not found") or e.contains("File not found")
```

</details>

### Fix Filtering

#### confidence filtering

#### Safe filter returns only safe fixes

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = EasyFix.create(id: "safe", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "likely", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "uncertain", description: "d", confidence: FixConfidence.Uncertain)
val fixes = [safe, likely, uncertain]

val filtered = FixApplicator.filter_by_confidence(fixes, FixConfidence.Safe)
expect filtered[0].id == "safe"
expect filtered.len() == 1
```

</details>

#### Likely filter returns safe and likely

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = EasyFix.create(id: "safe", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "likely", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "uncertain", description: "d", confidence: FixConfidence.Uncertain)
val fixes = [safe, likely, uncertain]

val filtered = FixApplicator.filter_by_confidence(fixes, FixConfidence.Likely)
expect filtered.len() == 2
```

</details>

#### Uncertain filter returns all

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val safe = EasyFix.create(id: "safe", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "likely", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "uncertain", description: "d", confidence: FixConfidence.Uncertain)
val fixes = [safe, likely, uncertain]

val filtered = FixApplicator.filter_by_confidence(fixes, FixConfidence.Uncertain)
expect filtered.len() == 3
```

</details>

#### returns empty list when no fixes match

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val uncertain = EasyFix.create(id: "u1", description: "d", confidence: FixConfidence.Uncertain)
val filtered = FixApplicator.filter_by_confidence([uncertain], FixConfidence.Safe)
expect filtered.len() == 0
```

</details>

#### ID prefix filtering

#### filters by prefix

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = EasyFix.create(id: "L:todo_format:1", description: "d", confidence: FixConfidence.Safe)
val f2 = EasyFix.create(id: "L:bare_bool:1", description: "d", confidence: FixConfidence.Safe)
val f3 = EasyFix.create(id: "L:todo_format:2", description: "d", confidence: FixConfidence.Safe)

val filtered = FixApplicator.filter_by_id([f1, f2, f3], "L:todo_format")
expect filtered.len() == 2
```

</details>

#### returns empty when no match

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = EasyFix.create(id: "L:todo:1", description: "d", confidence: FixConfidence.Safe)
val filtered = FixApplicator.filter_by_id([f1], "E:type")
expect filtered.len() == 0
```

</details>

#### matches exact prefix

1. expect filtered len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val f1 = EasyFix.create(id: "L:abc", description: "d", confidence: FixConfidence.Safe)
val f2 = EasyFix.create(id: "L:abcdef", description: "d", confidence: FixConfidence.Safe)
val filtered = FixApplicator.filter_by_id([f1, f2], "L:abc")
expect filtered.len() == 2  # Both start with "L:abc"
```

</details>

### FixReport

#### empty report

#### starts with zero counts

1. expect report modified files len
2. expect report details len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val report = FixReport.empty()
expect report.applied == 0
expect report.skipped == 0
expect report.modified_files.len() == 0
expect report.details.len() == 0
```

</details>

#### report formatting

#### formats dry-run report

1. var report = FixReport empty
2. expect output contains
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = FixReport.empty()
report.applied = 2
report.modified_files = ["a.spl", "b.spl"]
report.details = ["[f1] fix one", "[f2] fix two"]

val output = report.format(true)
expect output.contains("Would apply")
expect output.contains("2 fix(es)")
```

</details>

#### formats applied report

1. var report = FixReport empty
2. expect output contains
3. expect output contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var report = FixReport.empty()
report.applied = 1
report.modified_files = ["test.spl"]
report.details = ["[f1] fixed issue"]

val output = report.format(false)
expect output.contains("Applied")
expect output.contains("1 fix(es)")
```

</details>

### Lint-EasyFix Integration

#### Lint with EasyFix

#### creates lint with easy_fix

1.  with fix
2.  with easy fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fix = EasyFix.create(
    id: "L:todo_format:1",
    description: "add format tags",
    confidence: FixConfidence.Uncertain
)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 10, end: 10, line: 1, column: 11, new_text: "[runtime][P2] "
))

val lint = Lint.new("T001", LintLevel.Warn, LintCategory.Style,
    "TODO/FIXME missing [area][priority] format")
    .with_fix("Use: TODO: [area][P0-P3] description")
    .with_easy_fix(fix)

expect lint.easy_fix.? == true
expect lint.fix_hint.? == true
```

</details>

#### creates lint without easy_fix

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint = Lint.new("W001", LintLevel.Warn, LintCategory.Warning, "unused variable")
expect lint.easy_fix.? == false
expect lint.fix_hint.? == false
```

</details>

#### LintResult with EasyFix

#### reports has_easy_fix true when present

1. var fix = EasyFix create
2.  with easy fix
3. expect result has easy fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
val lint = Lint.new("T001", LintLevel.Warn, LintCategory.Style, "msg")
    .with_easy_fix(fix)
val result = LintResult.new("test.spl", 1, 1, lint)
expect result.has_easy_fix() == true
```

</details>

#### reports has_easy_fix false when absent

1. expect result has easy fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lint = Lint.new("W001", LintLevel.Warn, LintCategory.Warning, "msg")
val result = LintResult.new("test.spl", 1, 1, lint)
expect result.has_easy_fix() == false
```

</details>

#### includes fix info in formatted output

1. var fix = EasyFix create
2.  with easy fix
3. expect formatted contains
4. expect formatted contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var fix = EasyFix.create(id: "L:test:1", description: "d", confidence: FixConfidence.Safe)
val lint = Lint.new("T001", LintLevel.Warn, LintCategory.Style, "msg")
    .with_easy_fix(fix)
val result = LintResult.new("test.spl", 1, 1, lint)
val formatted = result.format()
expect formatted.contains("fix: available")
expect formatted.contains("L:test:1")
```

</details>

### EasyFix Edge Cases

#### empty inputs

#### handles empty fix list

1. expect new sources len


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello"
val result = FixApplicator.apply([], sources)
match result:
    case Ok(new_sources):
        expect new_sources.len() == 0  # No files modified
    case Err(_):
        expect false
```

</details>

#### handles fix with no replacements

1. expect new sources len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello"
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources.len() == 0  # No changes needed
    case Err(_):
        expect false
```

</details>

#### replacement at file boundaries

#### replaces entire file content

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "old"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 3, line: 1, column: 1, new_text: "new content"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "new content"
    case Err(_):
        expect false
```

</details>

#### inserts at beginning of file

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "world"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 0, line: 1, column: 1, new_text: "hello "
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "hello world"
    case Err(_):
        expect false
```

</details>

#### appends at end of file

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "hello"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 5, end: 5, line: 1, column: 6, new_text: " world"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "hello world"
    case Err(_):
        expect false
```

</details>

#### replacement size changes

#### handles replacement longer than original

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "ab"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 2, line: 1, column: 1, new_text: "abcdef"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "abcdef"
    case Err(_):
        expect false
```

</details>

#### handles replacement shorter than original

1. var fix = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "abcdef"

var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 6, line: 1, column: 1, new_text: "ab"
))

val result = FixApplicator.apply([fix], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "ab"
    case Err(_):
        expect false
```

</details>

#### adjacent replacements

#### applies adjacent non-overlapping fixes

1. var fix1 = EasyFix create
2. var fix2 = EasyFix create
3. var fix3 = EasyFix create


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var sources: Dict<String, String> = {}
sources["test.spl"] = "aabbcc"

var fix1 = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
fix1.add_replacement(Replacement.create(
    file: "test.spl", start: 0, end: 2, line: 1, column: 1, new_text: "xx"
))
var fix2 = EasyFix.create(id: "f2", description: "d", confidence: FixConfidence.Safe)
fix2.add_replacement(Replacement.create(
    file: "test.spl", start: 2, end: 4, line: 1, column: 3, new_text: "yy"
))
var fix3 = EasyFix.create(id: "f3", description: "d", confidence: FixConfidence.Safe)
fix3.add_replacement(Replacement.create(
    file: "test.spl", start: 4, end: 6, line: 1, column: 5, new_text: "zz"
))

val result = FixApplicator.apply([fix1, fix2, fix3], sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"] == "xxyyzz"
    case Err(_):
        expect false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 50 |
| Active scenarios | 50 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
