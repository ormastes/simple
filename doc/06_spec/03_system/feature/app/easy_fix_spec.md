# EasyFix Auto-Fix System

> Tests the EasyFix automatic code repair system that suggests and applies fixes for common compiler errors. Verifies that fix suggestions are accurate, that dry-run mode previews changes correctly, and that applied fixes resolve the errors.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the EasyFix automatic code repair system that suggests and applies fixes
for common compiler errors. Verifies that fix suggestions are accurate, that
dry-run mode previews changes correctly, and that applied fixes resolve the errors.

## Scenarios

### EasyFix Data Structures

#### FixConfidence enum

#### has Safe level

- has Safe level


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Safe level")
val c = FixConfidence.Safe
expect c == FixConfidence.Safe
```

</details>

#### has Likely level

- has Likely level


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Likely level")
val c = FixConfidence.Likely
expect c == FixConfidence.Likely
```

</details>

#### has Uncertain level

- has Uncertain level


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("has Uncertain level")
val c = FixConfidence.Uncertain
expect c == FixConfidence.Uncertain
```

</details>

#### Safe != Likely

- Safe != Likely


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Safe != Likely")
expect FixConfidence.Safe != FixConfidence.Likely
```

</details>

#### Safe != Uncertain

- Safe != Uncertain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Safe != Uncertain")
expect FixConfidence.Safe != FixConfidence.Uncertain
```

</details>

#### Likely != Uncertain

- Likely != Uncertain


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Likely != Uncertain")
expect FixConfidence.Likely != FixConfidence.Uncertain
```

</details>

#### Replacement creation

#### creates a replacement with all fields

- creates a replacement with all fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a replacement with all fields")
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

- creates a zero-length insertion


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a zero-length insertion")
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

- creates a deletion (empty new_text)


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates a deletion (empty new_text)")
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

- formats for display


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats for display")
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

- creates an empty fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates an empty fix")
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

- adds replacements


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds replacements")
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

- adds multiple replacements


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("adds multiple replacements")
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

- reports safe confidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports safe confidence")
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
expect fix.is_safe() == true
```

</details>

#### reports non-safe for Likely

- reports non-safe for Likely


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports non-safe for Likely")
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Likely)
expect fix.is_safe() == false
```

</details>

#### reports non-safe for Uncertain

- reports non-safe for Uncertain


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports non-safe for Uncertain")
val fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Uncertain)
expect fix.is_safe() == false
```

</details>

#### formats confidence as string

- formats confidence as string


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats confidence as string")
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

- replaces text at the beginning


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces text at the beginning")
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

- replaces text at the end


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces text at the end")
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

- replaces text in the middle


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces text in the middle")
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

- inserts text (zero-length span)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inserts text (zero-length span)")
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

- deletes text (empty new_text)


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("deletes text (empty new_text)")
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

- applies two fixes in same file


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies two fixes in same file")
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

- applies three fixes preserving order


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies three fixes preserving order")
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

- detects overlapping spans


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects overlapping spans")
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

- applies fixes to different files


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies fixes to different files")
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

- returns error for missing file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns error for missing file")
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

- Safe filter returns only safe fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Safe filter returns only safe fixes")
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

- Likely filter returns safe and likely


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Likely filter returns safe and likely")
val safe = EasyFix.create(id: "safe", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "likely", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "uncertain", description: "d", confidence: FixConfidence.Uncertain)
val fixes = [safe, likely, uncertain]

val filtered = FixApplicator.filter_by_confidence(fixes, FixConfidence.Likely)
expect filtered.len() == 2
```

</details>

#### Uncertain filter returns all

- Uncertain filter returns all


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("Uncertain filter returns all")
val safe = EasyFix.create(id: "safe", description: "d", confidence: FixConfidence.Safe)
val likely = EasyFix.create(id: "likely", description: "d", confidence: FixConfidence.Likely)
val uncertain = EasyFix.create(id: "uncertain", description: "d", confidence: FixConfidence.Uncertain)
val fixes = [safe, likely, uncertain]

val filtered = FixApplicator.filter_by_confidence(fixes, FixConfidence.Uncertain)
expect filtered.len() == 3
```

</details>

#### returns empty list when no fixes match

- returns empty list when no fixes match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty list when no fixes match")
val uncertain = EasyFix.create(id: "u1", description: "d", confidence: FixConfidence.Uncertain)
val filtered = FixApplicator.filter_by_confidence([uncertain], FixConfidence.Safe)
expect filtered.len() == 0
```

</details>

#### ID prefix filtering

#### filters by prefix

- filters by prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("filters by prefix")
val f1 = EasyFix.create(id: "L:todo_format:1", description: "d", confidence: FixConfidence.Safe)
val f2 = EasyFix.create(id: "L:bare_bool:1", description: "d", confidence: FixConfidence.Safe)
val f3 = EasyFix.create(id: "L:todo_format:2", description: "d", confidence: FixConfidence.Safe)

val filtered = FixApplicator.filter_by_id([f1, f2, f3], "L:todo_format")
expect filtered.len() == 2
```

</details>

#### returns empty when no match

- returns empty when no match


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns empty when no match")
val f1 = EasyFix.create(id: "L:todo:1", description: "d", confidence: FixConfidence.Safe)
val filtered = FixApplicator.filter_by_id([f1], "E:type")
expect filtered.len() == 0
```

</details>

#### matches exact prefix

- matches exact prefix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("matches exact prefix")
val f1 = EasyFix.create(id: "L:abc", description: "d", confidence: FixConfidence.Safe)
val f2 = EasyFix.create(id: "L:abcdef", description: "d", confidence: FixConfidence.Safe)
val filtered = FixApplicator.filter_by_id([f1, f2], "L:abc")
expect filtered.len() == 2  # Both start with "L:abc"
```

</details>

### FixReport

#### empty report

#### starts with zero counts

- starts with zero counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("starts with zero counts")
val report = FixReport.empty()
expect report.applied == 0
expect report.skipped == 0
expect report.modified_files.len() == 0
expect report.details.len() == 0
```

</details>

#### report formatting

#### formats dry-run report

- formats dry-run report


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats dry-run report")
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

- formats applied report


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats applied report")
var report = FixReport.empty()
report.applied = 1
report.modified_files = ["test.spl"]
report.details = ["[f1] fixed issue"]

val output = report.format(false)
expect output.contains("Applied")
expect output.contains("1 fix(es)")
```

</details>

### EasyFixLint-EasyFix Integration

#### EasyFixLint with EasyFix

#### creates lint with easy_fix

- creates lint with easy_fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates lint with easy_fix")
var fix = EasyFix.create(
    id: "L:todo_format:1",
    description: "add format tags",
    confidence: FixConfidence.Uncertain
)
fix.add_replacement(Replacement.create(
    file: "test.spl", start: 10, end: 10, line: 1, column: 11, new_text: "[runtime][P2] "
))

# WRONG-CONSTRUCTOR FIX (2026-08-04): `EasyFixLint` declares no
# `static fn new` (src/lib/nogc_sync_mut/tooling/easy_fix/types.spl:240)
# — its siblings Replacement/EasyFix use `static fn create`, and the
# language rule is `Point(x: 3, y: 4)`, not `.new()`. `EasyFixLint.new(...)`
# therefore died with "semantic: unknown static method new on class
# EasyFixLint". Use the field constructor with all six declared fields.
val lint = EasyFixLint(code: "T001", level: LintLevel.Warn, category: LintCategory.Style,
    message: "TODO/FIXME missing [area][priority] format",
    fix_hint: nil, easy_fix: nil)
    .with_fix("Use: TODO: [area][P0-P3] description")
    .with_easy_fix(fix)

expect lint.easy_fix != nil
expect lint.fix_hint != nil
```

</details>

#### creates lint without easy_fix

- creates lint without easy_fix


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates lint without easy_fix")
val lint = EasyFixLint(code: "W001", level: LintLevel.Warn, category: LintCategory.Warning,
    message: "unused variable", fix_hint: nil, easy_fix: nil)
expect lint.easy_fix == nil
expect lint.fix_hint == nil
```

</details>

#### EasyFixLintResult with EasyFix

#### reports has_easy_fix true when present

- reports has_easy_fix true when present


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports has_easy_fix true when present")
var fix = EasyFix.create(id: "f1", description: "d", confidence: FixConfidence.Safe)
val lint = EasyFixLint(code: "T001", level: LintLevel.Warn, category: LintCategory.Style,
    message: "msg", fix_hint: nil, easy_fix: nil)
    .with_easy_fix(fix)
# Same wrong-constructor fix: EasyFixLintResult declares no `static fn new`
# (types.spl:277); use the field constructor.
val result = EasyFixLintResult(file_path: "test.spl", line: 1, column: 1, lint: lint)
expect result.has_easy_fix() == true
```

</details>

#### reports has_easy_fix false when absent

- reports has_easy_fix false when absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports has_easy_fix false when absent")
val lint = EasyFixLint(code: "W001", level: LintLevel.Warn, category: LintCategory.Warning,
    message: "msg", fix_hint: nil, easy_fix: nil)
# Same wrong-constructor fix: EasyFixLintResult declares no `static fn new`
# (types.spl:277); use the field constructor.
val result = EasyFixLintResult(file_path: "test.spl", line: 1, column: 1, lint: lint)
expect result.has_easy_fix() == false
```

</details>

#### includes fix info in formatted output

- includes fix info in formatted output


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("includes fix info in formatted output")
var fix = EasyFix.create(id: "L:test:1", description: "d", confidence: FixConfidence.Safe)
val lint = EasyFixLint(code: "T001", level: LintLevel.Warn, category: LintCategory.Style,
    message: "msg", fix_hint: nil, easy_fix: nil)
    .with_easy_fix(fix)
# Same wrong-constructor fix: EasyFixLintResult declares no `static fn new`
# (types.spl:277); use the field constructor.
val result = EasyFixLintResult(file_path: "test.spl", line: 1, column: 1, lint: lint)
val formatted = result.format()
expect formatted.contains("fix: available")
expect formatted.contains("L:test:1")
```

</details>

### EasyFix Edge Cases

#### empty inputs

#### handles empty fix list

- handles empty fix list


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles empty fix list")
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

- handles fix with no replacements


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles fix with no replacements")
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

- replaces entire file content


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("replaces entire file content")
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

- inserts at beginning of file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("inserts at beginning of file")
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

- appends at end of file


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("appends at end of file")
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

- handles replacement longer than original


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles replacement longer than original")
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

- handles replacement shorter than original


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles replacement shorter than original")
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

- applies adjacent non-overlapping fixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("applies adjacent non-overlapping fixes")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3051d8377dd9216cd9d00357abe3ef9beefeb0630ce699e769020a6ac3d86ae1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3051d8377dd9216cd9d00357abe3ef9beefeb0630ce699e769020a6ac3d86ae1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3051d8377dd9216cd9d00357abe3ef9beefeb0630ce699e769020a6ac3d86ae1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/app/easy_fix_spec.spl
mirror: doc/06_spec/03_system/feature/app/easy_fix_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/app/easy_fix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/app/easy_fix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/app/easy_fix_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Safe level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/easy_fix_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Likely level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/app/easy_fix_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has Uncertain level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
