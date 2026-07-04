# EasyFix Rules

> Tests individual EasyFix rule definitions including pattern matching, fix generation, and rule priority ordering. Verifies that each rule correctly identifies its target error pattern and produces valid code transformations.

<!-- sdn-diagram:id=easy_fix_rules_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=easy_fix_rules_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

easy_fix_rules_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=easy_fix_rules_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 100 | 100 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# EasyFix Rules

Tests individual EasyFix rule definitions including pattern matching, fix generation, and rule priority ordering. Verifies that each rule correctly identifies its target error pattern and produces valid code transformations.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/app/easy_fix_rules_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests individual EasyFix rule definitions including pattern matching, fix
generation, and rule priority ordering. Verifies that each rule correctly
identifies its target error pattern and produces valid code transformations.

## Scenarios

### Rule: print_in_test_spec

#### basic detection

#### detects print() in spec file

1. expect fixes[0] id contains
2. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "it \"test\":\n    print(42)\n"
val fixes = check_print_in_test_spec(source, "my_spec.spl")
expect fixes[0].id.contains("print_in_test_spec")
expect fixes.len() == 1
```

</details>

#### detects print with string arg

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "it \"test\":\n    print(\"hello\")\n"
val fixes = check_print_in_test_spec(source, "my_spec.spl")
expect fixes.len() == 1
```

</details>

#### detects print with expression

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "it \"test\":\n    print(x + y)\n"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes.len() == 1
```

</details>

#### detects multiple prints

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "it \"a\":\n    print(1)\n    print(2)\n    print(3)\n"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes.len() == 3
```

</details>

#### generates correct replacement

1. expect fixes[0] replacements[0] new text contains
2. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    print(42)"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes[0].replacements[0].new_text.contains("expect")
expect fixes.len() == 1
```

</details>

#### preserves indentation

1. expect fixes len
2. expect rep new text starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "        print(x)"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
val rep = fixes[0].replacements[0]
expect fixes.len() == 1
expect rep.new_text.starts_with("        ")
```

</details>

#### non-spec files

#### ignores print in regular .spl files

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    print(42)\n"
val fixes = check_print_in_test_spec(source, "main.spl")
expect fixes.len() == 0
```

</details>

#### ignores print in non-spl files

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "print(42)"
val fixes = check_print_in_test_spec(source, "test.txt")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_print_in_test_spec("", "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### handles file with only comments

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# comment\n# another\n"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### has Likely confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    print(42)"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Likely: expect true
    _: fail("Expected Likely confidence")
```

</details>

### Rule: unnamed_duplicate_typed_args

#### basic detection

#### detects fn with two same types

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(Int, Int) -> Int:\n    0\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates named params

1. expect rep new text contains
2. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(Int, Int) -> Int:\n    0\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("int1: Int")
expect rep.new_text.contains("int2: Int")
```

</details>

#### detects three same types

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn triple(String, String, String):\n    pass\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### rewrites declaration and same-file positional call

1. expect fixes len
2. expect fixes[0] replacements len
3. expect fixed contains
4. expect fixed contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(Int, Int) -> Int:\n    0\nval total = add(1, 2)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
expect fixes[0].replacements.len() == 2

var sources: Dict<String, String> = {}
sources["test.spl"] = source

val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(new_sources):
        val fixed = new_sources["test.spl"]
        expect fixed.contains("fn add(int1: Int, int2: Int)")
        expect fixed.contains("add(int1: 1, int2: 2)")
    case Err(_):
        expect false
```

</details>

#### rewrites same-file positional call when duplicate typed params already have names

1. expect fixes len
2. expect fixes[0] replacements len


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn clamp(min: Int, max: Int, value: Int) -> Int:\n    value\nval result = clamp(1, 5, current)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
expect fixes[0].replacements.len() == 1
expect fixes[0].replacements[0].new_text == "min: 1, max: 5, value: current"
```

</details>

#### rewrites same-file method calls

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "me move(dx: Int, dy: Int):\n    pass\nval _ = point.move(3, 4)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
expect fixes[0].replacements[0].new_text == "dx: 3, dy: 4"
```

</details>

#### no false positives

#### ignores named params

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn add(a: Int, b: Int) -> Int:\n    a + b\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### ignores single type-only param

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn identity(Int) -> Int:\n    0\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### ignores different types

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn convert(Int, String) -> Bool:\n    true\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### does not rewrite already named calls

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn clamp(min: Int, max: Int, value: Int) -> Int:\n    value\nval result = clamp(min: 1, max: 5, value: current)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### does not rewrite ambiguous same-name call targets

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn move(dx: Int, dy: Int):\n    pass\nfn move(x: Int, y: Int):\n    pass\nval _ = move(1, 2)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### does not rewrite mismatched arity calls

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn clamp(min: Int, max: Int, value: Int) -> Int:\n    value\nval result = clamp(1, 5)\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_unnamed_duplicate_typed_args("", "test.spl")
expect fixes.len() == 0
```

</details>

#### handles me methods

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "me move(Int, Int):\n    pass\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### handles static fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static fn create(String, String) -> Self:\n    pass\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### has Uncertain confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn f(Int, Int):\n    pass\n"
val fixes = check_unnamed_duplicate_typed_args(source, "test.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Uncertain: expect true
    _: fail("Expected Uncertain confidence")
```

</details>

### Rule: resource_leak

#### basic detection

#### detects val x = open(...)

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val f = open(\"file.txt\")\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### detects File.open

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val f = File.open(\"path\")\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### detects connect

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val conn = connect(\"localhost:8080\")\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates with block

1. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val f = open(\"file.txt\")\n"
val fixes = check_resource_leak(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("with f = open")
```

</details>

#### no false positives

#### ignores non-resource assignments

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val x = compute(42)\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### ignores var assignments

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "var f = open(\"file\")\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_resource_leak("", "test.spl")
expect fixes.len() == 0
```

</details>

#### has Uncertain confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "val f = open(\"x\")\n"
val fixes = check_resource_leak(source, "test.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Uncertain: expect true
    _: fail("Expected Uncertain confidence")
```

</details>

### Rule: spipe_missing_docstrings

#### basic detection

#### detects describe without docstring

1. expect fixes[0] id contains
2. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"My Feature\":\n    it \"works\":\n        expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
expect fixes[0].id.contains("spipe_missing_docstrings")
expect fixes.len() >= 1
```

</details>

#### detects context without docstring

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    \"\"\"\n    ## X\n    \"\"\"\n    context \"when Y\":\n        it \"works\":\n            expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
# context block should be detected (describe has docstring)
expect fixes.len() >= 1
```

</details>

#### generates docstring template

1. expect rep new text contains
2. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"My Feature\":\n    it \"works\":\n        expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("\"\"\"")
expect rep.new_text.contains("My Feature")
```

</details>

#### no false positives

#### ignores describe with docstring

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    \"\"\"\n    ## X\n    \"\"\"\n    it \"works\":\n        expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### ignores non-spec files

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    pass\n"
val fixes = check_spipe_missing_docstrings(source, "main.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_spipe_missing_docstrings("", "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### has Safe confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    it \"y\":\n        expect true\n"
val fixes = check_spipe_missing_docstrings(source, "test_spec.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Safe: expect true
    _: fail("Expected Safe confidence")
```

</details>

### Rule: spipe_manual_assertions

#### basic detection

#### detects if x: fail()

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x > 5: fail(\"too big\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect fixes.len() == 1
```

</details>

#### detects if not x: fail()

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if not valid: fail(\"invalid\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect fixes.len() == 1
```

</details>

#### generates expect for positive condition

1. expect rep new text contains
2. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x > 5: fail(\"too big\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("expect")
expect rep.new_text.contains("to_be_falsy")
```

</details>

#### generates expect for negated condition

1. expect rep new text contains
2. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if not valid: fail(\"invalid\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("expect(valid)")
expect rep.new_text.contains("to_be_truthy")
```

</details>

#### detects multiple manual assertions

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if a: fail(\"a\")\n    if b: fail(\"b\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect fixes.len() == 2
```

</details>

#### no false positives

#### ignores if without fail

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x > 5: print(x)\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### ignores non-spec files

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x: fail(\"err\")\n"
val fixes = check_spipe_manual_assertions(source, "main.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_spipe_manual_assertions("", "test_spec.spl")
expect fixes.len() == 0
```

</details>

#### has Likely confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    if x: fail(\"y\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Likely: expect true
    _: fail("Expected Likely confidence")
```

</details>

#### preserves indentation

1. expect rep new text starts with


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "        if x: fail(\"y\")\n"
val fixes = check_spipe_manual_assertions(source, "test_spec.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.starts_with("        ")
```

</details>

### Rule: non_exhaustive_match

#### basic detection

#### detects match without case _

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "match x:\n    case 1: \"one\"\n    case 2: \"two\"\nval y = 0\n"
val fixes = check_non_exhaustive_match(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates catch-all arm with todo

1. expect rep new text contains
2. expect rep new text contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "match x:\n    case 1: \"one\"\nval y = 0\n"
val fixes = check_non_exhaustive_match(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text.contains("case _:")
expect rep.new_text.contains("todo(")
```

</details>

#### no false positives

#### ignores match with case _

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "match x:\n    case 1: \"one\"\n    case _: \"other\"\nval y = 0\n"
val fixes = check_non_exhaustive_match(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_non_exhaustive_match("", "test.spl")
expect fixes.len() == 0
```

</details>

#### has Safe confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "match x:\n    case 1: \"one\"\nval y = 0\n"
val fixes = check_non_exhaustive_match(source, "test.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Safe: expect true
    _: fail("Expected Safe confidence")
```

</details>

### Rule: typo_suggestion

#### Levenshtein distance

#### returns 0 for identical strings

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("hello", "hello") == 0
```

</details>

#### returns length for empty string

1. expect levenshtein
2. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("", "abc") == 3
expect levenshtein("abc", "") == 3
```

</details>

#### returns 1 for single insertion

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("helo", "hello") == 1
```

</details>

#### returns 1 for single deletion

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("hello", "helo") == 1
```

</details>

#### returns 1 for single substitution

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("hello", "hallo") == 1
```

</details>

#### returns 2 for two edits

1. expect levenshtein
2. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("kitten", "sitten") == 1
expect levenshtein("kitten", "sittin") == 2
```

</details>

#### handles completely different strings

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("abc", "xyz") == 3
```

</details>

#### handles single character strings

1. expect levenshtein
2. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("a", "b") == 1
expect levenshtein("a", "a") == 0
```

</details>

#### handles both empty

1. expect levenshtein


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect levenshtein("", "") == 0
```

</details>

#### typo fix suggestion

#### suggests close match

1. expect fix id contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known = ["println", "print", "format"]
val result = suggest_typo_fix("test.spl", 1, 1, 0, 5, "prnt", known)
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == "print"
        expect fix.id.contains("typo_suggestion")
    case None:
        expect false
```

</details>

#### returns None for no close match

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known = ["println", "print", "format"]
val result = suggest_typo_fix("test.spl", 1, 1, 0, 10, "xyzxyzxyz", known)
match result:
    case Some(_):
        expect false
    case None:
        expect true
```

</details>

#### has Likely confidence

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known = ["hello"]
val result = suggest_typo_fix("test.spl", 1, 1, 0, 4, "helo", known)
match result:
    case Some(fix):
        match fix.confidence:
            FixConfidence.Likely: expect true
            _: fail("Expected Likely confidence")
    case None:
        expect false
```

</details>

#### picks closest match

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known = ["print", "println", "printf"]
val result = suggest_typo_fix("test.spl", 1, 1, 0, 5, "prnt", known)
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == "print"
    case None:
        expect false
```

</details>

### Rule: parser_contextual_keyword

#### async static reorder

#### detects async static fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates correct reorder

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text == "static async fn "
```

</details>

#### has Safe confidence

1. expect fixes len
2.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() > 0
match fixes[0].confidence:
    FixConfidence.Safe: expect true
    _: fail("Expected Safe confidence")
```

</details>

#### static pub reorder

#### detects static pub fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static pub fn factory():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates pub static fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static pub fn factory():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text == "pub static fn "
```

</details>

#### pub async static reorder

#### detects pub async static fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub async static fn handler():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 1
```

</details>

#### generates pub static async fn

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub async static fn handler():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
val rep = fixes[0].replacements[0]
expect rep.new_text == "pub static async fn "
```

</details>

#### no false positives

#### ignores correct static async fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "static async fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### ignores plain fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn simple():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### ignores pub static fn

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "pub static fn factory():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 0
```

</details>

#### edge cases

#### handles empty file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val fixes = check_parser_contextual_keyword("", "test.spl")
expect fixes.len() == 0
```

</details>

#### handles indented keywords

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    async static fn serve():\n        pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 1
```

</details>

### Rule: type_mismatch_coercion

#### coercion suggestions

#### suggests .to_string() for Int to String

1. expect fix replacements[0] new text == " to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "String", "Int")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == ".to_string()"
    case None:
        expect false
```

</details>

#### suggests .to_string() for Float to String

1. expect fix replacements[0] new text == " to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "String", "Float")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == ".to_string()"
    case None:
        expect false
```

</details>

#### suggests .to_string() for Bool to String

1. expect fix replacements[0] new text == " to string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "String", "Bool")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == ".to_string()"
    case None:
        expect false
```

</details>

#### suggests .to_int() for Float to Int

1. expect fix replacements[0] new text == " to int


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "Int", "Float")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == ".to_int()"
    case None:
        expect false
```

</details>

#### suggests .to_float() for Int to Float

1. expect fix replacements[0] new text == " to float


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "Float", "Int")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == ".to_float()"
    case None:
        expect false
```

</details>

#### suggests != 0 for Int to Bool

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "Bool", "Int")
match result:
    case Some(fix):
        expect fix.replacements[0].new_text == " != 0"
    case None:
        expect false
```

</details>

#### no coercion available

#### returns None for unknown type pair

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "MyType", "OtherType")
match result:
    case Some(_):
        expect false
    case None:
        expect true
```

</details>

#### returns None for same types

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "Int", "Int")
match result:
    case Some(_):
        expect false
    case None:
        expect true
```

</details>

#### fix metadata

#### has Likely confidence

1.  : fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 1, 10, 15, "String", "Int")
match result:
    case Some(fix):
        match fix.confidence:
            FixConfidence.Likely: expect true
            _: fail("Expected Likely confidence")
    case None:
        expect false
```

</details>

#### inserts at correct position

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = suggest_type_coercion_fix("test.spl", 5, 20, 42, "String", "Int")
match result:
    case Some(fix):
        val rep = fix.replacements[0]
        expect rep.start == 42
        expect rep.end == 42
        expect rep.line == 5
    case None:
        expect false
```

</details>

### check_all_rules integration

#### aggregation

#### returns empty for clean file

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn main():\n    val x = 42\n"
val fixes = check_all_rules(source, "main.spl")
expect fixes.len() == 0
```

</details>

#### collects fixes from multiple rules

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_all_rules(source, "test.spl")
# At minimum: parser_contextual_keyword should fire
expect fixes.len() >= 1
```

</details>

#### collects spec-related fixes for spec files

1. expect fixes len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    it \"y\":\n        print(42)\n        if z: fail(\"err\")\n"
val fixes = check_all_rules(source, "test_spec.spl")
# Should get: missing docstring + print_in_test + manual assertion
expect fixes.len() >= 2
```

</details>

#### no duplicates

#### each fix has unique ID

1. expect not ids contains
2. ids push


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "describe \"X\":\n    it \"y\":\n        print(1)\n        print(2)\n"
val fixes = check_all_rules(source, "test_spec.spl")
var ids: List<String> = []
for fix in fixes:
    expect not ids.contains(fix.id)
    ids.push(fix.id)
```

</details>

### Round-trip fix verification

#### parser_contextual_keyword round-trip

#### fixing async static fn clears the warning

1. expect fixes len
2. expect recheck len


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 1

# Apply fix manually
val rep = fixes[0].replacements[0]
val fixed = source.slice(0, rep.start) + rep.new_text + source.slice(rep.end)

# Re-check: should be clean
val recheck = check_parser_contextual_keyword(fixed, "test.spl")
expect recheck.len() == 0
```

</details>

#### print_in_test_spec round-trip

#### fixing print clears the warning

1. expect fixes len
2. expect recheck len


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "    print(42)"
val fixes = check_print_in_test_spec(source, "test_spec.spl")
expect fixes.len() == 1

val rep = fixes[0].replacements[0]
val fixed = source.slice(0, rep.start) + rep.new_text + source.slice(rep.end)

val recheck = check_print_in_test_spec(fixed, "test_spec.spl")
expect recheck.len() == 0
```

</details>

### FixApplicator with shared rules

#### apply rule fixes

#### applies parser keyword fix

1. expect new sources["test spl"] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")

var sources: Dict<String, String> = {}
sources["test.spl"] = source

val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(new_sources):
        expect new_sources["test.spl"].contains("static async fn")
    case Err(e):
        expect false
```

</details>

#### applies multiple rule fixes without conflict

1. expect fixes len
2. expect fixed contains
3. expect fixed contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "async static fn serve():\n    pass\nstatic pub fn make():\n    pass\n"
val fixes = check_parser_contextual_keyword(source, "test.spl")
expect fixes.len() == 2

var sources: Dict<String, String> = {}
sources["test.spl"] = source

val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(new_sources):
        val fixed = new_sources["test.spl"]
        expect fixed.contains("static async fn")
        expect fixed.contains("pub static fn")
    case Err(e):
        expect false
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 100 |
| Active scenarios | 100 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
