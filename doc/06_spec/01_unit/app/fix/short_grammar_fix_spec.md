# Short Grammar Fix Specification

> <details>

<!-- sdn-diagram:id=short_grammar_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=short_grammar_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

short_grammar_fix_spec -> compiler
short_grammar_fix_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=short_grammar_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 66 | 66 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Short Grammar Fix Specification

## Scenarios

### short grammar easy fix

#### rewrites explicit method-call lambda to method reference

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val lengths = words.map(\\w: w.len())\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("&:len")
```

</details>

#### applies method reference replacement in memory

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val lengths = words.map(\\w: w.len())\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
var sources: Dict<text, text> = {}
sources["sample.spl"] = source
val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(updated):
        expect(updated["sample.spl"]).to_contain("words.map(&:len)")
    case Err(e):
        expect(e).to_equal("")
```

</details>

#### rewrites no-arg receiver method expressions to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val adjusted = words.map(\\w: w.len() + 1)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.len() + 1")
```

</details>

#### rewrites arithmetic lambdas to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val doubled = nums.map(\\x: x * 2)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 * 2")
```

</details>

#### rewrites map identity callbacks to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val same = values.map(\\x: x)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1")
```

</details>

#### rewrites then identity callbacks to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val same = promise.then(\\value: value)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1")
```

</details>

#### does not rewrite parenthesized pipe lambdas until parser support exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val tripled = 5 |> (\\x: x * 3)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### rewrites repeated single parameter uses to numbered placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val squares = nums.map(\\x: x * x)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 * _1")
```

</details>

#### does not rewrite bare identity lambdas to a standalone placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val same = atom.swap(\\x: x)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### does not rewrite local lambda value bindings until interpreter support exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val has_error = \\call: call.args.len() > 0 and call.args[0] == \"ERROR\"\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### rewrites ignored lambda parameters to wildcard parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    registry.register(FeatureHandler.of(FeatureId.Halt, rank, \"gdb\", \\args: gdb.halt(), \"halt\"))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\\_: gdb.halt()")
```

</details>

#### rewrites ignored literal transforms to wildcard parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val separators = headers.map(\\h: \"---\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\\_: \"---\"")
```

</details>

#### rewrites predicate lambdas to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val evens = nums.filter(\\x: x % 2 == 0)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 % 2 == 0")
```

</details>

#### rewrites compact predicate lambdas to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val twos = nums.filter(\\x: x==2)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1==2")
```

</details>

#### rewrites compact arithmetic lambdas to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val next = nums.map(\\x: x+1)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1+1")
```

</details>

#### rewrites direct callback argument lambdas to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val missing = set_filter(s, \\x: x == \"Charlie\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 == \"Charlie\"")
```

</details>

#### is registered in all fix rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val trimmed = parts.map(\\p: p.trim())\n"
val fixes = collect_fixes_from_source("sample.spl", source)
var found = false
for fix in fixes:
    val reps = easyfix_replacements(fix)
    if reps.len() > 0 and reps[0].new_text == "&:trim":
        found = true
expect(found).to_equal(true)
```

</details>

#### registers placeholder rewrites in all fix rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val doubled = nums.map(\\x: x * 2)\n"
val fixes = collect_fixes_from_source("sample.spl", source)
var found = false
for fix in fixes:
    val reps = easyfix_replacements(fix)
    if reps.len() > 0 and reps[0].new_text == "_1 * 2":
        found = true
expect(found).to_equal(true)
```

</details>

#### rewrites receiver method predicates to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val evens = values.filter(\\x: x.parse_int() % 2 == 0)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.parse_int() % 2 == 0")
```

</details>

#### rewrites free function predicates to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val evens = values.filter(\\x: int(x) % 2 == 0)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("int(_1) % 2 == 0")
```

</details>

#### rewrites single argument free function transforms to direct function references

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val doubled = values.map(\\x: double(x))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("double")
```

</details>

#### registers free function reference rewrites in all fix rules

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val parsed = values.map(\\x: parse_value(x))\n"
val fixes = collect_fixes_from_source("sample.spl", source)
var found = false
for fix in fixes:
    val reps = easyfix_replacements(fix)
    if reps.len() > 0 and reps[0].new_text == "parse_value":
        found = true
expect(found).to_equal(true)
```

</details>

#### rewrites simple field access transforms to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val names = items.map(\\item: item.name)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.name")
```

</details>

#### rewrites array literal transforms to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val pairs = items.flat_map(\\x: [x, x * 10])\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("[_1, _1 * 10]")
```

</details>

#### rewrites inline if transforms to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val values = items.compact_map(\\x: if x % 2 == 0: x * 10 else: nil)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("if _1 % 2 == 0: _1 * 10 else: nil")
```

</details>

#### rewrites direct field-access predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val stale = rows.filter(\\row: row.violation_type == \"StaleRunning\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.violation_type == \"StaleRunning\"")
```

</details>

#### does not rewrite functional update arrow callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    arr->map(\\x: x * 2)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### does not rewrite lambdas inside multiline docstrings

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val q = "\"\"\""
val source = "fn sample():\n    " + q + "Example:\n        values.map(\\x: x + 1)\n    " + q + "\n    val actual = values.map(\\x: x + 1)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 + 1")
```

</details>

#### rewrites quoted literal comparisons to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val has_json = args.any(\\arg: arg == \"--json\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1 == \"--json\"")
```

</details>

#### rewrites string concatenation transforms to placeholder grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val recovered = p.catch_err(\\e: \"handled: \" + e)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"handled: \" + _1")
```

</details>

#### rewrites ignored result constructor transforms to wildcard parameters

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val mapped = Ok(5).map(\\x: Err(\"bad\"))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\\_: Err(\"bad\")")
```

</details>

#### does not rewrite already-wildcard constant callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val headers = columns.map(\\_: \"---\")\n    val p = Pipeline.new().filter(\\_: true)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### rewrites indexed predicates with param-free index expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val open = rows.filter(\\row: row[self.table.column_index(\"status\")] == status)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1[self.table.column_index(\"status\")] == status")
```

</details>

#### rewrites indexed receiver method predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val names = rows.filter(\\row: row[0].starts_with(\"A\"))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1[0].starts_with(\"A\")")
```

</details>

#### rewrites repeated indexed transform expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val totals = rows.map(\\row: row[\"price\"] * row[\"quantity\"])\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1[\"price\"] * _1[\"quantity\"]")
```

</details>

#### rewrites repeated list argument predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    cond.add_condition(\\args: args.len() > 0 and args[0] == \"GET\", \"retrieve\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.len() > 0 and _1[0] == \"GET\"")
```

</details>

#### rewrites string interpolation transforms to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = bytes.map(\\b: \"" + open + "b" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"" + open + "_1" + close + "\"")
```

</details>

#### rewrites prefixed string interpolation transforms to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = bytes.map(\\b: \"byte:" + open + "b" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"byte:" + open + "_1" + close + "\"")
```

</details>

#### rewrites indexed string interpolation transforms to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = rows.map(\\row: \"first:" + open + "row[0]" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"first:" + open + "_1[0]" + close + "\"")
```

</details>

#### rewrites indexed interpolation callbacks outside map

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    table.register(\"greet\", \\args: \"Hello, " + open + "args[0]" + close + "!\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"Hello, " + open + "_1[0]" + close + "!\"")
```

</details>

#### does not stop string interpolation rewrites at commas inside strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = rows.map(\\row: \"left, right " + open + "row[0]" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"left, right " + open + "_1[0]" + close + "\"")
```

</details>

#### rewrites formatted string interpolation transforms to numbered placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = counts.map(\\count: \"count:" + open + "count:05d" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"count:" + open + "_1:05d" + close + "\"")
```

</details>

#### does not rewrite matching literal text around interpolation placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = counts.map(\\count: \"count=" + open + "count" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"count=" + open + "_1" + close + "\"")
```

</details>

#### does not rewrite escaped interpolation braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = counts.map(\\count: \"" + open + open + "count" + close + close + " " + open + "count" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"" + open + open + "count" + close + close + " " + open + "_1" + close + "\"")
```

</details>

#### does not rewrite interpolation identifiers with matching prefixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val text = counts.map(\\count: \"" + open + "countdown" + close + " " + open + "count" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("\"" + open + "countdown" + close + " " + open + "_1" + close + "\"")
```

</details>

#### does not rewrite match selector lambdas until interpreter support exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val names = values.map(\\value: match value:\n        case 1: \"one\"\n        case _: \"many\"\n    )\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### rewrites receiver calls with param-free explicit arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val values = items.map(\\x: x.adjust(1) + 1)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.adjust(1) + 1")
```

</details>

#### rewrites free function calls with param-free additional arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val values = items.map(\\x: add(x, 1))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("add(_1, 1)")
```

</details>

#### rewrites indexed forwarding call arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample(column: text, predicate: fn(Any) -> bool):\n    self.where(\\row: predicate(row[column]))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("predicate(_1[column])")
```

</details>

#### rewrites field access forwarding call arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    bugs.filter(\\bug: is_open_bug_status(bug.status))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("is_open_bug_status(_1.status)")
```

</details>

#### rewrites method calls where placeholder is not the first argument

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val found = params.any(\\p: self.occurs_check(id, p))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("self.occurs_check(id, _1)")
```

</details>

#### rewrites matcher composition calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample(m1: Matcher, m2: Matcher):\n    Matcher(matches_fn: \\arg: m1.matches(arg) and m2.matches(arg))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("m1.matches(_1) and m2.matches(_1)")
```

</details>

#### rewrites captured forwarding calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample(source: text, file: text):\n    for_each_line(source, \\ctx: _check_short_grammar_line(ctx, file))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_check_short_grammar_line(_1, file)")
```

</details>

#### rewrites callback field receiver forwarding calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    Ok(RemoteExecutionManager.new(read_register_fn: \\reg: self.read_register(reg)))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("self.read_register(_1)")
```

</details>

#### rewrites casted receiver forwarding calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    HardwareReplayController.create(16, \\reg: self.read_register(reg as i64))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("self.read_register(_1 as i64)")
```

</details>

#### rewrites casted function forwarding calls

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample(callback: fn(T) -> ()): \n    val wrapped: fn(Any) -> () = \\v: callback(v as T)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("callback(_1 as T)")
```

</details>

#### rewrites nested call arguments that use the callback parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val result = Promise.resolved(3).then(\\x: Promise.resolved(x + 4))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("Promise.resolved(_1 + 4)")
```

</details>

#### rewrites nested host future callbacks

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val result = HostFuture.ready(5).then(\\x: HostFuture.ready(x + 8))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("HostFuture.ready(_1 + 8)")
```

</details>

#### rewrites nested receiver no-arg method call arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val block = define_block(\"csv\", LexerMode.Raw, \\p: Ok(p.trim()))\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("Ok(_1.trim())")
```

</details>

#### rewrites unary not field predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val local = symbols.filter(\\sym: not sym.is_imported)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("not _1.is_imported")
```

</details>

#### rewrites existence check predicates

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "fn sample():\n    val tags = parts.filter(\\tag: tag.?)\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(1)
val reps = easyfix_replacements(fixes[0])
expect(reps[0].new_text).to_equal("_1.?")
```

</details>

#### does not rewrite tuple parameter interpolation transforms until parser support exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val parts = fields.map(\\(name, value): \"" + open + "name" + close + ": " + open + "value" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### does not rewrite tuple parameter interpolation with calls until parser support exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val open = "{"
val close = "}"
val source = "fn sample():\n    val parts = fields.map(\\(name, pattern): \"" + open + "name" + close + ": " + open + "pattern_to_text(pattern)" + close + "\")\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
expect(fixes.len()).to_equal(0)
```

</details>

#### applies replacements after non-ascii text

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "# unicode before fix — keeps text offsets honest\nfn sample():\n    val values = items.map(\\x: x.trim())\n"
val fixes = check_short_grammar_refactor(source, "sample.spl")
var sources: Dict<text, text> = {}
sources["sample.spl"] = source
val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(updated):
        expect(updated["sample.spl"]).to_contain("items.map(&:trim)")
        expect(updated["sample.spl"]).to_contain("# unicode before fix — keeps text offsets honest")
    case Err(e):
        expect(e).to_equal("")
```

</details>

#### rewrites self get/set accessor calls to field access short grammar

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Box:\n    value: i64\n    fn get_value() -> i64:\n        self.value\n    me set_value(v: i64):\n        self.value = v\n    me bump():\n        self.set_value(self.get_value() + 1)\n"
val fixes = check_field_access_refactor(source, "box.spl")
var sources: Dict<text, text> = {}
sources["box.spl"] = source
val result = FixApplicator.apply(fixes, sources)
match result:
    case Ok(updated):
        expect(updated["box.spl"]).to_contain("self.value = self.value + 1")
    case Err(e):
        expect(e).to_equal("")
```

</details>

#### does not rewrite an expression-context self setter call

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = "class Node:\n    visible: bool\n    me set_visible(v: bool):\n        self.visible = v\n    me build():\n        var n = self.set_visible(false)\n"
val fixes = check_field_access_refactor(source, "node.spl")
expect(fixes.len()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/fix/short_grammar_fix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- short grammar easy fix

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 66 |
| Active scenarios | 66 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
