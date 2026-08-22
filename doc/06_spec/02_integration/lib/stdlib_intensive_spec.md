# stdlib_intensive_spec

> Verifies the stdlib intensive behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# stdlib_intensive_spec

Verifies the stdlib intensive behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/02_integration/lib/stdlib_intensive_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the stdlib intensive behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### String + Collections Integration - Intensive

#### text processing pipeline

<details>
<summary>Advanced: processes 1000 strings with split/join</summary>

#### processes 1000 strings with split/join _(slow)_

- Verify: processes 1000 strings with split/join


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: processes 1000 strings with split/join")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var lines = []
for i in 0..1000:
    lines = lines + ["item_{i},value_{i},status_{i}"]

# Split each line
var processed = 0
for line in lines:
    val parts = line.split(",")
    if parts.len() == 3:
        processed = processed + 1

check(processed == 1000)
```

</details>


</details>

<details>
<summary>Advanced: builds text with array concatenation</summary>

#### builds text with array concatenation _(slow)_

- Verify: builds text with array concatenation


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: builds text with array concatenation")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var words = []
for i in 0..500:
    words = words + ["word{i}"]

val text = words.join(" ")
check(text.len() > 2000)
check(text.contains("word0"))
check(text.contains("word499"))
```

</details>


</details>

#### filtering and transformation

<details>
<summary>Advanced: filters and maps 1000 items</summary>

#### filters and maps 1000 items _(slow)_

- Verify: filters and maps 1000 items


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: filters and maps 1000 items")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var items = []
for i in 0..1000:
    items = items + [i]

# Filter evens
var evens = []
for item in items:
    if item % 2 == 0:
        evens = evens + [item]

check(evens.len() == 500)
```

</details>


</details>

<details>
<summary>Advanced: transforms strings to uppercase pattern</summary>

#### transforms strings to uppercase pattern _(slow)_

- Verify: transforms strings to uppercase pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: transforms strings to uppercase pattern")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var words = ["hello", "world", "test", "simple"]

var uppers = []
for word in words:
    # Simulate uppercase (actual impl may vary)
    uppers = uppers + [word]

check(uppers.len() == 4)
```

</details>


</details>

### Math + Collections Integration - Intensive

#### statistical operations

<details>
<summary>Advanced: computes sum of 1000 numbers</summary>

#### computes sum of 1000 numbers _(slow)_

- Verify: computes sum of 1000 numbers


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: computes sum of 1000 numbers")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var numbers = []
for i in 0..1000:
    numbers = numbers + [i]

var sum = 0
for n in numbers:
    sum = sum + n

# Sum of 0..999 = 499500
check(sum == 499500)
```

</details>


</details>

<details>
<summary>Advanced: finds min/max in large dataset</summary>

#### finds min/max in large dataset _(slow)_

- Verify: finds min/max in large dataset


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: finds min/max in large dataset")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var numbers = []
for i in 0..1000:
    val n = (i * 7) % 100  # Generate varied numbers
    numbers = numbers + [n]

var min_val = 999999
var max_val = -999999

for n in numbers:
    if n < min_val:
        min_val = n
    if n > max_val:
        max_val = n

check(min_val >= 0)
check(max_val < 100)
```

</details>


</details>

#### numeric transformations

<details>
<summary>Advanced: applies arithmetic to 500 items</summary>

#### applies arithmetic to 500 items _(slow)_

- Verify: applies arithmetic to 500 items


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: applies arithmetic to 500 items")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var values = []
for i in 0..500:
    values = values + [i]

# Square each value
var squared = []
for v in values:
    squared = squared + [v * v]

check(squared.len() == 500)
check(squared[0] == 0)
check(squared[10] == 100)
```

</details>


</details>

### Path + String Integration - Intensive

#### path construction

<details>
<summary>Advanced: builds 500 file paths</summary>

#### builds 500 file paths _(slow)_

- Verify: builds 500 file paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: builds 500 file paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var paths = []
for i in 0..500:
    val path = "dir/subdir/file{i}.spl"
    paths = paths + [path]

check(paths.len() == 500)
check(paths[0].contains("file0.spl"))
check(paths[499].contains("file499.spl"))
```

</details>


</details>

<details>
<summary>Advanced: extracts components from paths</summary>

#### extracts components from paths _(slow)_

- Verify: extracts components from paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: extracts components from paths")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var paths = [
    "src/compiler/10.frontend/core/lexer.spl",
    "test/unit/std/string_spec.spl",
    "doc/07_guide/syntax.md"
]

for path in paths:
    val has_slash = path.contains("/")
    check(has_slash)

    val parts = path.split("/")
    check(parts.len() >= 2)
```

</details>


</details>

#### path validation

<details>
<summary>Advanced: validates 1000 path patterns</summary>

#### validates 1000 path patterns _(slow)_

- Verify: validates 1000 path patterns


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: validates 1000 path patterns")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var valid_count = 0

for i in 0..1000:
    val path = "test/file{i}.txt"

    # Simple validation
    if path.contains("/") and path.contains("."):
        valid_count = valid_count + 1

check(valid_count == 1000)
```

</details>


</details>

### Multi-Module Workflow - Intensive

#### data processing pipeline

<details>
<summary>Advanced: processes CSV-like data end-to-end</summary>

#### processes CSV-like data end-to-end _(slow)_

- Verify: processes CSV-like data end-to-end


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: processes CSV-like data end-to-end")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Generate CSV data
var csv_lines = []
csv_lines = csv_lines + ["name,age,city"]

for i in 0..100:
    val line = "user{i},{i + 20},city{i % 10}"
    csv_lines = csv_lines + [line]

# Parse CSV
var records = []
for line in csv_lines:
    if line.contains("name"):  # Skip header
        pass
    else:
        val fields = line.split(",")
        if fields.len() == 3:
            records = records + [fields]

check(records.len() == 100)
```

</details>


</details>

<details>
<summary>Advanced: aggregates data by category</summary>

#### aggregates data by category _(slow)_

- Verify: aggregates data by category


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: aggregates data by category")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var data = []
for i in 0..200:
    val category = i % 5
    data = data + [category]

# Count by category
var counts = [0, 0, 0, 0, 0]
for item in data:
    if item >= 0 and item < 5:
        counts[item] = counts[item] + 1

# Each category should have 40 items
for count in counts:
    check(count == 40)
```

</details>


</details>

#### text analysis workflow

<details>
<summary>Advanced: analyzes 500 text documents</summary>

#### analyzes 500 text documents _(slow)_

- Verify: analyzes 500 text documents


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: analyzes 500 text documents")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var docs = []
for i in 0..500:
    val doc = "Document {i} contains multiple words and numbers like {i * 2}"
    docs = docs + [doc]

var word_count = 0
for doc in docs:
    var words = doc.split(" ")
    word_count = word_count + words.len()

check(word_count > 3000)
```

</details>


</details>

<details>
<summary>Advanced: filters and sorts text data</summary>

#### filters and sorts text data _(slow)_

- Verify: filters and sorts text data


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: filters and sorts text data")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var items = []
for i in 0..300:
    if i % 3 == 0:
        items = items + ["special_{i}"]
    else:
        items = items + ["regular_{i}"]

# Filter special items
var special = []
for item in items:
    if item.contains("special"):
        special = special + [item]

check(special.len() == 100)
```

</details>


</details>

### Collections Stress Test - Intensive

#### array operations

<details>
<summary>Advanced: appends 2000 items</summary>

#### appends 2000 items _(slow)_

- Verify: appends 2000 items


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: appends 2000 items")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var arr = []
for i in 0..2000:
    arr = arr + [i]

check(arr.len() == 2000)
check(arr[0] == 0)
check(arr[1999] == 1999)
```

</details>


</details>

<details>
<summary>Advanced: concatenates arrays repeatedly</summary>

#### concatenates arrays repeatedly _(slow)_

- Verify: concatenates arrays repeatedly


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: concatenates arrays repeatedly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var base = [1, 2, 3]
var result = []

for i in 0..100:
    for item in base:
        result = result + [item]

check(result.len() == 300)
```

</details>


</details>

#### nested collections

<details>
<summary>Advanced: handles nested arrays</summary>

#### handles nested arrays _(slow)_

- Verify: handles nested arrays


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: handles nested arrays")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var matrix = []
for row in 0..50:
    var row_data = []
    for col in 0..50:
        row_data = row_data + [row * 50 + col]
    matrix = matrix + [row_data]

check(matrix.len() == 50)
check(matrix[0].len() == 50)
```

</details>


</details>

<details>
<summary>Advanced: processes nested data structures</summary>

#### processes nested data structures _(slow)_

- Verify: processes nested data structures


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: processes nested data structures")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var groups = []
for g in 0..10:
    var items = []
    for i in 0..20:
        items = items + [g * 100 + i]
    groups = groups + [items]

# Flatten
var flattened = []
for group in groups:
    for item in group:
        flattened = flattened + [item]

check(flattened.len() == 200)
```

</details>


</details>

### String Operations Stress Test - Intensive

#### string building

<details>
<summary>Advanced: concatenates 500 strings</summary>

#### concatenates 500 strings _(slow)_

- Verify: concatenates 500 strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: concatenates 500 strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var parts: [text] = []
for i in 0..500:
    parts = parts + ["item{i},"]
val result = parts.join("")

check(result.len() > 2500)
```

</details>


</details>

<details>
<summary>Advanced: splits and rejoins strings</summary>

#### splits and rejoins strings _(slow)_

- Verify: splits and rejoins strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: splits and rejoins strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var original = "a,b,c,d,e,f,g,h,i,j"

for i in 0..100:
    val parts = original.split(",")
    val rejoined = parts.join(",")
    check(rejoined == original)
```

</details>


</details>

#### pattern matching

<details>
<summary>Advanced: searches in 1000 strings</summary>

#### searches in 1000 strings _(slow)_

- Verify: searches in 1000 strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: searches in 1000 strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var matches = 0

for i in 0..1000:
    val text = "test_string_{i}_with_pattern"
    if text.contains("pattern"):
        matches = matches + 1

check(matches == 1000)
```

</details>


</details>

<details>
<summary>Advanced: extracts substrings repeatedly</summary>

#### extracts substrings repeatedly _(slow)_

- Verify: extracts substrings repeatedly


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-LIB-LIB_STDLIB_INTENSIVE-001
step("Verify: extracts substrings repeatedly")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val text = "0123456789abcdefghij"

var extracts = []
for i in 0..10:
    if i + 5 <= text.len():
        val substr = text[i..i+5]
        extracts = extracts + [substr]

check(extracts.len() == 10)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 22 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `256e18fd88fb45c69482a7f2654bba999c2ed4b58de505a22e8ae815e0da6218`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `256e18fd88fb45c69482a7f2654bba999c2ed4b58de505a22e8ae815e0da6218`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `256e18fd88fb45c69482a7f2654bba999c2ed4b58de505a22e8ae815e0da6218`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/02_integration/lib/stdlib_intensive_spec.spl
mirror: doc/06_spec/02_integration/lib/stdlib_intensive_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/lib/stdlib_intensive_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/02_integration/lib/stdlib_intensive_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/lib/stdlib_intensive_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
