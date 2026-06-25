# Test Analysis Specification

> <details>

<!-- sdn-diagram:id=test_analysis_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=test_analysis_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

test_analysis_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=test_analysis_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Test Analysis Specification

## Scenarios

### ErrorType Enum

#### converts to string correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorType.ParseError.to_string()).to_equal("parse_error")
expect(ErrorType.SemanticError.to_string()).to_equal("semantic_error")
expect(ErrorType.FileNotFound.to_string()).to_equal("file_not_found")
expect(ErrorType.Timeout.to_string()).to_equal("timeout")
expect(ErrorType.Utf8Error.to_string()).to_equal("utf8_error")
expect(ErrorType.UnknownError.to_string()).to_equal("unknown_error")
```

</details>

#### provides descriptions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(ErrorType.ParseError.description()).to_contain("Syntax")
expect(ErrorType.SemanticError.description()).to_contain("semantic")
expect(ErrorType.FileNotFound.description()).to_contain("not found")
expect(ErrorType.Timeout.description()).to_contain("timeout")
expect(ErrorType.Utf8Error.description()).to_contain("encoding")
expect(ErrorType.UnknownError.description()).to_contain("Unrecognized")
```

</details>

### Error Classification Function

#### when classifying parse errors

#### detects explicit parse error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("parse error: Unexpected token")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### detects unexpected token error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("Unexpected token: expected Fn")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### detects syntax error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("parse error: expected expression, found Default")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### when classifying semantic errors

#### detects function not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("semantic: function `foo` not found")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects method not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("method `bar` not found on type")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects mutability error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("cannot modify self in immutable fn")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects undefined identifier

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("identifier not found: xyz")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### when classifying file errors

#### detects file not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("failed to read: No such file or directory")
expect(result.to_string()).to_equal("file_not_found")
```

</details>

#### detects directory error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("No such file or directory (os error 2)")
expect(result.to_string()).to_equal("file_not_found")
```

</details>

#### when classifying timeout errors

#### detects timeout with 'timed out'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("Test timed out after 30 seconds")
expect(result.to_string()).to_equal("timeout")
```

</details>

#### detects timeout with 'timeout'

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("Execution timeout exceeded")
expect(result.to_string()).to_equal("timeout")
```

</details>

#### when classifying encoding errors

#### detects UTF-8 error

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("stream did not contain valid UTF-8")
expect(result.to_string()).to_equal("utf8_error")
```

</details>

#### when classifying unknown errors

#### returns unknown for unrecognized patterns

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = classify_error("Something completely unexpected")
expect(result.to_string()).to_equal("unknown_error")
```

</details>

### Feature Patterns

#### has parser patterns defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_parser_patterns().len()).to(be_gte(15))
```

</details>

#### has semantic patterns defined

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(get_semantic_patterns().len()).to(be_gte(2))
```

</details>

#### each pattern has required fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
for pattern in get_parser_patterns():
    expect(pattern.pattern.len()).to(be_gt(0))
    expect(pattern.feature.len()).to(be_gt(0))
    expect(pattern.description.len()).to(be_gt(0))

for pattern in get_semantic_patterns():
    expect(pattern.pattern.len()).to(be_gt(0))
    expect(pattern.feature.len()).to(be_gt(0))
    expect(pattern.description.len()).to(be_gt(0))
```

</details>

### Feature Extraction

#### when extracting parser features

#### extracts static fields

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected Fn, found Static")
expect(features).to_contain("static_fields")
```

</details>

#### extracts default parameters

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found Default")
expect(features).to_contain("default_parameters")
```

</details>

#### extracts implicit val/var

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found Assign")
expect(features).to_contain("implicit_val_var")
```

</details>

<details>
<summary>Advanced: extracts matrix multiplication</summary>

#### extracts matrix multiplication

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found At")
expect(features).to_contain("matrix_multiplication")
```

</details>


</details>

#### extracts XOR keyword

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected identifier, found Xor")
expect(features).to_contain("xor_keyword")
```

</details>

#### extracts dict literal syntax

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected Comma, found Colon")
expect(features).to_contain("dict_literal_syntax")
```

</details>

#### extracts val pattern matching

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected pattern, found Val")
expect(features).to_contain("val_pattern_matching")
```

</details>

#### extracts where clause

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected identifier, found Where")
expect(features).to_contain("where_clause")
```

</details>

#### extracts list comprehension

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found For")
expect(features).to_contain("list_comprehension")
```

</details>

#### extracts parallel operator

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found Slash")
expect(features).to_contain("parallel_operator")
```

</details>

#### extracts from pattern

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected pattern, found From")
expect(features).to_contain("from_pattern")
```

</details>

#### extracts return expression

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected expression, found Return")
expect(features).to_contain("return_expression")
```

</details>

#### extracts class var fields

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected Fn, found Var")
expect(features).to_contain("class_var_fields")
```

</details>

#### extracts array literal syntax

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("expected RBracket, found Comma")
expect(features).to_contain("array_literal_syntax")
```

</details>

#### when extracting semantic features

#### extracts string char_at method

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("method `char_at` not found")
expect(features).to_contain("string_char_at_method")
```

</details>

#### extracts mutability checking

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("cannot modify in immutable fn")
expect(features).to_contain("mutability_checking")
```

</details>

#### when extracting multiple features

#### extracts all matching features

1. var features = extract needed features
   - Expected: features.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "expected expression, found Assign and expected Comma, found Colon"
var features = extract_needed_features(error)
expect(features.len()).to_equal(2)
expect(features).to_contain("implicit_val_var")
expect(features).to_contain("dict_literal_syntax")
```

</details>

#### when no features match

#### returns empty list

1. var features = extract needed features
   - Expected: features.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("generic error message")
expect(features.len()).to_equal(0)
```

</details>

### Feature Description Lookup

#### returns description for parser features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = get_feature_description("static_fields")
expect(desc).to_contain("Static")
```

</details>

#### returns description for semantic features

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = get_feature_description("mutability_checking")
expect(desc).to_contain("mutability")
```

</details>

#### returns unknown for invalid feature

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = get_feature_description("nonexistent_feature")
expect(desc).to_equal("Unknown feature")
```

</details>

### TestRecord Structure

#### creates test record with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val record = TestRecord {
    test_id: "1",
    test_name: "test_foo",
    file: "test/foo_spec.spl",
    status: "failed",
    category: "Unit ",
    error_message: "parse error",
    last_run: "2026-01-30T10:00:00Z"
}

expect(record.test_id).to_equal("1")
expect(record.test_name).to_equal("test_foo")
expect(record.status).to_equal("failed")
```

</details>

### Test Database Reading

#### reads valid test database

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "tests |test_id, test_name, file, status, category, error_message, last_run|\n1|t1|f1|failed|Unit |parse error|2026-01-30T10:00:00Z\n2|t2|f2|passed|Unit ||2026-01-30T10:00:00Z"
match read_test_database_simulated(true, content):
    case Ok(records):
        expect(records.len()).to_equal(2)
        expect(records[0].test_name).to_equal("t1")
        expect(records[1].status).to_equal("passed")
    case Err(_):
        expect(true).to_equal(false)
```

</details>

#### handles missing file

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match read_test_database_simulated(false, ""):
    case Ok(_):
        expect(true).to_equal(false)
    case Err(msg):
        expect(msg).to_contain("missing file")
```

</details>

#### handles invalid SDN format

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match read_test_database_simulated(true, "bad row"):
    case Ok(_):
        expect(true).to_equal(false)
    case Err(msg):
        expect(msg).to_contain("invalid")
```

</details>

### Failed Test Filtering

#### filters only failed tests

1. var failed = get failed tests
   - Expected: failed.len() equals `2`
   - Expected: failed[0].test_name equals `t1`
   - Expected: failed[1].test_name equals `t3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "failed", category: "Unit ", error_message: "err1", last_run: "" },
    TestRecord { test_id: "2", test_name: "t2", file: "f2", status: "passed", category: "Unit ", error_message: "", last_run: "" },
    TestRecord { test_id: "3", test_name: "t3", file: "f3", status: "failed", category: "Unit ", error_message: "err3", last_run: "" },
    TestRecord { test_id: "4", test_name: "t4", file: "f4", status: "skipped", category: "Unit ", error_message: "", last_run: "" }
]

var failed = get_failed_tests(records)
expect(failed.len()).to_equal(2)
expect(failed[0].test_name).to_equal("t1")
expect(failed[1].test_name).to_equal("t3")
```

</details>

#### returns empty list when no failures

1. var failed = get failed tests
   - Expected: failed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "passed", category: "Unit ", error_message: "", last_run: "" }
]

var failed = get_failed_tests(records)
expect(failed.len()).to_equal(0)
```

</details>

### Failure Statistics

#### creates failure stats with all fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = FailureStats.new(
    2,
    [CountEntry { name: "parse_error", count: 1 }],
    [CountEntry { name: "implicit_val_var", count: 2 }]
)
expect(stats.total_failed).to_equal(2)
expect(stats.error_count("parse_error")).to_equal(1)
expect(stats.feature_count("implicit_val_var")).to_equal(2)
```

</details>

### Failure Analysis Function

#### analyzes test records correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "failed", category: "Unit ", error_message: "parse error: expected expression, found Assign", last_run: "" },
    TestRecord { test_id: "2", test_name: "t2", file: "f2", status: "failed", category: "Unit ", error_message: "method `char_at` not found", last_run: "" },
    TestRecord { test_id: "3", test_name: "t3", file: "f3", status: "passed", category: "Unit ", error_message: "", last_run: "" }
]
val stats = analyze_failures_local(records)
expect(stats.total_failed).to_equal(2)
expect(stats.error_count("parse_error")).to_equal(1)
expect(stats.error_count("semantic_error")).to_equal(1)
expect(stats.feature_count("implicit_val_var")).to_equal(1)
expect(stats.feature_count("string_char_at_method")).to_equal(1)
```

</details>

#### handles empty record list

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stats = analyze_failures_local([])
expect(stats.total_failed).to_equal(0)
expect(stats.error_count("parse_error")).to_equal(0)
```

</details>

#### counts multiple features from same error

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "failed", category: "Unit ", error_message: "expected expression, found Assign and expected Comma, found Colon", last_run: "" }
]
val stats = analyze_failures_local(records)
expect(stats.feature_count("implicit_val_var")).to_equal(1)
expect(stats.feature_count("dict_literal_syntax")).to_equal(1)
```

</details>

### End-to-End Workflow

#### performs full analysis on test database

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val content = "tests |test_id, test_name, file, status, category, error_message, last_run|\n1|t1|f1|failed|Unit |parse error: Unexpected token|2026-01-30T10:00:00Z\n2|t2|f2|failed|System|cannot modify self in immutable fn|2026-01-30T10:00:00Z\n3|t3|f3|passed|Unit ||2026-01-30T10:00:00Z"
match read_test_database_simulated(true, content):
    case Ok(records):
        val stats = analyze_failures_local(records)
        expect(stats.total_failed).to_equal(2)
        expect(stats.error_count("parse_error")).to_equal(1)
        expect(stats.error_count("semantic_error")).to_equal(1)
    case Err(_):
        expect(true).to_equal(false)
```

</details>

#### filters tests by category

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "failed", category: "Unit ", error_message: "error1", last_run: "" },
    TestRecord { test_id: "2", test_name: "t2", file: "f2", status: "failed", category: "System", error_message: "error2", last_run: "" },
    TestRecord { test_id: "3", test_name: "t3", file: "f3", status: "failed", category: "Unit ", error_message: "error3", last_run: "" }
]

# Count Unit category failures
var unit_count = 0
for record in records:
    if record.status == "failed" and record.category == "Unit ":
        unit_count = unit_count + 1

expect(unit_count).to_equal(2)
```

</details>

### Edge Cases

#### when handling empty data

#### handles empty error message

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error_type = classify_error("")
expect(error_type.to_string()).to_equal("unknown_error")
```

</details>

#### handles empty feature extraction

1. var features = extract needed features
   - Expected: features.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var features = extract_needed_features("")
expect(features.len()).to_equal(0)
```

</details>

#### when handling very long messages

#### classifies long error messages

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val long_error = "parse error: " + "x".repeat(1000)
val error_type = classify_error(long_error)
expect(error_type.to_string()).to_equal("parse_error")
```

</details>

#### when handling special characters

#### handles error with quotes

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "parse error: expected '|' found '&'"
val error_type = classify_error(error)
expect(error_type.to_string()).to_equal("parse_error")
```

</details>

#### handles error with newlines

1. var features = extract needed features


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val error = "parse error\nexpected Fn\nfound Static"
var features = extract_needed_features(error)
expect(features).to_contain("static_fields")
```

</details>

### Performance Characteristics

#### handles many test records efficiently

1. records push
   - Expected: stats.total_failed equals `20`
   - Expected: stats.error_count("parse_error") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var records = []
var i: i64 = 0
while i < 20:
    records.push(TestRecord { test_id: i.to_string(), test_name: "t{i}", file: "f{i}", status: "failed", category: "Unit ", error_message: "parse error: expected Fn, found Static", last_run: "" })
    i = i + 1
val stats = analyze_failures_local(records)
expect(stats.total_failed).to_equal(20)
expect(stats.error_count("parse_error")).to_equal(20)
```

</details>

#### handles many unique features

<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "failed", category: "Unit ", error_message: "expected Fn, found Static", last_run: "" },
    TestRecord { test_id: "2", test_name: "t2", file: "f2", status: "failed", category: "Unit ", error_message: "expected expression, found Default", last_run: "" },
    TestRecord { test_id: "3", test_name: "t3", file: "f3", status: "failed", category: "Unit ", error_message: "expected expression, found Assign", last_run: "" },
    TestRecord { test_id: "4", test_name: "t4", file: "f4", status: "failed", category: "Unit ", error_message: "expected Comma, found Colon", last_run: "" },
    TestRecord { test_id: "5", test_name: "t5", file: "f5", status: "failed", category: "Unit ", error_message: "method `char_at` not found", last_run: "" }
]
val stats = analyze_failures_local(records)
expect(stats.total_failed).to_equal(5)
expect(stats.feature_count("static_fields")).to_equal(1)
expect(stats.feature_count("default_parameters")).to_equal(1)
expect(stats.feature_count("implicit_val_var")).to_equal(1)
expect(stats.feature_count("dict_literal_syntax")).to_equal(1)
expect(stats.feature_count("string_char_at_method")).to_equal(1)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/test_analysis_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- ErrorType Enum
- Error Classification Function
- Feature Patterns
- Feature Extraction
- Feature Description Lookup
- TestRecord Structure
- Test Database Reading
- Failed Test Filtering
- Failure Statistics
- Failure Analysis Function
- End-to-End Workflow
- Edge Cases
- Performance Characteristics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
