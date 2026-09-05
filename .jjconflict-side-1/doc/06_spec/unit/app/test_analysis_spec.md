# test_analysis_spec

> Purpose: Prove that ErrorType Enum.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 58 | 58 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# test_analysis_spec

Purpose: Prove that ErrorType Enum.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/test_analysis_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that ErrorType Enum.
Audience: APP maintainers who read this spec to confirm the behavior still holds.

## Scenarios

### ErrorType Enum

#### converts to string correctly

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- converts to string correctly
- Verify: converts to string correctly
   - Expected: ErrorType.ParseError.to_string() equals `parse_error`
   - Expected: ErrorType.SemanticError.to_string() equals `semantic_error`
   - Expected: ErrorType.FileNotFound.to_string() equals `file_not_found`
   - Expected: ErrorType.Timeout.to_string() equals `timeout`
   - Expected: ErrorType.Utf8Error.to_string() equals `utf8_error`
   - Expected: ErrorType.UnknownError.to_string() equals `unknown_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("converts to string correctly")
step("Verify: converts to string correctly")
# @req: REQ-APP-ERRORTYPE-ENUM-001
expect(ErrorType.ParseError.to_string()).to_equal("parse_error")
expect(ErrorType.SemanticError.to_string()).to_equal("semantic_error")
expect(ErrorType.FileNotFound.to_string()).to_equal("file_not_found")
expect(ErrorType.Timeout.to_string()).to_equal("timeout")
expect(ErrorType.Utf8Error.to_string()).to_equal("utf8_error")
expect(ErrorType.UnknownError.to_string()).to_equal("unknown_error")
```

</details>

#### provides descriptions

- provides descriptions
- Verify: provides descriptions


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides descriptions")
step("Verify: provides descriptions")
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

- detects explicit parse error
- Verify: detects explicit parse error
   - Expected: result.to_string() equals `parse_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects explicit parse error")
step("Verify: detects explicit parse error")
val result = classify_error("parse error: Unexpected token")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### detects unexpected token error

- detects unexpected token error
- Verify: detects unexpected token error
   - Expected: result.to_string() equals `parse_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects unexpected token error")
step("Verify: detects unexpected token error")
val result = classify_error("Unexpected token: expected Fn")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### detects syntax error

- detects syntax error
- Verify: detects syntax error
   - Expected: result.to_string() equals `parse_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects syntax error")
step("Verify: detects syntax error")
val result = classify_error("parse error: expected expression, found Default")
expect(result.to_string()).to_equal("parse_error")
```

</details>

#### when classifying semantic errors

#### detects function not found

- detects function not found
- Verify: detects function not found
   - Expected: result.to_string() equals `semantic_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects function not found")
step("Verify: detects function not found")
val result = classify_error("semantic: function `foo` not found")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects method not found

- detects method not found
- Verify: detects method not found
   - Expected: result.to_string() equals `semantic_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects method not found")
step("Verify: detects method not found")
val result = classify_error("method `bar` not found on type")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects mutability error

- detects mutability error
- Verify: detects mutability error
   - Expected: result.to_string() equals `semantic_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects mutability error")
step("Verify: detects mutability error")
val result = classify_error("cannot modify self in immutable fn")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### detects undefined identifier

- detects undefined identifier
- Verify: detects undefined identifier
   - Expected: result.to_string() equals `semantic_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects undefined identifier")
step("Verify: detects undefined identifier")
val result = classify_error("identifier not found: xyz")
expect(result.to_string()).to_equal("semantic_error")
```

</details>

#### when classifying file errors

#### detects file not found

- detects file not found
- Verify: detects file not found
   - Expected: result.to_string() equals `file_not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects file not found")
step("Verify: detects file not found")
val result = classify_error("failed to read: No such file or directory")
expect(result.to_string()).to_equal("file_not_found")
```

</details>

#### detects directory error

- detects directory error
- Verify: detects directory error
   - Expected: result.to_string() equals `file_not_found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects directory error")
step("Verify: detects directory error")
val result = classify_error("No such file or directory (os error 2)")
expect(result.to_string()).to_equal("file_not_found")
```

</details>

#### when classifying timeout errors

#### detects timeout with 'timed out'

- detects timeout with 'timed out'
- Verify: detects timeout with 'timed out'
   - Expected: result.to_string() equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects timeout with 'timed out'")
step("Verify: detects timeout with 'timed out'")
val result = classify_error("Test timed out after 30 seconds")
expect(result.to_string()).to_equal("timeout")
```

</details>

#### detects timeout with 'timeout'

- detects timeout with 'timeout'
- Verify: detects timeout with 'timeout'
   - Expected: result.to_string() equals `timeout`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects timeout with 'timeout'")
step("Verify: detects timeout with 'timeout'")
val result = classify_error("Execution timeout exceeded")
expect(result.to_string()).to_equal("timeout")
```

</details>

#### when classifying encoding errors

#### detects UTF-8 error

- detects UTF-8 error
- Verify: detects UTF-8 error
   - Expected: result.to_string() equals `utf8_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects UTF-8 error")
step("Verify: detects UTF-8 error")
val result = classify_error("stream did not contain valid UTF-8")
expect(result.to_string()).to_equal("utf8_error")
```

</details>

#### when classifying unknown errors

#### returns unknown for unrecognized patterns

- returns unknown for unrecognized patterns
- Verify: returns unknown for unrecognized patterns
   - Expected: result.to_string() equals `unknown_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for unrecognized patterns")
step("Verify: returns unknown for unrecognized patterns")
val result = classify_error("Something completely unexpected")
expect(result.to_string()).to_equal("unknown_error")
```

</details>

### Feature Patterns

#### has parser patterns defined

- has parser patterns defined
- Verify: has parser patterns defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has parser patterns defined")
step("Verify: has parser patterns defined")
expect(get_parser_patterns().len()).to(be_gte(15))
```

</details>

#### has semantic patterns defined

- has semantic patterns defined
- Verify: has semantic patterns defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has semantic patterns defined")
step("Verify: has semantic patterns defined")
expect(get_semantic_patterns().len()).to(be_gte(2))
```

</details>

#### each pattern has required fields

- each pattern has required fields
- Verify: each pattern has required fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("each pattern has required fields")
step("Verify: each pattern has required fields")
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

- extracts static fields
- Verify: extracts static fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts static fields")
step("Verify: extracts static fields")
var features = extract_needed_features("expected Fn, found Static")
expect(features).to_contain("static_fields")
```

</details>

#### extracts default parameters

- extracts default parameters
- Verify: extracts default parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts default parameters")
step("Verify: extracts default parameters")
var features = extract_needed_features("expected expression, found Default")
expect(features).to_contain("default_parameters")
```

</details>

#### extracts implicit val/var

- extracts implicit val/var
- Verify: extracts implicit val/var


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts implicit val/var")
step("Verify: extracts implicit val/var")
var features = extract_needed_features("expected expression, found Assign")
expect(features).to_contain("implicit_val_var")
```

</details>

<details>
<summary>Advanced: extracts matrix multiplication</summary>

#### extracts matrix multiplication

- extracts matrix multiplication
- Verify: extracts matrix multiplication


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts matrix multiplication")
step("Verify: extracts matrix multiplication")
var features = extract_needed_features("expected expression, found At")
expect(features).to_contain("matrix_multiplication")
```

</details>


</details>

#### extracts XOR keyword

- extracts XOR keyword
- Verify: extracts XOR keyword


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts XOR keyword")
step("Verify: extracts XOR keyword")
var features = extract_needed_features("expected identifier, found Xor")
expect(features).to_contain("xor_keyword")
```

</details>

#### extracts dict literal syntax

- extracts dict literal syntax
- Verify: extracts dict literal syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts dict literal syntax")
step("Verify: extracts dict literal syntax")
var features = extract_needed_features("expected Comma, found Colon")
expect(features).to_contain("dict_literal_syntax")
```

</details>

#### extracts val pattern matching

- extracts val pattern matching
- Verify: extracts val pattern matching


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts val pattern matching")
step("Verify: extracts val pattern matching")
var features = extract_needed_features("expected pattern, found Val")
expect(features).to_contain("val_pattern_matching")
```

</details>

#### extracts where clause

- extracts where clause
- Verify: extracts where clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts where clause")
step("Verify: extracts where clause")
var features = extract_needed_features("expected identifier, found Where")
expect(features).to_contain("where_clause")
```

</details>

#### extracts list comprehension

- extracts list comprehension
- Verify: extracts list comprehension


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts list comprehension")
step("Verify: extracts list comprehension")
var features = extract_needed_features("expected expression, found For")
expect(features).to_contain("list_comprehension")
```

</details>

#### extracts parallel operator

- extracts parallel operator
- Verify: extracts parallel operator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts parallel operator")
step("Verify: extracts parallel operator")
var features = extract_needed_features("expected expression, found Slash")
expect(features).to_contain("parallel_operator")
```

</details>

#### extracts from pattern

- extracts from pattern
- Verify: extracts from pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts from pattern")
step("Verify: extracts from pattern")
var features = extract_needed_features("expected pattern, found From")
expect(features).to_contain("from_pattern")
```

</details>

#### extracts return expression

- extracts return expression
- Verify: extracts return expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts return expression")
step("Verify: extracts return expression")
var features = extract_needed_features("expected expression, found Return")
expect(features).to_contain("return_expression")
```

</details>

#### extracts class var fields

- extracts class var fields
- Verify: extracts class var fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts class var fields")
step("Verify: extracts class var fields")
var features = extract_needed_features("expected Fn, found Var")
expect(features).to_contain("class_var_fields")
```

</details>

#### extracts array literal syntax

- extracts array literal syntax
- Verify: extracts array literal syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts array literal syntax")
step("Verify: extracts array literal syntax")
var features = extract_needed_features("expected RBracket, found Comma")
expect(features).to_contain("array_literal_syntax")
```

</details>

#### when extracting semantic features

#### extracts string char_at method

- extracts string char_at method
- Verify: extracts string char_at method


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts string char_at method")
step("Verify: extracts string char_at method")
var features = extract_needed_features("method `char_at` not found")
expect(features).to_contain("string_char_at_method")
```

</details>

#### extracts mutability checking

- extracts mutability checking
- Verify: extracts mutability checking


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts mutability checking")
step("Verify: extracts mutability checking")
var features = extract_needed_features("cannot modify in immutable fn")
expect(features).to_contain("mutability_checking")
```

</details>

#### when extracting multiple features

#### extracts all matching features

- extracts all matching features
- Verify: extracts all matching features
   - Expected: features.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts all matching features")
step("Verify: extracts all matching features")
val error = "expected expression, found Assign and expected Comma, found Colon"
var features = extract_needed_features(error)
expect(features.len()).to_equal(2)
expect(features).to_contain("implicit_val_var")
expect(features).to_contain("dict_literal_syntax")
```

</details>

#### when no features match

#### returns empty list

- returns empty list
- Verify: returns empty list
   - Expected: features.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list")
step("Verify: returns empty list")
var features = extract_needed_features("generic error message")
expect(features.len()).to_equal(0)
```

</details>

### Feature Description Lookup

#### returns description for parser features

- returns description for parser features
- Verify: returns description for parser features


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns description for parser features")
step("Verify: returns description for parser features")
val desc = get_feature_description("static_fields")
expect(desc).to_contain("Static")
```

</details>

#### returns description for semantic features

- returns description for semantic features
- Verify: returns description for semantic features


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns description for semantic features")
step("Verify: returns description for semantic features")
val desc = get_feature_description("mutability_checking")
expect(desc).to_contain("mutability")
```

</details>

#### returns unknown for invalid feature

- returns unknown for invalid feature
- Verify: returns unknown for invalid feature
   - Expected: desc equals `Unknown feature`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns unknown for invalid feature")
step("Verify: returns unknown for invalid feature")
val desc = get_feature_description("nonexistent_feature")
expect(desc).to_equal("Unknown feature")
```

</details>

### TestRecord Structure

#### creates test record with all fields

- creates test record with all fields
- Verify: creates test record with all fields
   - Expected: record.test_id equals `1`
   - Expected: record.test_name equals `test_foo`
   - Expected: record.status equals `failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates test record with all fields")
step("Verify: creates test record with all fields")
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

- reads valid test database
- Verify: reads valid test database
   - Expected: records.len() equals `2`
   - Expected: records[0].test_name equals `t1`
   - Expected: records[1].status equals `passed`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads valid test database")
step("Verify: reads valid test database")
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

- handles missing file
- Verify: handles missing file
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles missing file")
step("Verify: handles missing file")
match read_test_database_simulated(false, ""):
    case Ok(_):
        expect(true).to_equal(false)
    case Err(msg):
        expect(msg).to_contain("missing file")
```

</details>

#### handles invalid SDN format

- handles invalid SDN format
- Verify: handles invalid SDN format
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles invalid SDN format")
step("Verify: handles invalid SDN format")
match read_test_database_simulated(true, "bad row"):
    case Ok(_):
        expect(true).to_equal(false)
    case Err(msg):
        expect(msg).to_contain("invalid")
```

</details>

### Failed Test Filtering

#### filters only failed tests

- filters only failed tests
- Verify: filters only failed tests
   - Expected: failed.len() equals `2`
   - Expected: failed[0].test_name equals `t1`
   - Expected: failed[1].test_name equals `t3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters only failed tests")
step("Verify: filters only failed tests")
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

- returns empty list when no failures
- Verify: returns empty list when no failures
   - Expected: failed.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns empty list when no failures")
step("Verify: returns empty list when no failures")
val records = [
    TestRecord { test_id: "1", test_name: "t1", file: "f1", status: "passed", category: "Unit ", error_message: "", last_run: "" }
]

var failed = get_failed_tests(records)
expect(failed.len()).to_equal(0)
```

</details>

### Failure Statistics

#### creates failure stats with all fields

- creates failure stats with all fields
- Verify: creates failure stats with all fields
   - Expected: stats.total_failed equals `2`
   - Expected: stats.error_count("parse_error") equals `1`
   - Expected: stats.feature_count("implicit_val_var") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates failure stats with all fields")
step("Verify: creates failure stats with all fields")
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

- analyzes test records correctly
- Verify: analyzes test records correctly
   - Expected: stats.total_failed equals `2`
   - Expected: stats.error_count("parse_error") equals `1`
   - Expected: stats.error_count("semantic_error") equals `1`
   - Expected: stats.feature_count("implicit_val_var") equals `1`
   - Expected: stats.feature_count("string_char_at_method") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("analyzes test records correctly")
step("Verify: analyzes test records correctly")
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

- handles empty record list
- Verify: handles empty record list
   - Expected: stats.total_failed equals `0`
   - Expected: stats.error_count("parse_error") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty record list")
step("Verify: handles empty record list")
val stats = analyze_failures_local([])
expect(stats.total_failed).to_equal(0)
expect(stats.error_count("parse_error")).to_equal(0)
```

</details>

#### counts multiple features from same error

- counts multiple features from same error
- Verify: counts multiple features from same error
   - Expected: stats.feature_count("implicit_val_var") equals `1`
   - Expected: stats.feature_count("dict_literal_syntax") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("counts multiple features from same error")
step("Verify: counts multiple features from same error")
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

- performs full analysis on test database
- Verify: performs full analysis on test database
   - Expected: stats.total_failed equals `2`
   - Expected: stats.error_count("parse_error") equals `1`
   - Expected: stats.error_count("semantic_error") equals `1`
   - Expected: true is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("performs full analysis on test database")
step("Verify: performs full analysis on test database")
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

- filters tests by category
- Verify: filters tests by category
   - Expected: unit_count equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("filters tests by category")
step("Verify: filters tests by category")
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

- handles empty error message
- Verify: handles empty error message
   - Expected: error_type.to_string() equals `unknown_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty error message")
step("Verify: handles empty error message")
val error_type = classify_error("")
expect(error_type.to_string()).to_equal("unknown_error")
```

</details>

#### handles empty feature extraction

- handles empty feature extraction
- Verify: handles empty feature extraction
   - Expected: features.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty feature extraction")
step("Verify: handles empty feature extraction")
var features = extract_needed_features("")
expect(features.len()).to_equal(0)
```

</details>

#### when handling very long messages

#### classifies long error messages

- classifies long error messages
- Verify: classifies long error messages
   - Expected: error_type.to_string() equals `parse_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("classifies long error messages")
step("Verify: classifies long error messages")
val long_error = "parse error: " + "x".repeat(1000)
val error_type = classify_error(long_error)
expect(error_type.to_string()).to_equal("parse_error")
```

</details>

#### when handling special characters

#### handles error with quotes

- handles error with quotes
- Verify: handles error with quotes
   - Expected: error_type.to_string() equals `parse_error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles error with quotes")
step("Verify: handles error with quotes")
val error = "parse error: expected '|' found '&'"
val error_type = classify_error(error)
expect(error_type.to_string()).to_equal("parse_error")
```

</details>

#### handles error with newlines

- handles error with newlines
- Verify: handles error with newlines


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles error with newlines")
step("Verify: handles error with newlines")
val error = "parse error\nexpected Fn\nfound Static"
var features = extract_needed_features(error)
expect(features).to_contain("static_fields")
```

</details>

### Performance Characteristics

#### handles many test records efficiently

- handles many test records efficiently
- Verify: handles many test records efficiently
   - Expected: stats.total_failed equals `20`
   - Expected: stats.error_count("parse_error") equals `20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many test records efficiently")
step("Verify: handles many test records efficiently")
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

- handles many unique features
- Verify: handles many unique features
   - Expected: stats.total_failed equals `5`
   - Expected: stats.feature_count("static_fields") equals `1`
   - Expected: stats.feature_count("default_parameters") equals `1`
   - Expected: stats.feature_count("implicit_val_var") equals `1`
   - Expected: stats.feature_count("dict_literal_syntax") equals `1`
   - Expected: stats.feature_count("string_char_at_method") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles many unique features")
step("Verify: handles many unique features")
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

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 58 |
| Active scenarios | 58 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-ERRORTYPE-ENUM-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `46bc5cd8c781931dcfda0aba569cfd5c72b947f2a51e436a0c52203b3f1a6019`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `46bc5cd8c781931dcfda0aba569cfd5c72b947f2a51e436a0c52203b3f1a6019`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `46bc5cd8c781931dcfda0aba569cfd5c72b947f2a51e436a0c52203b3f1a6019`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/test_analysis_spec.spl
mirror: doc/06_spec/unit/app/test_analysis_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/test_analysis_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/test_analysis_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/test_analysis_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 30 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/test_analysis_spec.spl:248:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'converts to string correctly' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_analysis_spec.spl:260:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides descriptions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/test_analysis_spec.spl:276:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects explicit parse error' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
