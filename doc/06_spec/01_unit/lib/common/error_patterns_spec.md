# Error Patterns Specification

> Tests covering ErrorKind constants, simple_error, simple_error_with_source, make_error, make_io_error, make_validation_error, format_error, format_error_compact, error handling patterns.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Error Patterns Specification

## Scenarios

### ErrorKind constants

#### has NotFound kind

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has NotFound kind
   - Expected: ERROR_NOT_FOUND equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has NotFound kind")
expect(ERROR_NOT_FOUND).to_equal("not found")
```

</details>

#### has PermissionDenied kind

- has PermissionDenied kind
   - Expected: ERROR_PERMISSION_DENIED equals `permission denied`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has PermissionDenied kind")
expect(ERROR_PERMISSION_DENIED).to_equal("permission denied")
```

</details>

#### has InvalidInput kind

- has InvalidInput kind
   - Expected: ERROR_INVALID_INPUT equals `invalid input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has InvalidInput kind")
expect(ERROR_INVALID_INPUT).to_equal("invalid input")
```

</details>

#### has InvalidData kind

- has InvalidData kind
   - Expected: ERROR_INVALID_DATA equals `invalid data`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has InvalidData kind")
expect(ERROR_INVALID_DATA).to_equal("invalid data")
```

</details>

#### has Unknown kind

- has Unknown kind
   - Expected: ERROR_UNKNOWN equals `unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has Unknown kind")
expect(ERROR_UNKNOWN).to_equal("unknown error")
```

</details>

#### has TimedOut kind

- has TimedOut kind
   - Expected: ERROR_TIMED_OUT equals `timed out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has TimedOut kind")
expect(ERROR_TIMED_OUT).to_equal("timed out")
```

</details>

#### has AlreadyExists kind

- has AlreadyExists kind
   - Expected: ERROR_ALREADY_EXISTS equals `already exists`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has AlreadyExists kind")
expect(ERROR_ALREADY_EXISTS).to_equal("already exists")
```

</details>

#### has all 13 error kinds

- has all 13 error kinds
   - Expected: kinds.len() equals `13`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has all 13 error kinds")
val kinds = [ERROR_NOT_FOUND, ERROR_PERMISSION_DENIED, ERROR_CONNECTION_REFUSED, ERROR_CONNECTION_RESET, ERROR_INTERRUPTED, ERROR_TIMED_OUT, ERROR_INVALID_INPUT, ERROR_INVALID_DATA, ERROR_UNEXPECTED_EOF, ERROR_ALREADY_EXISTS, ERROR_WOULD_BLOCK, ERROR_OTHER, ERROR_UNKNOWN]
expect(kinds.len()).to_equal(13)
```

</details>

### simple_error

#### creates error with kind and message

- creates error with kind and message
   - Expected: error_message(err) equals `File not found: data.txt`
   - Expected: error_kind(err) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates error with kind and message")
val err = simple_error(ERROR_NOT_FOUND, "File not found: data.txt")
expect(error_message(err)).to_equal("File not found: data.txt")
expect(error_kind(err)).to_equal("not found")
```

</details>

#### creates error with nil source

- creates error with nil source


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates error with nil source")
val err = simple_error(ERROR_UNKNOWN, "something failed")
val src = error_source(err)
expect(src).to_be_nil()
```

</details>

### simple_error_with_source

#### creates error with source chain

- creates error with source chain
   - Expected: error_message(outer) equals `config load failed`
   - Expected: error_kind(outer) equals `invalid data`
   - Expected: error_message(src) equals `file missing`
   - Expected: error_kind(src) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates error with source chain")
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
expect(error_message(outer)).to_equal("config load failed")
expect(error_kind(outer)).to_equal("invalid data")
val src = error_source(outer)
expect(error_message(src)).to_equal("file missing")
expect(error_kind(src)).to_equal("not found")
```

</details>

#### creates deep error chain

- creates deep error chain
   - Expected: error_message(e3) equals `operation failed`
   - Expected: error_message(src2) equals `request failed`
   - Expected: error_message(src1) equals `server down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates deep error chain")
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
expect(error_message(e3)).to_equal("operation failed")
val src2 = error_source(e3)
expect(error_message(src2)).to_equal("request failed")
val src1 = error_source(src2)
expect(error_message(src1)).to_equal("server down")
val src0 = error_source(src1)
expect(src0).to_be_nil()
```

</details>

### make_error

#### creates error with Unknown kind

- creates error with Unknown kind
   - Expected: error_message(err) equals `something went wrong`
   - Expected: error_kind(err) equals `unknown error`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates error with Unknown kind")
val err = make_error("something went wrong")
expect(error_message(err)).to_equal("something went wrong")
expect(error_kind(err)).to_equal("unknown error")
```

</details>

### make_io_error

#### creates IO error with specified kind

- creates IO error with specified kind
   - Expected: error_message(err) equals `file.txt not found`
   - Expected: error_kind(err) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates IO error with specified kind")
val err = make_io_error(ERROR_NOT_FOUND, "file.txt not found")
expect(error_message(err)).to_equal("file.txt not found")
expect(error_kind(err)).to_equal("not found")
```

</details>

#### creates different IO error kinds

- creates different IO error kinds
   - Expected: error_kind(e1) equals `permission denied`
   - Expected: error_kind(e2) equals `timed out`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates different IO error kinds")
val e1 = make_io_error(ERROR_PERMISSION_DENIED, "access denied")
val e2 = make_io_error(ERROR_TIMED_OUT, "connection timed out")
expect(error_kind(e1)).to_equal("permission denied")
expect(error_kind(e2)).to_equal("timed out")
```

</details>

### make_validation_error

#### creates validation error with InvalidInput kind

- creates validation error with InvalidInput kind
   - Expected: error_message(err) equals `email format invalid`
   - Expected: error_kind(err) equals `invalid input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("creates validation error with InvalidInput kind")
val err = make_validation_error("email format invalid")
expect(error_message(err)).to_equal("email format invalid")
expect(error_kind(err)).to_equal("invalid input")
```

</details>

### format_error

#### formats single error

- formats single error
   - Expected: formatted equals `Error: file missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats single error")
val err = simple_error(ERROR_NOT_FOUND, "file missing")
val formatted = format_error(err)
expect(formatted).to_equal("Error: file missing")
```

</details>

#### formats error with source chain

- formats error with source chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats error with source chain")
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
val formatted = format_error(outer)
expect(formatted).to_contain("Error: config load failed")
expect(formatted).to_contain("Caused by: file missing")
```

</details>

#### formats deep error chain

- formats deep error chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats deep error chain")
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
val formatted = format_error(e3)
expect(formatted).to_contain("Error: operation failed")
expect(formatted).to_contain("Caused by: request failed")
expect(formatted).to_contain("Caused by: server down")
```

</details>

### format_error_compact

#### formats single error compactly

- formats single error compactly
   - Expected: formatted equals `file missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats single error compactly")
val err = simple_error(ERROR_NOT_FOUND, "file missing")
val formatted = format_error_compact(err)
expect(formatted).to_equal("file missing")
```

</details>

#### formats error chain with colons

- formats error chain with colons
   - Expected: formatted equals `config load failed: file missing`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats error chain with colons")
val inner = simple_error(ERROR_NOT_FOUND, "file missing")
val outer = simple_error_with_source(ERROR_INVALID_DATA, "config load failed", inner)
val formatted = format_error_compact(outer)
expect(formatted).to_equal("config load failed: file missing")
```

</details>

#### formats deep chain compactly

- formats deep chain compactly
   - Expected: formatted equals `operation failed: request failed: server down`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("formats deep chain compactly")
val e1 = simple_error(ERROR_CONNECTION_REFUSED, "server down")
val e2 = simple_error_with_source(ERROR_TIMED_OUT, "request failed", e1)
val e3 = simple_error_with_source(ERROR_OTHER, "operation failed", e2)
val formatted = format_error_compact(e3)
expect(formatted).to_equal("operation failed: request failed: server down")
```

</details>

### error handling patterns

#### uses nil for no error (option pattern)

- uses nil for no error (option pattern)
   - Expected: result equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses nil for no error (option pattern)")
var current_error = nil
# Simulate successful operation
val result = 42
expect(current_error).to_be_nil()
expect(result).to_equal(42)
```

</details>

#### uses error dict for failure (option pattern)

- uses error dict for failure (option pattern)
   - Expected: has_error is true
   - Expected: error_message(current_error) equals `operation failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses error dict for failure (option pattern)")
var current_error = nil
# Simulate failed operation
current_error = make_error("operation failed")
val has_error = current_error != nil
expect(has_error).to_equal(true)
expect(error_message(current_error)).to_equal("operation failed")
```

</details>

#### propagates errors through chain

- propagates errors through chain
   - Expected: error_kind(final_err) equals `invalid data`
   - Expected: error_kind(src) equals `not found`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("propagates errors through chain")
fn inner_op() -> dict:
    make_io_error(ERROR_NOT_FOUND, "data.txt not found")
fn outer_op() -> dict:
    val err = inner_op()
    simple_error_with_source(ERROR_INVALID_DATA, "cannot load config", err)
val final_err = outer_op()
expect(error_kind(final_err)).to_equal("invalid data")
val src = error_source(final_err)
expect(error_kind(src)).to_equal("not found")
```

</details>

#### handles multiple error kinds differently

- handles multiple error kinds differently
   - Expected: handle_error(e1) equals `retry with default`
   - Expected: handle_error(e2) equals `request access`
   - Expected: handle_error(e3) equals `retry later`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles multiple error kinds differently")
fn handle_error(err: dict) -> text:
    val kind = error_kind(err)
    if kind == ERROR_NOT_FOUND:
        return "retry with default"
    if kind == ERROR_PERMISSION_DENIED:
        return "request access"
    if kind == ERROR_TIMED_OUT:
        return "retry later"
    "unknown handling"
val e1 = make_io_error(ERROR_NOT_FOUND, "missing")
val e2 = make_io_error(ERROR_PERMISSION_DENIED, "denied")
val e3 = make_io_error(ERROR_TIMED_OUT, "slow")
expect(handle_error(e1)).to_equal("retry with default")
expect(handle_error(e2)).to_equal("request access")
expect(handle_error(e3)).to_equal("retry later")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/error_patterns_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ErrorKind constants, simple_error, simple_error_with_source, make_error, make_io_error, make_validation_error, format_error, format_error_compact, error handling patterns.
- ErrorKind constants
- simple_error
- simple_error_with_source
- make_error
- make_io_error
- make_validation_error
- format_error
- format_error_compact
- error handling patterns

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9a995e818c88fa1fae3780e2be618beb062236bb71e3ade62c0af0ebd9be282e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9a995e818c88fa1fae3780e2be618beb062236bb71e3ade62c0af0ebd9be282e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9a995e818c88fa1fae3780e2be618beb062236bb71e3ade62c0af0ebd9be282e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/error_patterns_spec.spl
mirror: doc/06_spec/01_unit/lib/common/error_patterns_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/error_patterns_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/error_patterns_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/error_patterns_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/error_patterns_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has NotFound kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/error_patterns_spec.spl:102:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has PermissionDenied kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/error_patterns_spec.spl:107:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has InvalidInput kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
