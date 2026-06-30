# Unsupported Construct Verification Specification

> Verifies that the verification checker correctly rejects unsupported constructs when used with @verify. Async functions, FFI calls, and unsafe operations must produce clear error diagnostics rather than silently generating incorrect Lean.

<!-- sdn-diagram:id=unsupported_construct_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unsupported_construct_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unsupported_construct_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unsupported_construct_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unsupported Construct Verification Specification

Verifies that the verification checker correctly rejects unsupported constructs when used with @verify. Async functions, FFI calls, and unsafe operations must produce clear error diagnostics rather than silently generating incorrect Lean.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LEAN-UNSUP-001 |
| Category | Infrastructure |
| Difficulty | 2/5 |
| Status | Implemented |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/00_formal_verification/compiler/unsupported_construct_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the verification checker correctly rejects unsupported constructs
when used with @verify. Async functions, FFI calls, and unsafe operations must
produce clear error diagnostics rather than silently generating incorrect Lean.

## Behavior

- IO functions in verified context produce V-EFFECT-001 errors
- Unsafe operations in verified context produce V-UNSAFE-001 errors
- FFI calls are detected via the `check_unsafe_operation("ffi_call")` path
- Recursive functions without termination proof produce V-TERM-001 errors
- Multiple violations are all reported (not just the first)

## Scenarios

### Unsupported Construct Detection

#### IO effects in verified context

#### rejects verified function calling IO functions

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "my_verified_fn",
    false,       # not recursive
    false,       # no termination needed
    ["print", "read_file"],  # IO calls
    false        # no unsafe ops
)
expect(result.has_errors()).to_equal(true)
expect(result.error_count()).to_equal(2)
```

</details>

#### produces V-EFFECT-001 error code for IO violations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_call_in_verified("print")
expect(check).to_equal(Some(diag.VerificationErrorCode.IoInVerified))
```

</details>

#### allows pure functions in verified context

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "pure_fn",
    false,
    false,
    [],          # no IO calls
    false        # no unsafe ops
)
expect(result.has_errors()).to_equal(false)
```

</details>

#### unsafe operations in verified context

#### rejects verified function with unsafe operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "unsafe_verified_fn",
    false,
    false,
    [],
    true         # has unsafe ops
)
expect(result.has_errors()).to_equal(true)
expect(result.error_count()).to_equal(1)
```

</details>

#### detects raw pointer dereference as unsafe

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_unsafe_operation("raw_pointer_deref")
expect(check).to_equal(Some(diag.VerificationErrorCode.RawPointerInVerified))
```

</details>

#### detects unsafe cast as violation

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_unsafe_operation("unsafe_cast")
expect(check).to_equal(Some(diag.VerificationErrorCode.UnsafeInVerified))
```

</details>

#### FFI calls in verified context

#### detects FFI call as unsupported in verified code

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_unsafe_operation("ffi_call")
expect(check).to_equal(Some(diag.VerificationErrorCode.FfiInVerified))
```

</details>

#### produces clear FFI error via VerificationChecker

1. var vc = checker VerificationChecker new
2. vc report ffi error
   - Expected: result.has_errors() is true
   - Expected: result.error_count() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var vc = checker.VerificationChecker.new()
val span = diag.Span.empty()
vc.report_ffi_error(span, "extern_crypto_hash")
val result = vc.get_result()
expect(result.has_errors()).to_equal(true)
expect(result.error_count()).to_equal(1)
```

</details>

#### recursive functions without termination

#### rejects recursive function missing decreases clause

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "recursive_fn",
    true,        # is recursive
    false,       # NO termination proof
    [],
    false
)
expect(result.has_errors()).to_equal(true)
expect(result.error_count()).to_equal(1)
```

</details>

#### allows recursive function with termination proof

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "recursive_fn",
    true,        # is recursive
    true,        # has termination proof
    [],
    false
)
expect(result.has_errors()).to_equal(false)
```

</details>

#### multiple violations

#### reports all violations, not just the first

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = checker.validate_verified_function(
    "bad_fn",
    true,        # recursive
    false,       # no termination
    ["println", "write_file", "sleep"],  # 3 IO calls
    true         # unsafe ops
)
# 1 termination + 3 IO + 1 unsafe = 5 errors
expect(result.has_errors()).to_equal(true)
expect(result.error_count()).to_equal(5)
```

</details>

#### contract purity

#### rejects mutating calls in contract expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_call_in_contract("set_value")
expect(check).to_equal(Some(diag.VerificationErrorCode.ContractHasSideEffects))
```

</details>

#### allows pure reads in contract expressions

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_call_in_contract("get_value")
expect(check).to_equal(nil)
```

</details>

#### allowed operations pass cleanly

#### returns nil for unknown operations

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_unsafe_operation("normal_call")
expect(check).to_equal(nil)
```

</details>

#### allows non-IO function names

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val check = checker.check_call_in_verified("calculate_sum")
expect(check).to_equal(nil)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
