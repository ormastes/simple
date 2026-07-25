# Verification Diagnostics Specification

> <details>

<!-- sdn-diagram:id=verification_diagnostics_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=verification_diagnostics_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

verification_diagnostics_spec -> verification
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=verification_diagnostics_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Verification Diagnostics Specification

## Scenarios

### Verification Diagnostics

#### VerificationErrorCode

#### returns stable codes and help text

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(diag.VerificationErrorCode.AopNonGhostTargetsVerified.code()).to_equal("V-AOP-001")
expect(diag.VerificationErrorCode.MacroUndeclaredIntroduction.code()).to_equal("M-INTRO-001")
expect(diag.VerificationErrorCode.MissingTermination.code()).to_equal("V-TERM-001")
expect(diag.VerificationErrorCode.UnsafeInVerified.message()).to_contain("unsafe")
expect(diag.VerificationErrorCode.MissingTermination.help()).to_contain("decreases")
expect(diag.VerificationErrorCode.FfiInVerified.help()).to_contain("@trusted")
```

</details>

#### Span

#### creates spans

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = diag.Span.new(10, 20, 5, 3)
expect(span.start).to_equal(10)
expect(span.end).to_equal(20)
expect(span.line).to_equal(5)
expect(span.column).to_equal(3)
val empty = diag.Span.empty()
expect(empty.start).to_equal(0)
expect(empty.end).to_equal(0)
```

</details>

#### VerificationDiagnostic

#### formats context and location

1. d = d with item


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = diag.Span.new(0, 10, 1, 1)
var d = diag.VerificationDiagnostic.new(
    diag.VerificationErrorCode.MissingTermination,
    span
)
d = d.with_item("factorial").with_file("math.spl").with_context("recursive function")
val formatted = d.format()
expect(formatted).to_contain("V-TERM-001")
expect(formatted).to_contain("factorial")
expect(formatted).to_contain("math.spl")
expect(formatted).to_contain("recursive function")
```

</details>

#### VerificationDiagnostics

#### collects and formats diagnostics

1. var collector = diag VerificationDiagnostics new
   - Expected: collector.is_empty() is true
2. collector push
3. collector push
   - Expected: collector.is_empty() is false
   - Expected: collector.error_count() equals `2`
   - Expected: collector.format_all().len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var collector = diag.VerificationDiagnostics.new()
expect(collector.is_empty()).to_equal(true)

val span = diag.Span.new(0, 10, 1, 1)
collector.push(diag.VerificationDiagnostic.new(diag.VerificationErrorCode.IoInVerified, span))
collector.push(diag.VerificationDiagnostic.new(diag.VerificationErrorCode.FfiInVerified, span))

expect(collector.is_empty()).to_equal(false)
expect(collector.error_count()).to_equal(2)
expect(collector.format_all().len()).to_equal(2)
```

</details>

#### Helper functions

#### builds common diagnostics

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val span = diag.Span.new(0, 10, 1, 1)
expect(diag.missing_termination_error(span, "factorial").code.code()).to_equal("V-TERM-001")
expect(diag.io_in_verified_error(span, "read_file").code.code()).to_equal("V-EFFECT-001")
expect(diag.ffi_in_verified_error(span, "call_c_func").code.code()).to_equal("V-UNSAFE-003")
expect(diag.ghost_access_error(span, "counter").code.code()).to_equal("V-GHOST-001")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/00_formal_verification/compiler/verification_diagnostics_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Verification Diagnostics

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
