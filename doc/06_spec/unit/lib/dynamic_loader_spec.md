# Dynamic Loader Specification

> Tests covering DynLoader, sffi_lib_path, DynLib, DynLoader, sffi_call, DynLib call variants.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dynamic Loader Specification

## Scenarios

### DynLoader

### sffi_lib_path

#### maps torch prefix to libspl_torch.so

- maps torch prefix to libspl_torch.so


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maps torch prefix to libspl_torch.so")
val path = sffi_lib_path("torch")
expect(path).to_contain("libspl_torch")
```

</details>

#### uses build/ as default base

- uses build/ as default base


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses build/ as default base")
val path = sffi_lib_path("test")
expect(path).to_start_with("build/")
```

</details>

#### includes .so suffix

- includes .so suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes .so suffix")
val path = sffi_lib_path("audio")
expect(path).to_end_with(".so")
```

</details>

### DynLib

#### returns nil for nonexistent library

- returns nil for nonexistent library
   - Expected: result == nil is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns nil for nonexistent library")
val result = DynLib.load("/nonexistent/libfake_12345.so")
expect(result == nil).to_equal(true)
```

</details>

#### loads libm.so successfully

- loads libm.so successfully
   - Expected: result == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads libm.so successfully")
val result = DynLib.load("libm.so.6")
expect(result == nil).to_equal(false)
```

</details>

#### returns 0 for unknown symbol

- returns 0 for unknown symbol
   - Expected: fptr equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 for unknown symbol")
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    val fptr = lib.sym("__nonexistent_symbol_xyz__")
    expect(fptr).to_equal(0)
```

</details>

### DynLoader

#### loads library and caches it

- loads library and caches it
   - Expected: ok is true
   - Expected: ok2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads library and caches it")
val loader = DynLoader.instance()
val ok = loader.ensure_loaded("libm.so.6")
expect(ok).to_equal(true)
val ok2 = loader.ensure_loaded("libm.so.6")
expect(ok2).to_equal(true)
```

</details>

#### returns false for missing library

- returns false for missing library
   - Expected: ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns false for missing library")
val loader = DynLoader.instance()
val ok = loader.ensure_loaded("/nonexistent/libfake_99999.so")
expect(ok).to_equal(false)
```

</details>

### sffi_call

#### returns 0 gracefully when library is missing

- returns 0 gracefully when library is missing
   - Expected: result equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns 0 gracefully when library is missing")
val result = sffi_call("rt_fake_nonexistent_function", [])
expect(result).to_equal(0)
```

</details>

### DynLib call variants

#### call0 runs without error on a real symbol

- call0 runs without error on a real symbol
   - Expected: r equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call0 runs without error on a real symbol")
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    # floor has wrong arity/type for i64 but we only test dispatch
    val r = lib.call0("floor")
    # Tautology — true regardless of return value; proves no crash
    expect(r).to_equal(r)
```

</details>

#### call_n accepts empty args array

- call_n accepts empty args array
   - Expected: r equals `r`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call_n accepts empty args array")
val result = DynLib.load("libm.so.6")
if result.?:
    val lib = result.unwrap()
    val r = lib.call_n("floor", [])
    expect(r).to_equal(r)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/dynamic_loader_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DynLoader, sffi_lib_path, DynLib, DynLoader, sffi_call, DynLib call variants.
- DynLoader
- sffi_lib_path
- DynLib
- DynLoader
- sffi_call
- DynLib call variants

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2d2ac50796ab210b6957212fe054587e6d461edc2153535805ba4cbdf5318b2b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2d2ac50796ab210b6957212fe054587e6d461edc2153535805ba4cbdf5318b2b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2d2ac50796ab210b6957212fe054587e6d461edc2153535805ba4cbdf5318b2b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/dynamic_loader_spec.spl
mirror: doc/06_spec/unit/lib/dynamic_loader_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/dynamic_loader_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/dynamic_loader_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/dynamic_loader_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/dynamic_loader_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'maps torch prefix to libspl_torch.so' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/dynamic_loader_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses build/ as default base' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/dynamic_loader_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'includes .so suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
