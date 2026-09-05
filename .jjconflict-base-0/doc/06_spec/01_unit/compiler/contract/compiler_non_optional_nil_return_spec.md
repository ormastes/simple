# Compiler functions widened to satisfy the non-optional return contract

> The strict seed traps at runtime with "nil is forbidden by the non-optional return contract of '<fn>' [E-SFFI-016]" whenever a function declared `-> T` (no trailing `?`) has a code path that tails off into `nil`. A sweep across `src/compiler/**` found 42 such sites; each was either (a) widened to `T?` because the nil is a legitimate "not found" / "no info" outcome that callers already distinguish, or (b) made total by returning a valid default.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Compiler functions widened to satisfy the non-optional return contract

The strict seed traps at runtime with "nil is forbidden by the non-optional return contract of '<fn>' [E-SFFI-016]" whenever a function declared `-> T` (no trailing `?`) has a code path that tails off into `nil`. A sweep across `src/compiler/**` found 42 such sites; each was either (a) widened to `T?` because the nil is a legitimate "not found" / "no info" outcome that callers already distinguish, or (b) made total by returning a valid default.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler internals / return-type contracts |
| Status | Active |
| Source | `test/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The strict seed traps at runtime with "nil is forbidden by the non-optional
return contract of '<fn>' [E-SFFI-016]" whenever a function declared
`-> T` (no trailing `?`) has a code path that tails off into `nil`. A sweep
across `src/compiler/**` found 42 such sites; each was either (a) widened to
`T?` because the nil is a legitimate "not found" / "no info" outcome that
callers already distinguish, or (b) made total by returning a valid default.

This spec exercises a representative sample of the widened (`T?`) functions
on their nil path, plus one totalized (non-optional) function, to prove the
fix compiles and behaves sanely under the strict seed.

## Coverage

- `get_extension_config` (src/compiler/99.loader/module_resolver/types.spl):
  unknown extension -> nil, known extension -> Some(config).
- `backend_for_name` (src/compiler/70.backend/backend/backend_helpers.spl):
  unknown name -> nil, known name -> Some(BackendKind).
- `shb_find_fn` (src/compiler/80.driver/shb/shb_hash.spl): missing name -> nil,
  present name -> Some(entry).
- `unwrap_promise` (src/compiler/30.types/type_system/effects.spl): totalized
  to return the input unchanged when it is not a `Promise<T>` wrapper, instead
  of nil.

## Scenarios

### non-optional return contract fixes

#### get_extension_config returns nil for an unknown extension and a value for a known one

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- get_extension_config returns nil for an unknown extension and a value for a known one


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("get_extension_config returns nil for an unknown extension and a value for a known one")
val missing = get_extension_config("not_a_real_extension_xyz")
assert_true(missing == nil)
val found = get_extension_config("spl")
assert_true(found != nil)
val cfg = found!
assert_equal(cfg.extension, "spl")
```

</details>

#### backend_for_name returns nil for an unknown name and a value for a known one

- backend_for_name returns nil for an unknown name and a value for a known one


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("backend_for_name returns nil for an unknown name and a value for a known one")
val missing = backend_for_name("not_a_real_backend_xyz")
assert_true(missing == nil)
val found = backend_for_name("lua")
assert_true(found != nil)
```

</details>

#### shb_find_fn returns nil for a missing name and the entry for a present one

- shb_find_fn returns nil for a missing name and the entry for a present one


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shb_find_fn returns nil for a missing name and the entry for a present one")
val entries: [ShbFnEntry] = [
    ShbFnEntry(name: "alpha", params: [], return_type: "i64", flags: 0)
]
val missing = shb_find_fn(entries, "beta")
assert_true(missing == nil)
val found = shb_find_fn(entries, "alpha")
assert_true(found != nil)
assert_equal(found!.name, "alpha")
```

</details>

#### unwrap_promise is total: non-Promise input passes through unchanged

- unwrap_promise is total: non-Promise input passes through unchanged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("unwrap_promise is total: non-Promise input passes through unchanged")
assert_equal(unwrap_promise("i64"), "i64")
assert_equal(unwrap_promise("Promise<text>"), "text")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `9c8c3dfe1356f838ee5d61f462aa2916f934a5acfbfaeea27d85c5e8349b4b83`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9c8c3dfe1356f838ee5d61f462aa2916f934a5acfbfaeea27d85c5e8349b4b83`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9c8c3dfe1356f838ee5d61f462aa2916f934a5acfbfaeea27d85c5e8349b4b83`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.spl
mirror: doc/06_spec/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'get_extension_config returns nil for an unknown extension and a value for a known one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'backend_for_name returns nil for an unknown name and a value for a known one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/contract/compiler_non_optional_nil_return_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shb_find_fn returns nil for a missing name and the entry for a present one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
