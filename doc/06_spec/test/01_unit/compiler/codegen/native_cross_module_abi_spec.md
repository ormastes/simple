# Native Cross Module Abi Specification

> <details>

<!-- sdn-diagram:id=native_cross_module_abi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_cross_module_abi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_cross_module_abi_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_cross_module_abi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Cross Module Abi Specification

## Scenarios

### native cross-module call ABI regression

#### use_map resolution for bare function names

#### collect_use_imports Single branch now resolves bare names under module prefix

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Before the fix: use_map["is_digit"] was absent for `use std.common.ctype`
# so calls.rs fell through to import_map and picked a non-deterministic
# wrong module's mangled name.
# After the fix: use_map["is_digit"] = "common__ctype__is_digit" so
# calls.rs uses the correct mangled import symbol.
# This assert pins the expected digit count -- if the ABI regresses,
# the native binary returns 0 (bool never true) instead of 10.
assert CTYPE_DIGIT_COUNT_0_TO_127 == 10
```

</details>

#### i64 return via cross-module call also resolved correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# to_lower(ch): if upper(ch) -> ch+32 else ch
# sum over ch in 0..127: 8128 (identity) + 26*32 (uppercase offsets) = 8960
# Before the fix the native binary returned garbage (e.g. 983245137).
assert CTYPE_TO_LOWER_SUM_0_TO_127 == 8960
```

</details>

#### symbol name mangling

#### caller imports mangled name matching exporter symbol

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# `nm .simple/native_cache/objects/*.o` must show:
#   U common__ctype__is_digit  (caller import -- mangled)
#   T common__ctype__is_digit  (callee export -- mangled)
# Before the fix the caller imported bare "is_digit", causing an
# undefined-symbol link error or resolution to a wrong function.
assert true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/codegen/native_cross_module_abi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- native cross-module call ABI regression

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
