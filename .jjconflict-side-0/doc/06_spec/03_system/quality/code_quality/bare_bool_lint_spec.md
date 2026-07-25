# Bare Bool Lint Spec — Text Scanner Behavior

> Tests the text-scanner lint (`check_bare_bool`) behavior after the predicate-exemption wave:

<!-- sdn-diagram:id=bare_bool_lint_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=bare_bool_lint_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

bare_bool_lint_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=bare_bool_lint_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bare Bool Lint Spec — Text Scanner Behavior

Tests the text-scanner lint (`check_bare_bool`) behavior after the predicate-exemption wave:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-bare-bool-suppressions |
| Category | Tooling |
| Difficulty | 2/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/bare_bool_lint_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the text-scanner lint (`check_bare_bool`) behavior after the
predicate-exemption wave:

- Group 1: Parameter detection — `pub fn` with `: bool` param fires; return-only bool does NOT.
- Group 2: Private function exemption — non-pub fn is skipped.
- Group 3: Predicate prefix with bool param — text-scanner still fires on bool *params*
  in `is_*` fns (D-1 only exempts the Rust AST return-type path, not text-scanner params).

Note: The text-scanner never fires on return types regardless of D-1.  These specs
test the text-scanner path only; the Rust AST predicate exemption is integration-verified
via the normal build lint after checker_core.rs lands.

## Scenarios

### bare_bool lint — parameter detection

#### AC-1a: should flag pub fn with a bool parameter

1. "pub fn set enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn set_enabled(flag: bool):\n" +
    "    pass_dn\n"
expect(count_bare_bool_fixes(source)).to_be_greater_than(0)
```

</details>

#### AC-1b: should NOT flag pub fn whose only bool is the return type

1. "pub fn is ready
   - Expected: count_bare_bool_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn is_ready() -> bool:\n" +
    "    return true\n"
expect(count_bare_bool_fixes(source)).to_equal(0)
```

</details>

#### AC-1c: should flag pub fn with a mixed signature (bool param + bool return)

1. "pub fn toggle


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn toggle(current: bool) -> bool:\n" +
    "    return not current\n"
expect(count_bare_bool_fixes(source)).to_be_greater_than(0)
```

</details>

### bare_bool lint — private function exemption

#### AC-2a: should NOT flag private fn with a bool parameter

1. "fn internal toggle
   - Expected: count_bare_bool_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "fn internal_toggle(flag: bool):\n" +
    "    pass_dn\n"
expect(count_bare_bool_fixes(source)).to_equal(0)
```

</details>

### bare_bool lint — predicate prefix does NOT exempt bool params

#### AC-3a: should flag is_* fn that takes a bool parameter

1. "pub fn is flagged


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn is_flagged(flag: bool) -> bool:\n" +
    "    return flag\n"
expect(count_bare_bool_fixes(source)).to_be_greater_than(0)
```

</details>

#### AC-3b: should NOT flag is_* fn with no bool parameters (return type only)

1. "pub fn is active
   - Expected: count_bare_bool_fixes(source) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source =
    "pub fn is_active() -> bool:\n" +
    "    return true\n"
expect(count_bare_bool_fixes(source)).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
