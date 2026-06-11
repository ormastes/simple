# Type Subst Specification

> <details>

<!-- sdn-diagram:id=type_subst_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=type_subst_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

type_subst_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=type_subst_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Type Subst Specification

## Scenarios

### Type Subst

#### keeps type substitution state APIs available

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = subst_source()

expect(source).to_contain("var subst_param_names: [text] = []")
expect(source).to_contain("var subst_type_tags: [i64] = []")
expect(source).to_contain("fn type_subst_reset()")
expect(source).to_contain("fn type_subst_add(param_name: text, type_tag: i64)")
expect(source).to_contain("fn type_subst_lookup(param_name: text) -> i64")
expect(source).to_contain("return subst_type_tags[i]")
expect(source).to_contain("-1")
```

</details>

#### keeps expression statement and declaration substitution walkers available

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = subst_source()

expect(source).to_contain("fn subst_type_in_expr(eid: i64)")
expect(source).to_contain("fn subst_type_in_stmt(sid: i64)")
expect(source).to_contain("fn type_subst_lookup_by_tag(type_tag: i64) -> i64")
expect(source).to_contain("fn subst_type_in_decl(did: i64)")
expect(source).to_contain("fn type_subst_specialize_decl(generic_did: i64, param_names: [text], type_tags: [i64]) -> i64")
expect(source).to_contain("subst_type_in_decl(cloned_did)")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/type_subst_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Type Subst

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
