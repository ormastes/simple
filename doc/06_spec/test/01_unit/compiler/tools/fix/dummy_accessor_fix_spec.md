# Dummy-Accessor Auto-Fix

> The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*` methods that only forward a backing field. This spec covers the auto-fix that rewrites such call sites to direct field access and deletes the wrappers:

<!-- sdn-diagram:id=dummy_accessor_fix_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=dummy_accessor_fix_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

dummy_accessor_fix_spec -> std
dummy_accessor_fix_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=dummy_accessor_fix_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

<details>
<summary>Full Scenario Manual</summary>

# Dummy-Accessor Auto-Fix

The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*` methods that only forward a backing field. This spec covers the auto-fix that rewrites such call sites to direct field access and deletes the wrappers:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Tooling |
| Status | Implemented |
| Source | `test/01_unit/compiler/tools/fix/dummy_accessor_fix_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The `dummy_accessor` / ACC001 lint warns about trivial `get_*`/`set_*`/`is_*`
methods that only forward a backing field. This spec covers the auto-fix that
rewrites such call sites to direct field access and deletes the wrappers:

    obj.get_x()   -> obj.x        # getter / predicate -> varname access
    obj.set_x(v)  -> obj.x = v    # setter             -> assignment

## Key Concepts

| Concept | Description |
|---------|-------------|
| tier-1  | Globally-unambiguous name (only ever a dummy): rewrite every call site, delete wrappers. |
| tier-2  | Ambiguous name (a real method shares it): rewrite only `self.`/`me.` calls in the defining class; keep the wrapper. |
| cache invalidation | Both the wrapper-owning file and caller files change content, so the content-hashed compile cache misses stale entries. |


</details>
