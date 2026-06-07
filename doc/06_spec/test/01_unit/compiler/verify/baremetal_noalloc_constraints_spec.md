# baremetal_noalloc_constraints_spec

> Bare-metal verifier noalloc source constraint regression.

<!-- sdn-diagram:id=baremetal_noalloc_constraints_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=baremetal_noalloc_constraints_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

baremetal_noalloc_constraints_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=baremetal_noalloc_constraints_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# baremetal_noalloc_constraints_spec

Bare-metal verifier noalloc source constraint regression.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/verify/baremetal_noalloc_constraints_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Bare-metal verifier noalloc source constraint regression.

This scans the verifier source so the production command continues to enforce
the same boundaries as the library dependency tests.

## Scenarios

### baremetal verifier noalloc constraints

#### has a reusable no-match source constraint helper

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("fn check_no_matches(label: text, cmd: text) -> bool:", path)).to_equal(true)
expect(_has("matches.len() == 0", path)).to_equal(true)
```

</details>

#### checks current build and documentation artifact paths

<details>
<summary>Executable SPipe</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("src/app/build/baremetal.smf", path)).to_equal(true)
expect(_has("src/app/build/__init__.smf", path)).to_equal(true)
expect(_has("src/app/build/types.smf", path)).to_equal(true)
expect(_has("doc/07_guide/backend/baremetal.md", path)).to_equal(true)
expect(_has("doc/09_report/2026/02/baremetal_build_system_integration_2026-02-14.md", path)).to_equal(true)
```

</details>

#### guards noalloc against allocating runtime family imports

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no allocating-family imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("std\\\\.(nogc_sync_mut|nogc_async_mut|nogc_async_immut|gc_async_mut)\\\\.", path)).to_equal(true)
```

</details>

#### guards noalloc against hosted app imports

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no app imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("app\\\\.", path)).to_equal(true)
```

</details>

#### guards noalloc against allocation annotations

<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no allocation annotations in nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("@alloc\\\\b", path)).to_equal(true)
```

</details>

#### guards noalloc against host allocation APIs

<details>
<summary>Executable SPipe</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no host allocation APIs in nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("malloc|calloc|free", path)).to_equal(true)
expect(_has("rt_alloc", path)).to_equal(true)
expect(_has("extern fn .*realloc", path)).to_equal(true)
```

</details>

#### guards noalloc against unsafe reachable helper imports

<details>
<summary>Executable SPipe</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "src/compiler/90.tools/verify/baremetal.spl"
expect(_has("no unsafe reachable imports from nogc_async_mut_noalloc", path)).to_equal(true)
expect(_has("verify_noalloc_reachable_imports", path)).to_equal(true)
expect(_has("compiler.tools.verify.noalloc_reachable", path)).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
