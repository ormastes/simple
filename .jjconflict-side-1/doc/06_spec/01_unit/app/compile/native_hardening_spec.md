# Native Hardening Specification

> <details>

<!-- sdn-diagram:id=native_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_hardening_spec -> app
native_hardening_spec -> testing
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Hardening Specification

## Scenarios

### App native build hardening

#### adds unresolved-symbol flags on Linux and FreeBSD

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_link_hardening_flags("linux")).to_equal(
    " -Wl,--allow-multiple-definition -Wl,--unresolved-symbols=ignore-all"
)
expect(native_link_hardening_flags("freebsd")).to_equal(
    " -Wl,--allow-multiple-definition -Wl,--unresolved-symbols=ignore-all"
)
```

</details>

#### skips unresolved-symbol flags on non-ELF hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(native_link_hardening_flags("macos")).to_equal("")
expect(native_link_hardening_flags("windows")).to_equal("")
```

</details>

#### only strips llvm constructors on ELF hosts

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(should_strip_llvm_constructors_for_platform("linux")).to_equal(true)
expect(should_strip_llvm_constructors_for_platform("freebsd")).to_equal(true)
expect(should_strip_llvm_constructors_for_platform("macos")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/compile/native_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- App native build hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
