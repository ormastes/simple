# Native Link Hardening Specification

> <details>

<!-- sdn-diagram:id=native_link_hardening_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=native_link_hardening_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

native_link_hardening_spec -> compiler
native_link_hardening_spec -> testing
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=native_link_hardening_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Native Link Hardening Specification

## Scenarios

### Native linker hardening

#### adds unresolved-symbol flags for ELF direct linkers

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unresolved_symbol_flags_for_unix_linker("linux")).to_equal([
    "--allow-multiple-definition",
    "--unresolved-symbols=ignore-all"
])
expect(unresolved_symbol_flags_for_unix_linker("freebsd")).to_equal([
    "--allow-multiple-definition",
    "--unresolved-symbols=ignore-all"
])
```

</details>

#### skips ELF unresolved-symbol flags on non-ELF direct linkers

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unresolved_symbol_flags_for_unix_linker("macos")).to_equal([])
expect(unresolved_symbol_flags_for_unix_linker("darwin")).to_equal([])
```

</details>

#### adds unresolved-symbol flags for cc fallback on Linux and FreeBSD

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unresolved_symbol_flags_for_cc("Linux")).to_equal([
    "-Wl,--allow-multiple-definition",
    "-Wl,--unresolved-symbols=ignore-all"
])
expect(unresolved_symbol_flags_for_cc("FreeBSD")).to_equal([
    "-Wl,--allow-multiple-definition",
    "-Wl,--unresolved-symbols=ignore-all"
])
```

</details>

#### skips cc fallback unresolved-symbol flags on Darwin

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(unresolved_symbol_flags_for_cc("Darwin")).to_equal([])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/native_link_hardening_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Native linker hardening

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
