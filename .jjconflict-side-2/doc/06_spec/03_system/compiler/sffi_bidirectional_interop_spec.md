# Sffi Bidirectional Interop Specification

> <details>

<!-- sdn-diagram:id=sffi_bidirectional_interop_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sffi_bidirectional_interop_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sffi_bidirectional_interop_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sffi_bidirectional_interop_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sffi Bidirectional Interop Specification

## Scenarios

### SFFI Bidirectional Class Interop

#### fixture declares C representation and C export

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sffi_fixture_source()
expect(source).to_contain("@repr(\"C\")")
expect(source).to_contain("@export(\"C\")")
expect(source).to_contain("class GpioRegister")
```

</details>

#### fixture carries bitfield metadata expected by C layout generation

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sffi_fixture_source()
expect(source).to_contain("mode: u8 @bits(4)")
expect(source).to_contain("output: bool @bits(1)")
expect(source).to_contain("input: bool @bits(1)")
expect(source).to_contain("speed: u8 @bits(2)")
```

</details>

#### fixture includes standalone exported function

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val source = sffi_fixture_source()
expect(source).to_contain("fn add_numbers(a: i32, b: i32) -> i32")
expect(source).to_contain("a + b")
```

</details>

#### shared library naming follows supported platform conventions

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(shared_lib_name("gpio_driver", "linux")).to_equal("libgpio_driver.so")
expect(shared_lib_name("gpio_driver", "darwin")).to_equal("libgpio_driver.dylib")
expect(shared_lib_name("gpio_driver", "windows")).to_equal("gpio_driver.dll")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/sffi_bidirectional_interop_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SFFI Bidirectional Class Interop

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
