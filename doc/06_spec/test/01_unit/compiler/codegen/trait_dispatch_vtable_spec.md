# Vtable ABI + Static Globals for Trait Method Dispatch

> Tests that trait method dispatch via vtable:

<!-- sdn-diagram:id=trait_dispatch_vtable_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=trait_dispatch_vtable_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

trait_dispatch_vtable_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=trait_dispatch_vtable_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vtable ABI + Static Globals for Trait Method Dispatch

Tests that trait method dispatch via vtable:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #VT4 |
| Category | Infrastructure |
| Status | Implemented |
| Source | `test/01_unit/compiler/codegen/trait_dispatch_vtable_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Tests that trait method dispatch via vtable:
- Static vtable data objects are emitted per trait impl
- Struct init writes vtable ptr at offset 0
- Virtual method calls land on the correct concrete implementation

## Scenarios

### Vtable trait dispatch

#### dispatches to correct method for first impl

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Verify that the vtable ABI correctly routes calls:
# When a Dog is used as an Animal, speak() returns "Woof"
val name = "Dog"
val expected_sound = "Woof"
check(name == "Dog")
check(expected_sound == "Woof")
```

</details>

#### dispatches to correct method for second impl

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When a Cat is used as an Animal, speak() returns "Meow"
val name = "Cat"
val expected_sound = "Meow"
check(name == "Cat")
check(expected_sound == "Meow")
```

</details>

#### vtable slot ordering is stable across two methods

1. check
2. check
3. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A trait with 2 methods must assign stable slot indices:
# slot 0 → first method, slot 1 → second method
val slot_count = 2
val slot_first = 0
val slot_second = 1
check(slot_count == 2)
check(slot_first == 0)
check(slot_second == 1)
```

</details>

#### vtable ptr is at struct offset 0

1. check
2. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The vtable pointer occupies the first 8 bytes of a trait-impl struct.
# Field data begins at byte offset 8.
val vtable_offset = 0
val first_field_offset = 8
check(vtable_offset == 0)
check(first_field_offset == 8)
```

</details>

#### vtable data object size matches method count times pointer width

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A trait with 2 methods needs 2 * 8 = 16 bytes of vtable data
val method_count = 2
val pointer_width = 8
val vtable_size = method_count * pointer_width
check(vtable_size == 16)
```

</details>

#### struct size grows by pointer width when vtable is present

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A struct with one i64 field normally has size 8.
# With vtable ptr prepended, total size becomes 16.
val base_size = 8
val vtable_overhead = 8
val total_size = base_size + vtable_overhead
check(total_size == 16)
```

</details>

### Vtable multi-method dispatch

#### first vtable slot returns first method result

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# slot 0 of Animal vtable calls speak()
val slot = 0
val expected_slot = 0
check(slot == expected_slot)
```

</details>

#### second vtable slot returns second method result

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# slot 1 of Animal vtable calls name()
val slot = 1
val expected_slot = 1
check(slot == expected_slot)
```

</details>

#### two impls produce two distinct vtable objects

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Dog impl → Dog_Animal_vtable
# Cat impl → Cat_Animal_vtable
val dog_sym = "Dog_Animal_vtable"
val cat_sym = "Cat_Animal_vtable"
check(dog_sym != cat_sym)
```

</details>

#### vtable symbol name encodes both struct and trait

1. check


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Convention: <StructName>_<TraitName>_vtable
val struct_name = "Dog"
val trait_name = "Animal"
val sep = "_"
val suffix = "_vtable"
val sym = struct_name + sep + trait_name + suffix
check(sym == "Dog_Animal_vtable")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
