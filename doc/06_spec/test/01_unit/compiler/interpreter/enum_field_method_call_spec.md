# Enum-Field Method Call Regression

> Regression test for Bug A from `doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`: a method call on an enum value retrieved from a struct field crashed/failed because `interpreter_method/mod.rs` only consulted the local `enums` map when looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the lookup silently fell through and the interpreter produced a "method not found" error (or crash).

<!-- sdn-diagram:id=enum_field_method_call_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=enum_field_method_call_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

enum_field_method_call_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=enum_field_method_call_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Enum-Field Method Call Regression

Regression test for Bug A from `doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`: a method call on an enum value retrieved from a struct field crashed/failed because `interpreter_method/mod.rs` only consulted the local `enums` map when looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the lookup silently fell through and the interpreter produced a "method not found" error (or crash).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #INTERP-ENUM-FIELD-METHOD |
| Category | Interpreter |
| Difficulty | 2/5 |
| Status | Regression |
| Source | `test/01_unit/compiler/interpreter/enum_field_method_call_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Regression test for Bug A from
`doc/08_tracking/bug/memory_capabilities_interpreter_crashes_2026-06-11.md`:
a method call on an enum value retrieved from a struct field crashed/failed
because `interpreter_method/mod.rs` only consulted the local `enums` map when
looking up enum body methods, never `GLOBAL_ENUMS`.  When the enum's definition
was registered only in `GLOBAL_ENUMS` (cross-module or block-scoped), the
lookup silently fell through and the interpreter produced a "method not found"
error (or crash).

The fix adds a `GLOBAL_ENUMS` fallback probe in the `Value::Enum` method
dispatch path, mirroring the three-tier lookup used in
`interpreter_call/mod.rs` and `interpreter/expr/calls.rs`.

These tests exercise:
1. Plain enum-on-its-own method call (baseline).
2. Enum value stored in a struct field — method called on the retrieved value.
3. Nested: struct field holds an enum; inner method returns a string; checked
   with `.to_equal()`.

## Scenarios

### enum-field method call — interpreter regression

#### calls a method on a standalone enum value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val k = CapKind.Read
val name = k.label()
expect(name).to_equal("read")
```

</details>

#### calls a method on an enum value stored in a struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = CapEntry(kind: CapKind.Write)
val k = entry.kind
val name = k.label()
expect(name).to_equal("write")
```

</details>

#### calls a method via temp var after field access

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entry = CapEntry(kind: CapKind.Exec)
val k = entry.kind
expect(k.label()).to_equal("exec")
```

</details>

#### round-trips all three variants via struct field

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = CapEntry(kind: CapKind.Read)
val w = CapEntry(kind: CapKind.Write)
val e = CapEntry(kind: CapKind.Exec)
val rk = r.kind
val wk = w.kind
val ek = e.kind
expect(rk.label()).to_equal("read")
expect(wk.label()).to_equal("write")
expect(ek.label()).to_equal("exec")
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
