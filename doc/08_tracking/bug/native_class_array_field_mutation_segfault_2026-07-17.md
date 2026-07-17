# BUG: native backend segfaults on class array-field mutation via .push() or index-assignment

- **Date:** 2026-07-17
- **Status:** source fix implemented; execution pending
- **Area:** compiler native codegen (class field access + array mutation)
- **Severity:** high (segfault / runtime crash)

## Symptom

Compiled native-build segfaults or produces corrupted reads when code mutates a
class instance's array field directly via:
- `.push(...)` call on the field: `self.<array-field>.push(value)`
- Index-assignment on the field: `self.<array-field>[i] = value`

Index-assignment also silently produces wrong reads post-mutation.

Free-function context or mutation of a plain local array (not a class field)
works fine.

## Minimal repro

**Segfault on `.push()` (probe04b_class_mut.spl, probe04d_class_push_local.spl,
probe04e_class_push_nonempty.spl):**

```simple
class Container:
    var items: [i64]

fn mutate(c: Container):
    c.items.push(42)      # SEGFAULT in native-build path

fn main() -> i32:
    var c = Container(items: [])
    mutate(c)
    0
```

**Probe comparison (all via `bin/simple native-build`, compiled to binary):**
- `probe04b_class_mut.spl`: crash/segfault
- `probe04d_class_push_local.spl`: local array push works fine
- `probe04e_class_push_nonempty.spl`: nonzero array + push → segfault

## Cross-reference

Closely related to the class-mutation issue in
`doc/08_tracking/bug/struct_param_mutation_semantics_2026-07-03.md`
(see its "Side finding" section), but specifically targeting array-field access
rather than scalar fields. The scalar mutation loss in that doc is silent
(wrong value); this bug produces crashes.

## Workaround

- Avoid direct `.push()` on class array fields inside compiled methods
- Bind the result of field access to a local first if mutation is needed
- For index-assignment, ensure reads are re-verified post-assignment

## Affected code paths

Any compiled access that directly mutates a class field array (native-build
codegen, LLVM or Cranelift backends).

## Source fix and regression coverage

The source fix restores the missing class-field metadata and projection
provenance at the MIR boundary:

1. HIR/MIR aggregate prescans register declared `HirClass` field order, nested
   type name, representation, and array element type in the existing
   name-keyed metadata used for field lowering, while preserving declaration
   order and existing collision/shadow rules.
2. Mutating-method `Field` prelowering mirrors ordinary field projection after
   `emit_get_field`: class/nested values retain `struct_value_syms`; array
   fields retain `runtime_array_locals` and `runtime_value_locals`; named array
   elements retain `array_element_struct_syms`.

`scripts/check/check-native-seed-parity.shs` adds the strict dual-backend
`class_array_field_mutation` case. It pushes into the non-first field
`Container.items`, assigns an indexed element, rereads length and values, and
confirms the same array handle is visible through an alias captured before
mutation while the leading scalar field remains unchanged. The fixed normalized
expected output is `2742274299` on LLVM and Cranelift. Execution is pending; this
does not claim broader class-reference or struct-copy semantics are resolved.
