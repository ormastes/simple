# BUG: native backend segfaults on class array-field mutation via .push() or index-assignment

- **Date:** 2026-07-17
- **Status:** open
- **Area:** compiler native codegen (class field access + array mutation)
- **Severity:** high (segfault / runtime crash)

## Symptom

Compiled native-build segfaults or produces corrupted reads when a class method
mutates an array field directly via:
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

Any compiled class method that directly mutates a field array (native-build
codegen, LLVM or Cranelift backends).
