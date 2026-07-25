# BUG: native backend segfaults on class array-field mutation via .push() or index-assignment

- **Date:** 2026-07-17
- **Status:** NOT REPRODUCIBLE under `bin/simple native-build` (re-verified again post-cherry-pick onto tip 9b6f34f9b75, after 71a4d0f21e4/dd848072025/96856488b49 all landed); the segfault DOES reproduce under `bin/simple run`, but that command executes the bootstrap Rust seed's own OWN Cranelift JIT (`simple_compiler::codegen::jit`/`src/compiler_rust/compiler/src/codegen/instr/*.rs`), a completely separate implementation from the pure-Simple self-hosted compiler (`src/compiler/*.spl`) that native-build interprets. Root cause there (confirmed via gdb backtrace + `SIMPLE_DUMP_MIR`): the seed's `StructInit` MIR instruction is emitted with `field_offsets`/`field_types` describing an extra per-CLASS header slot (offset 0) that `field_values` never supplies a value for, so every field's value shifts down one slot and the true LAST field's storage is left uninitialized garbage. Fixing that is out of scope here (it lives in `src/compiler_rust`, which is bootstrap-only per project rules — "fix it in pure-Simple," not the seed). See "2026-07-17 re-verification" below for the full evidence trail.
- **Area:** compiler native codegen (class field access + array mutation)
- **Severity:** high (segfault / runtime crash) — but only in the bootstrap-seed JIT path, not in native-build

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

## Source fix and regression coverage landed by a parallel lane (dd848072025)

A parallel lane (commit dd848072025, "fix(mir): preserve class array field
metadata") independently restored class-field metadata and projection
provenance at the MIR boundary — `register_composite_field_metadata` now
registers declared `HirClass` field order, nested type name, representation,
and array element type (by name/sentinel, see the sibling bool-array-element
doc for the primitive-element gap this still left, closed by this lane's own
`struct_field_array_elem_type` addition), and mutating-method `Field`
prelowering (`remember_field_projection_provenance`) preserves
`struct_value_syms`/`runtime_array_locals`/`runtime_value_locals`/
`array_element_struct_syms` across a field projection. `scripts/check/
check-native-seed-parity.shs` adds a strict dual-backend
`class_array_field_mutation` case for this. That commit's own note was
"Execution is pending; this does not claim broader class-reference or
struct-copy semantics are resolved" — the re-verification below (re-run again
after cherry-picking onto tip 9b6f34f9b75, with dd848072025 and 96856488b49
both already landed) is that execution, and confirms native-build was already
correct for this doc's own repro shapes independent of that work landing.

## 2026-07-17 re-verification (fix lane s16, worktree wt_s9, tip 985885cb314; re-confirmed post-cherry-pick onto 9b6f34f9b75)

Re-ran this doc's exact probe shapes (`probe04b_class_mut.spl`,
`probe04e_class_push_nonempty.spl`, plus a fresh two-array-field/two-method
class mirroring `probe06_debug2.spl`, and a method-based push+index-assign
variant) through **`bin/simple native-build --entry <probe> -o <bin> --clean`**
followed by running the produced binary — the literal reproduction command this
doc's "Affected code paths" section names. None segfault; all print correct,
semantically-expected values:

- `probe04b_class_mut.spl` (free-fn `mock.calls.push(v)`): `len=1` (correct:
  `[]` + push(42))
- `probe04e_class_push_nonempty.spl` (`mock.calls.push(42)` on `[1]`): `len=2`
  (correct)
- Two-array-field class with `me` methods doing push+index-assign on both
  fields (`Band.alloc_page()`/`Band.mark_valid()`, mirrors
  `probe06_debug2.spl`): `p=0 pages_len=1 valid_len=1 before=0 after=1` — all
  correct, no crash
- A fresh method-based push + index-assign probe (`Container.add_item`/
  `Container.set_item` on an `[i64]` field): `len=3 v0=99 v2=42` — correct

Then reproduced the SAME shapes via `env -u SIMPLE_BOOTSTRAP bin/simple run
<probe>` (this doc's implicit "oracle"/reference command) and got genuine
SIGSEGVs — confirmed via `gdb --batch -ex run -ex bt` that the crash is inside
JIT-generated machine code (frame `#0` is an unsymbolicated address reached
through `JitCompiler::call_i64_void`), and via `SIMPLE_DUMP_MIR=main` that the
JIT's own `StructInit` instruction for a one-field class emits
`struct_size: 16, field_offsets: [0, 8], field_types: [TypeId(14), TypeId(17)]`
but `field_values: [VReg(4)]` (only ONE value for TWO declared slots) — the
real array/scalar value lands in the phantom offset-0 header slot and the
field actually read (offset 8) is uninitialized. This is a Rust-seed-only
defect (`src/compiler_rust/compiler/src/mir/lower/lowering_expr_struct.rs` /
`src/compiler_rust/compiler/src/codegen/instr/*.rs`), unrelated to the
pure-Simple `src/compiler/*.spl` pipeline that `native-build` interprets.

**Classification: BLOCKED as originally scoped (native-build), because it
does not reproduce there.** The underlying (real, confirmed) segfault lives
in the bootstrap Rust seed's own JIT compiler, which is explicitly
bootstrap-only and out of scope for a pure-Simple fix per project rules. No
`src/compiler/*.spl` change was made for this doc.

Note on "must match the seed oracle": for this bug specifically, the
prescribed oracle command (`bin/simple run`, i.e. the seed's JIT) is itself
the ONLY place the segfault happens — the sibling bug doc
(`native_bool_array_element_interpolation_special_garbage_2026-07-17.md`) has
the same property (the oracle prints `<special:N>` garbage where native-build
now prints the correct value). "Native matches oracle" is unsatisfiable by
construction here: native-build is strictly MORE correct than the oracle for
both docs' repro shapes, not merely different. This should not be read as
native-build failing to match a reference — the reference itself is broken.

If this needs fixing, it should be re-filed against `src/compiler_rust` (seed JIT) rather than
"native codegen."
