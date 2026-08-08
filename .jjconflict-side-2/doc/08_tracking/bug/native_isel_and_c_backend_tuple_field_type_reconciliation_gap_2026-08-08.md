# Native isel lanes + C backend: tuple/struct field type reconciliation

- **ID:** native_isel_and_c_backend_tuple_field_type_reconciliation_gap_2026-08-08
- **Status:** C backend — FIXED (static-verified, native-run pending build slot). Native isel lanes (x86_64/aarch64/riscv64/riscv32) — pointer fields OK as-is; float fields open, blocked on a much larger register-class gap (see below).
- **Related:** `native_pushed_tuple_into_empty_literal_list_unboxed_2026-08-02` gap (c), fixed for the LLVM lane in `64c46989bde` (`src/compiler/70.backend/backend/_MirToLlvm/aggregate_intrinsics.spl` `translate_get_field`/`store_field_bits`/`load_field_bits`, ~line 176-329).

## Trigger

A higher-model review of `64c46989bde` (LLVM-lane fix) asked whether the
native isel lanes and the C backend perform the same `dest_ty`-keyed
reconciliation of a loaded tuple/struct field (ptr → cast/inttoptr, float →
bit-preserving reinterpret) or whether they emit a raw-word load with no
reconciliation, reproducing the "tuple field access returns a raw
pointer/word" bug on those lanes only.

## Findings per lane

### C backend (`src/compiler/70.backend/backend/_CBackendTranslate/instruction_lowering.spl`)

**Before this change:** DEFECTIVE on both the write side (`Aggregate`) and
read side (`GetField`/`SetField`).

- `Aggregate` stored every field via `(int64_t)field_val` — for a `double`/
  `float` operand this is a C++ *numeric* conversion (truncates the value to
  the nearest representable integer), not a bit-preserving reinterpret. The
  LLVM lane's `store_field_bits` explicitly avoids exactly this (`bitcast`,
  "never `fptosi`").
- `GetField` read the raw int64 word straight into `dest_name` via
  `emit_assign` with no cast. For a `double`/`float` dest, C++ applies the
  inverse numeric conversion (int64 value → double value), which does not
  recover the original float — corrupted value, not merely a raw pointer.
  For a pointer-typed dest (`void*` or `Foo*`), assigning a bare `int64_t` to
  a pointer variable **with no cast is not valid C++** (no implicit
  int→pointer conversion) — this path would fail to *compile*, not just
  misbehave, whenever a struct/tuple field of pointer type was read.
- `SetField` had the same two gaps in reverse (storing a float value or a
  pointer value into the `int64_t*` slot with no cast — the pointer case
  again would not compile).

**Fix landed:** mirrors the LLVM lane's `dest_ty`-keyed reconciliation:
  - Float fields (`Aggregate` write, `GetField` read, `SetField` write) go
    through a same-size typed temp + `memcpy` bit-reinterpret (C++ has no
    `bitcast`; `memcpy` is the standard well-defined bit-reinterpret and
    `<cstring>`/`<string.h>` is already `#include`d by every C-backend
    output path).
  - Pointer-typed `GetField` reads get an explicit `(dest_ty)(...)` cast,
    mirroring the LLVM lane's `inttoptr` branch.
  - All other (integer/bool) fields keep the pre-existing plain
    load/store — unchanged, matches the LLVM lane's default branch.

  Diff: `git show <commit>:src/compiler/70.backend/backend/_CBackendTranslate/instruction_lowering.spl` — search `Aggregate(dest, kind, operands)` / `GetField(dest, base, field)` / `SetField(base, field, value)`.

  **Verification status: static-verified only (source-level, matches the
  LLVM lane's documented semantics and the existing `CTypeMapper`/`CIRBuilder`
  APIs used elsewhere in the same file). Native-run verification (actually
  compiling generated C++ and executing a tuple-with-float/tuple-with-ptr
  program through the C backend) is deferred — it requires an actual
  `--target=c`/native build+link+run pass, which was out of scope for this
  session (disk headroom / no-cargo-build constraint).**

### Native isel lanes (`src/compiler/70.backend/backend/native/isel_{x86_64,aarch64,riscv64,riscv32}.spl`)

All four `isel_get_field` implementations (`isel_get_field` x86_64 line 388,
`a64_isel_get_field` aarch64 line 530, `rv_isel_get_field` riscv64 line 551,
`rv32_isel_get_field` riscv32 line 503) do a single machine load
(`MOV_REG_MEM`/`LDR`/`LD`/`LW`) of the field word into a general-purpose
vreg, with **no per-field type dispatch at all** — no `dest_ty` parameter is
even threaded into these functions (compare to the LLVM lane's
`translate_get_field(dest, base, field)`, which looks up
`self.get_local_type(dest_id)` internally).

This is **not a narrow, isolated GetField gap** like the LLVM/C-backend one:
grep across all four isel files shows **zero occurrences** of
XMM/FMOV/FLD/FSD/float-register-class machinery anywhere. `isel_binop`,
`isel_const`, `isel_copy`, `isel_aggregate`, etc. are all single-GPR-class,
integer-only. There is no float value representation on any of these four
lanes to reconcile a `GetField` result *into* — arithmetic on a loaded float
field would immediately re-corrupt via `IMUL`/`ADD`/etc. integer ops on the
very next instruction, regardless of what `isel_get_field` did.

- **Pointer fields: NOT a bug.** At the native-isel machine level there is
  no separate SSA "ptr" vs "i64" type the way LLVM IR enforces one — a
  register is an untyped bit pattern, and a raw 8-byte load of a pointer's
  bits IS the pointer; no `inttoptr`-equivalent instruction exists or is
  needed. (Separately: none of the four lanes tag/steal bits from aggregate
  base pointers the way the LLVM lane's `untag_aggregate_base_ptr` does —
  `isel_aggregate` computes a raw stack address via `LEA`/`ADD`, so there is
  nothing to untag on this lane either.)
- **Float fields: real gap, but not independently fixable.** Landing a
  `dest_ty`-aware branch in `isel_get_field` alone (e.g. emitting a
  hypothetical `MOVSD` into an XMM vreg) would require a parallel float
  register class in the vreg allocator, `isel_binop`/`isel_const`/
  `isel_copy`/calling-convention float-arg passing, etc. across all four
  files — none of which exists today. A GetField-only patch would be
  cosmetic (the loaded value still has nowhere correct to go) and was not
  attempted. **Root cause: these four native isel backends have no float
  support at all, not a GetField-specific reconciliation gap.** Filing this
  as the blocking gap rather than guessing at a partial fix.

## Verdict summary

| Lane | Ptr field | Float field |
|---|---|---|
| LLVM (`_MirToLlvm`) | Fixed in `64c46989bde` | Fixed in `64c46989bde` |
| C backend (`_CBackendTranslate`) | Fixed this session | Fixed this session |
| native isel x86_64/aarch64/riscv64/riscv32 | Correct as-is (no typed-value model to reconcile against) | Open — blocked on adding a float register class to all four lanes (out of scope; not a narrow GetField fix) |

## Next step

File/track "native isel backends have no float register class" as its own
follow-up if float-typed tuple/struct fields on the native-isel (non-LLVM,
non-C) backend path are in scope for near-term work; do not attempt a
GetField-only patch there.
