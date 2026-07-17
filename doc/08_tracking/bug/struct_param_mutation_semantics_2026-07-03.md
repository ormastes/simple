# Struct/class param mutation semantics — decision doc (task #35)

- **Status:** OPEN — decision needed before implementing a fix
- **Discovered:** 2026-07-03 (task #35 investigation)
- **Area:** language semantics — value vs reference passing for `struct`/`class` params; divergence between interpreter and JIT/compiled backend
- **Severity:** High — silently corrupts any builder/accumulator/mock pattern that mutates an argument (hal_smp IPI mock counters, DOM decoration in `simple_browser_page.spl`)

## Task framing vs. evidence (the conflict)

Task #35 was framed as "the interpreter drops self-mutation in free functions," with
`hal_smp` (IPI mock counters read 0) as a known repro. Investigation found the
**opposite of that framing holds today**: the interpreter is the side that
*preserves* mutation; it is the **JIT/compiled backend** that silently drops it.
The task's premise should not be taken as already-confirmed root cause — see
Evidence below. This doc exists so that decision is made explicitly rather than
silently, per task instructions.

## Documented claim

- `test/03_system/feature/usage/structs_spec.spl` line 45 (mirrored to
  `doc/06_spec/03_system/feature/usage/structs_spec.md`): **"Structs are value
  types (copied by default)"**. This applies to `struct`, not `class` — no
  document anywhere claims `class` instances are value types.
- `doc/04_architecture/.../memory_model_implementation.md` ("MEMORY_MODEL
  IMPLEMENTATION_SUMMARY"), capability model:
  ```
  x: Data          # Shared (T) - read-only, aliasable
  x: mut Data      # Exclusive (mut T) - single writer
  x: ~Data         # Isolated (~T / iso T) - unique + transferable
  x: @Data         # Atomic RC (@T / Arc) - thread-safe ref-counted
  ```
  A plain (non-`mut`) param is documented as read-only/shared; `mut T` is the
  documented spelling for "caller observes the mutation."
- `me` (self-mutation) is **not documented at all** in
  `doc/07_guide/quick_reference/syntax_quick_reference.md` — it is only
  discoverable via the compiler's own HIR error text ("cannot modify self in
  immutable fn method '...'. Use `me` instead of `fn` to allow self mutation").
  This is a separate, standing documentation gap, filed here for visibility.
- No document states `class` param default semantics explicitly. The existing
  open bug `doc/08_tracking/bug/browser_engine_free_fn_arg_mutation_lost_2026-06-30.md`
  asserts (as its "Proper fix") that **class instances passed as function
  arguments must be passed by reference "consistently between the interpreter
  and the compiled/JIT path"** — i.e. it already treats class-by-reference as
  the intended design, and treats the JIT's mutation loss as the bug to fix,
  not the interpreter's mutation-preservation.

## Compiled / run behavior (verified via deployed `bin/simple`, single-file scripts)

| Case | Plain-language description | Static/HIR gate | Executed value |
|---|---|---|---|
| 1 | Free fn, plain (`fn`) param, `s.field = x` | **Rejected** (`[W1006]`: mutation requires `mut` capability on the receiver) → falls back to interpreter | interpreter performs the mutation anyway; caller sees it |
| 2 | Free fn, `mut` param, `s.field = x` | Accepted, compiles clean (no fallback) | mutation visible to caller |
| 3 | Method declared `fn`, mutates `self.field` | **Rejected** ("cannot modify self in immutable fn... use `me`") → falls back to interpreter | interpreter performs the mutation anyway; caller sees it |
| 3b | Method declared `me`, mutates `self.field` | Accepted, compiles clean | mutation visible to caller |

So for **structs**, the compiler's static enforcement (`[W1006]`) matches the
documented value-type spec, and it's working as intended: cases 1/3 SHOULD be
rejected, and are. The interpreter fallback path (which doesn't enforce the
capability rule and just aliases/mutates in place) is the one behaving
inconsistently with the static spec for structs — but this is masked in
single-script `bin/simple run` because a JIT rejection silently falls back to
the interpreter instead of surfacing as a hard error to the user.

For **classes** (no documented value-type claim, and an existing bug doc
already asserting reference semantics is intended), the situation inverts: the
interpreter's "mutate in place, visible to caller" behavior is the *desired*
one, and it is the **JIT/compiled backend that drops the mutation** — matching
`browser_engine_free_fn_arg_mutation_lost_2026-06-30.md` exactly, and confirmed
independently here via `hal_smp.spl`:

```spl
class SbiMockSmp:
    var probe_ext_results: [(u64, bool)]
    var ipi_calls: [(u64, u64)]
    var hart_start_calls: [(u64, u64, u64)]

fn hal_smp_ipi_send_with_mock(mock: SbiMockSmp, target: u32, vector: u32):
    ...
    mock.ipi_calls.push((target as u64, hart_mask))   # src/os/kernel/arch/riscv64/hal_smp.spl:140
```

`mock: SbiMockSmp` is a **plain param, no `mut`** — a class instance. The spec
in `test/01_unit/os/kernel/arch/riscv/hal_smp_spec.spl` (e.g. line 118:
`expect(mock.ipi_calls.len()).to_equal(1)`) then reads the caller's copy of
`mock` and expects to observe the mutation performed inside
`hal_smp_ipi_send_with_mock`. This currently passes only because these unit
specs run under the interpreter path (or a path where the JIT successfully
lowers it in a single-module context); it is at risk the moment this code (or
similarly-shaped code) is compiled/JIT'd across a module boundary, per the
`browser_engine` bug's confirmed cross-module-loss pattern.

## Recommendation

This is two distinct, independently actionable issues, not one:

1. **Struct value-type enforcement gap (interpreter under-enforces):** the
   interpreter should also apply the `mut`-capability HIR check for `struct`
   params/methods (cases 1 and 3), rather than silently falling back and
   aliasing. Silently falling back to a laxer interpreter semantics whenever
   JIT lowering fails is a general hazard beyond this bug (masks type/capability
   errors as passing runs) — worth a broader follow-up, but the immediate ask
   here is: don't let JIT-rejected struct mutation "work" via interpreter
   fallback.
2. **Class reference-type propagation gap (JIT/compiled backend under-delivers):**
   this is the `browser_engine_free_fn_arg_mutation_lost_2026-06-30.md` bug,
   already filed and OPEN. `hal_smp`'s reliance on `mock: SbiMockSmp` (plain
   param) mutating correctly is presently only safe because these specs
   exercise the interpreter/single-module path; it is exactly the shape at
   risk under the existing bug. Fix location is the compiled/JIT backend's
   argument-passing for class instances (`src/compiler_rust/compiler/src/**`
   codegen/lowering, or the equivalent `.spl` HIR lowering path once
   self-hosted) — **out of scope for this pass** (task #35 restricts changes to
   `src/app/interpreter/**`; compiler/compiler_rust paths are explicitly
   excluded).

No interpreter-engine code was changed in this pass: the interpreter's
observed behavior (mutate-in-place, visible to caller) is *already* the
correct/intended behavior for the `hal_smp` class-instance repro, matching the
pre-existing, still-open `browser_engine_free_fn_arg_mutation_lost_2026-06-30.md`
recommendation. Changing the interpreter to instead copy class-instance params
(to "match struct value semantics") would newly break `hal_smp` and any other
class-mutation-based test that currently passes, for no spec-mandated reason —
classes are not documented as value types anywhere in this codebase.

The `hal_smp` mock helper signatures (`mock: SbiMockSmp`, no `mut`) additionally
don't match the *documented* explicit-capability style (`mock: mut SbiMockSmp`)
seen in the memory-model doc's own example (`fn increment(counter: mut i64)`).
Tightening those signatures to say `mut SbiMockSmp` would make the mutation
capability explicit and JIT-safe (per case 2/3b above) without depending on
class-default-reference behavior at all — a low-risk mitigation available to
whoever picks up the compiled-backend fix, independent of resolving the
class-vs-struct default-semantics question.

## Affected specs / follow-up references

- `test/01_unit/os/kernel/arch/riscv/hal_smp_spec.spl` (`SbiMockSmp` — class
  param mutation across free fns; currently passing, at risk per above)
- `src/os/kernel/arch/riscv64/hal_smp.spl` (mock helpers `hal_smp_cpu_start_with_mock`,
  `hal_smp_ipi_send_with_mock`, `hal_smp_ipi_broadcast_with_mock`)
- `doc/08_tracking/bug/browser_engine_free_fn_arg_mutation_lost_2026-06-30.md`
  (the actual open bug for the compiled-path class-mutation loss; this doc's
  "Proper fix" section is the action item, not anything in `src/app/interpreter/**`)
- `x86_64_interrupt` "ABI bridge" specs mentioned in the task brief as possibly
  related: searched: no direct struct/class param-mutation coupling found in
  this pass; flagging for a follow-up look if a similar mutation-loss symptom
  surfaces there, but not confirmed related here.
- Documentation gap: `me` self-mutation keyword and `class` vs `struct` default
  param-passing semantics are both undocumented in
  `doc/07_guide/quick_reference/syntax_quick_reference.md`; worth a follow-up
  doc patch independent of the code fix.

## Verification limit

No `src/app/interpreter/**` changes were made in this pass (none were
warranted — see Recommendation). The compiled/JIT-backend fix
(`browser_engine_free_fn_arg_mutation_lost_2026-06-30.md`) remains open and
requires changes outside this task's scope (`src/compiler_rust/**` /
compiler HIR lowering), which needs a stage4/seed rebuild + deploy cycle to
verify end-to-end — explicitly out of scope for this pass per task
instructions.

## Verification (2026-07-17)

Runtime repro at tip 9feac6ef6e5:

- **Struct case** (`fn` param mutates field): JIT rejects with `[W1006]` as
  documented, falls back to interpreter. Interpreter now prints `n=0` (mutation
  NOT visible to caller), not the 2026-07-03-claimed `n=1`. **Struct/interpreter
  half no longer reproduces as originally described** — value-type semantics now
  enforced consistently even under interpreter fallback.

- **Class case, interpreter** (`bin/simple run`): Mutation visible, `n=1`.
  Matches documented reference semantics.

- **Class case, compiled** (`bin/simple native-build` to binary): Mutation LOST,
  output `n=0`. **Class/compiled-backend half STILL-REPRODUCES** exactly as filed.
  Confirmed the class-mutation-loss defect remains the real open issue, matching
  `browser_engine_free_fn_arg_mutation_lost_2026-06-30.md`.

**Status:** STILL-REPRODUCES (class/compiled half). Struct/interpreter half no
longer reproduces as written.
