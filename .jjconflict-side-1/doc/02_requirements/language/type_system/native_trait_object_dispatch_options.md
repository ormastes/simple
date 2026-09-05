# Decision: trait-typed receivers on the native lane — options

- **Date:** 2026-08-09
- **Status:** OPEN — needs a human policy call. Blocks a located compiler fix.
- **Blocked bug:** `doc/08_tracking/bug/native_trait_typed_return_receiver_unresolved_2026-08-09.md`
- **Not blocked by this (fix independently):**
  `doc/08_tracking/bug/native_option_unwrap_receiver_unresolved_2026-08-09.md`
  — concrete class via a single `Option<T>` type argument, one correct answer,
  no policy question.

## The situation, in four facts

1. **The native lane has no dynamic dispatch at all.** No vtable, no trait
   object, no fat pointer. Verified by symbol sweep over
   `src/compiler/70.backend/`, `25.traits/`, `60.mir_opt/`, `40.mono/`
   (476 files; control search matched 334, so the sweep was live): 5 hits, of
   which 4 are an ARM interrupt vector table in `crt0.s` and 1 is a comment.
   `owner_has_vtable` exists **only** in the Rust seed
   (`src/compiler_rust/compiler/src/codegen/instr/mod.rs`), with no pure-Simple
   counterpart. (An earlier report searched `src/compiler/60.codegen/`, which
   does not exist; that half of its evidence was vacuous.)
2. **Every working trait call today is static devirtualization** — the
   Unresolved arm's owner recovery through `struct_value_syms` at
   `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2505-2546`
   rewrites the call to a concrete `"{Class}::{method}"` symbol.
3. **MIR has no trait→impls index.**
   `src/compiler/50.mir/_MirLowering/module_lowering.spl:1127-1163` walks
   `module.impls` and indexes methods **only by target type**, discarding
   `impl_def`'s trait reference. So when the recovered owner name turns out to
   be a trait, lowering cannot ask "who implements this?"
4. **Measured receiver matrix** (from the bug doc, `native-build`, each shape
   built in isolation):

   | Shape | Result |
   |---|---|
   | trait-typed LOCAL var | PASS |
   | trait-typed struct FIELD | **PASS** — the widely-repeated claim that this fails is FALSE |
   | trait-typed OPTIONAL field | builds, **silently wrong** (`self.prefix` reads empty) |
   | trait-typed RETURN value | **HARD FAIL** `unresolved method call` |

Whatever is chosen, the optional-field row must not stay as it is. A silent
wrong answer is worse than a build error, and it is the only row that is
currently fail-open.

## Options

### 1. Single-impl devirtualization only

Build `trait_impl_syms["{Trait}::{method}"] -> [method_id]` in the
`module.impls` loop; in the Unresolved arm, when the recovered owner is a
trait with exactly **one** impl, devirtualize to it.

- **Cost:** small; two edits, both in files already read (see the bug doc's fix
  recipe steps 1–2).
- **Unblocks:** the trait-typed return shape today, in real programs.
- **Risk — the capability cliff:** soundness depends on a whole-program
  property nobody declared. A user writes `fn make() -> Greeter`, it compiles
  and ships. Months later someone in an unrelated module adds a second
  `impl Greeter for X`. The original file, unchanged, now fails to build — and
  the error points at the *call site*, not at the new impl that caused it. The
  user's mental model ("adding a type is additive") is simply wrong, with no
  warning at the point of the breaking edit.
- **Forecloses:** nothing structurally, but it establishes "one impl = trait
  objects work" as de-facto semantics that users will depend on, making a later
  restriction a breaking change.
- **Affects:** every native-lane user of traits. **Reversible:** yes in code,
  no in expectation.
- **Evidence it works:** shape C of
  `test/fixtures/native_trait_receiver_resolution/` builds and prints
  `return C`; plus a two-impl negative fixture that must fail with a diagnostic
  naming the trait and the impl count — not a bare `unresolved method call`.

### 2. Real vtable / trait-object dispatch in the native lane

- **Requires:** a trait→impl index in MIR (same as option 1's first half); a
  stable vtable layout per trait with a method-slot ordering that survives
  separate compilation; a representation for a trait-typed value that carries
  both data and vtable pointer (fat pointer or boxed header) — which changes
  ABI, struct field layout, and every place a trait-typed value is stored,
  passed, or returned; interaction with monomorphization in `40.mono/`
  (deciding which calls stay static and which go virtual); and codegen support
  in `70.backend/` where none exists.
- **Size:** the largest of the four by a wide margin — a new dispatch mechanism
  plus a representation change, not a patch. No estimate is offered here
  because none was measured.
- **Unlocks:** trait objects generally — heterogeneous collections, plugin
  boundaries, and the SimpleOS driver-trait shapes that keep getting worked
  around. Would also make the optional-field row correct by construction.
- **Tension with repo rules:** "NEVER over-engineer" argues against doing this
  speculatively; it is only justified if trait objects are a declared language
  goal. **Reversible:** effectively no.
- **Evidence it works:** the full receiver matrix passes *including* a
  two-impl program where the concrete type is chosen at runtime and both
  branches produce correct output.

### 3. Reject trait-typed receivers at the type level, in the native lane

Make it a clear, early compile-time error with a good message and a documented
list of supported receiver shapes, instead of an `unresolved method call`
leaking out of MIR.

- **Cost:** cheapest honest option. The diagnostic belongs upstream of MIR so
  it names the declaration, not the lowering.
- **Cost in expressiveness:** `fn make() -> SomeTrait` becomes illegal on the
  native lane; users write concrete return types or generics. Note the
  interpreter handles all these shapes fine, so this splits the two lanes'
  accepted languages — that divergence must be documented, not implied.
- **Forecloses:** nothing — option 2 remains open later, and this makes the
  eventual capability addition purely additive.
- **Affects:** anyone whose native-lane code uses trait-typed returns/fields.
  **Reversible:** yes, cleanly.
- **Evidence it works:** each matrix row either compiles correctly or fails
  with a message naming the trait, the receiver, and the supported
  alternatives. Critically, the **optional-field row must move from silently
  wrong to rejected** — this option is the only cheap one that fixes that row.

### 4. Hybrid — devirtualize when provably single-impl, diagnose clearly otherwise

Option 1 with the cliff converted from a mystery into a diagnostic: when the
trait has ≥2 impls, emit "trait `Greeter` has 3 impls; native lane cannot
dispatch dynamically — use a concrete type or generics", listing the impls.

- **Cost:** option 1 plus one good error message (already step 3 of the bug
  doc's fix recipe).
- **Residual risk:** the cliff is still a cliff — the program still stops
  compiling when someone adds an impl elsewhere. It just becomes
  *understandable* rather than baffling. That is a real improvement and an
  honest one, but it is not a fix for the underlying non-compositionality.
- **Affects / reversible:** as option 1.
- **Evidence:** as option 1, plus the two-impl fixture asserting the exact
  diagnostic text (sabotage-proved, per the AOT-lane fence convention).

## The optional-field row, in every option

Options 1, 3 and 4 all leave the trait-typed **optional** field silently
returning empty data unless it is handled deliberately. Whichever is chosen,
that shape must end up either correct or rejected — never building-and-wrong.
In option 3 and 4 it is naturally rejected; in option 1 it needs an explicit
decision or it slips through unchanged. It should be fenced by a `scripts/check/`
script driving `native-build`, since no `*_spec.spl` can observe this lane.

## Recommendation

**Option 4 now, option 3's honesty as the fallback, option 2 only if trait
objects are a declared language goal.** Option 4 is a small, reversible change
that unblocks today's real code, and its failure mode is a message a user can
act on rather than a mystery. It must ship together with the optional-field row
being made non-silent — that part is not optional in any scenario.

## The question for the human

**Is dynamic dispatch on trait objects a supported feature of Simple's native
lane, or is the native lane deliberately a statically-dispatched subset?**

- If *supported* → option 2, and it should be planned as a representation
  change, not appended to a bug fix.
- If *a static subset* → option 4 now and document the restriction, so the
  ≥2-impl diagnostic reads as a stated language rule rather than a compiler
  shortfall.

A secondary question, only if option 4 is chosen: should the ≥2-impl case be an
error, or a warning plus a runtime trap? (Recommendation: error. A runtime trap
reintroduces the fail-open problem this doc exists to close.)
