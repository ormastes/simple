# Trait conformance check is name-only — arity and parameter types are never compared

- **Status:** ARITY ARMED / TYPES STILL OPEN — mechanism confirmed; census
  complete, re-run by a pure-Simple checker that scores **3,928 Tier-A method
  pairs at 0 arity drift**, and the census's residual unknowns (the 20
  unscorable pairs and the 40 not-found traits) are closed. The **arity**
  comparison is now armed in `interpreter_eval.rs`, with receiver normalisation
  on both sides and accumulate-then-report; see *The check is armed* at the end
  of this file. Parameter **types** are still never compared, and the check
  fires only on the interpreter path — it does not close the JIT nil-sentinel-`3`
  hole (separate lane).
- **Standing gate:** `scripts/check/check-trait-arity.spl` (pure Simple).
- **Found:** 2026-08-04, while closing the `MirTextCodegen` / `MirToLlvm` break (`4670db2d31f2`)
- **Severity:** latent, repo-wide. A trait declaration can disagree with its
  implementer on argument count and the compiler stays silent.

## Summary

`impl <Trait> for <Type>` is accepted whenever the impl defines a method with
the *same name* as each abstract trait method. Nothing compares the parameter
list. A trait may declare `f(a, b)` while its only implementer defines
`f(a, b, c)`; the impl is accepted, and callers written against the trait's
declared 2-arg shape are then wrong in a way the declaration does not reveal.

## The check

`src/compiler_rust/compiler/src/interpreter_eval.rs:985`

```rust
let impl_method_names: std::collections::HashSet<_> =
    impl_block.methods.iter().map(|m| m.name.clone()).collect();

for trait_method in &trait_def.methods {
    if trait_method.is_abstract && !impl_method_names.contains(&trait_method.name) {
        return Err(crate::error::factory::missing_trait_method(
            &type_name, &trait_method.name, trait_name,
        ));
    }
}
```

Three properties follow directly from this code and are all confirmed by probe:

1. **Name-only.** The set is built from `m.name`. `m.params` is never read, so
   arity, parameter names, parameter types and return type are all unchecked.
2. **First-failure-only.** `return Err(...)` inside the loop, so a drift of N
   methods surfaces as N sequential one-method errors — this is why the
   `MirTextCodegen` three-method break read as a one-method problem.
3. **Interpreter-path only.** The check lives in `interpreter_eval.rs`. Under
   the default JIT engine it does not run at all.

The pure-Simple side has an equivalent name-only validator at
`src/compiler/25.traits/trait_impl.spl:120` (`validate_methods`, `self.has_method(method.name)`),
but it has **no callers** anywhere in `src/` — as does
`src/compiler/00.common/error.spl:516` (`missing_trait_method`). The live check
is the Rust one above.

## Probe evidence

Probes in `scratchpad/arity_probes/`. Run with the deployed
`bin/release/x86_64-unknown-linux-gnu/simple`.

| probe | shape | `bin/simple run` (JIT, default) | `SIMPLE_EXECUTION_MODE=interpret` |
|---|---|---|---|
| `p2_control` | trait 3-arg, impl 3-arg, call 3-arg | exit 0, `p2 result=7` | exit 0, `p2 result=7` |
| `p1_trait_arity` | trait declares `f(a,b)`, impl defines `f(a,b,c)`, call `f(1,2)` | **exit 0, `p1 result=6`** | exit 1, `error: semantic: function expects argument for parameter 'c', but none was provided` |
| `p3_plain_underarg` | no trait; 3-arg method, 2-arg call | **exit 0, `p3 result=6`** | exit 1, same arity error |
| `p4_missing_method` | trait declares `g`, impl omits it | **exit 0, `p4 result=3`** | exit 1, `error: semantic: type `C` does not implement required method `g` from trait `T`` |
| `p5_sibling_overload` | sibling class also has a 2-arg `f`; call 2-arg on the 3-arg class | **exit 0, `p5 result=6`** | exit 1, same arity error |
| `p6_selfcall_in_impl` | `self.f("z", 7)` where `f` is 3-arg | **exit 0, `p6 result=10`** | exit 1, `...parameter 'span'...` |

Two independent facts fall out:

- **The trait/impl arity mismatch itself is never reported, in either engine.**
  In `p1` the interpreter's complaint is about the *call site*, not about the
  impl disagreeing with the trait it claims to satisfy. Remove the bad call and
  the mismatched impl is accepted with no diagnostic at all.
- **Under JIT a missing trailing argument reads as the nil sentinel `3`.**
  `p1`/`p3`/`p5` return `1+2+3 = 6`; `p6` returns `7+3 = 10`. That is the same
  sentinel documented in `nil_sentinel_3_forbids_defaulted_int_args`. It is a
  silent wrong value, not a crash and not a nil.
- **The interpreter's call-site arity check is evaluation-time, not static.**
  It fires only when the bad call is actually executed, so a bad call on a cold
  path (as both real ones below were) passes every `bin/simple test` run.

## Instance found and fixed

`translate_function`, trait `MirTextCodegen`:

| site | signature / call | file:line |
|---|---|---|
| trait decl | `me translate_function(name: text, body: MirBody)` | `src/compiler/70.backend/backend/common/mir_text_codegen.spl:22` |
| impl (only implementer) | `me translate_function(name: text, body: MirBody, span: Span)` | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:349` |
| call site | `self.translate_function(name, body)` | `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl:347` |
| call site | `translator.translate_function(... , body)` | `src/compiler/80.driver/driver_bootstrap.spl:479` |

Both call sites are on the flat-bootstrap AOT path. `span` is read only under
`if self.debug_info:` (`core_codegen.spl:502`), and neither bootstrap translator
(`driver_bootstrap.spl:340`, `:456`) calls `enable_debug_info()` — that happens
only in `llvm_backend.spl:282` and `llvm_codegen_adapter.spl:48/93`. So the
under-arity calls were inert *by accident*: nothing read the sentinel.

Fixed by aligning the declaration with the sole implementer and giving both call
sites a real third argument. `driver_bootstrap.spl:479` now passes `fn_.span`,
matching the sibling loop at `core_codegen.spl:303`.
`core_codegen.spl:347` passes `Span.empty()` — flat-bootstrap bodies come from
`MirBody.from_bootstrap_parts`, which carries no function-level span, and
`Span.empty()` has `line: 0`, so `if span.line > 0: span.line else: 1` yields
the same `dbg_line = 1` the nil branch already produced. No behaviour change on
either path.

## Sweep: how widespread is the drift

> **SUPERSEDED — do not quote the numbers in this section.** The sweep's
> "30 drifted pairs across 4 traits" was not the lower bound it claimed to
> be; 3 of its 4 trait families were bare-name resolution artifacts. Kept
> for the record of what was believed and why. See *Census (2026-08-04)*
> below for the corrected figures.

Method: parse every `trait X:` block and every `impl T for Y:` block at column
0 across owned `src/**.spl` (excluding `src/compiler_rust/` and `vendor/`),
accumulate each `me`/`fn` signature across line continuations, drop a leading
`self`/`me` parameter so the `fn f(self, ...)` and `me f(...)` conventions
compare equal, and report name matches whose arity differs.

**Result: 30 drifted method pairs across 4 traits.**

| trait | drifted methods | impls affected |
|---|---|---|
| `BlockDevice` (`src/os/drivers/nvme/block_device.spl:17`) | `read_sector` — declared `(lba: u64, buf_phys: u64) -> Result<bool, text>`, every impl defines `(lba: u64) -> Result<[u8], text>` (return type differs too) | 9 |
| `RenderBackend3D` (`src/lib/nogc_sync_mut/engine/render/backend3d.spl`) | `bind_texture` 3-arg decl vs 2-arg impls; `create_pipeline` 1-arg decl vs 4-arg impls; `end_render_pass` 1-arg decl vs 0-arg impls | 12 classes |
| `RenderBackend` (`src/lib/nogc_async_mut/gpu/engine2d/backend.spl:33`) | `init` 2-arg decl vs 0-arg impls | 2 |
| `MirTextCodegen` | `translate_function` (fixed here) | 1 |

Spot-checked by reading the trait and impl source for `BlockDevice`,
`RenderBackend3D` and `RenderBackend` — all real, none a parser artifact.

**Error modes of this sweep (the 30 is a lower bound, not a census):**

- Only the `impl Trait for Type:` form is matched. The repo also uses
  `impl ClassName: TraitName` (see the comment at `backend3d.spl:70`); those
  blocks are classified inherent and skipped. 552 `impl X for Y` headers exist
  against 5,024 `impl X:` headers, so most impl blocks are not examined.
- Traits are keyed by bare name, so two traits sharing a name in different
  files collide and one shadows the other.
- 158 of the repo's 300 `trait` declarations were parsed; the rest are nested,
  indented, or generic-parameterised in a form the header regex misses.
- Return-type and parameter-type drift is not scored at all — only arity. The
  `BlockDevice` case shows type drift travels with arity drift, so the true
  defect count is at least 30.

Only the `MirTextCodegen` entry is touched by this change. The other 29 are
reported, not fixed: each needs its own owner to decide whether the trait or the
impls are authoritative, and `RenderBackend3D`/`RenderBackend` are live GPU
lanes under active work.

## Recommendation

Do **not** bolt full signature type-checking onto this. The minimal, targeted
fix is at `interpreter_eval.rs:985`: alongside the name-set membership test,
compare `trait_method.params.len()` against the matched impl method's
`params.len()` (after normalising the `self`/`me` receiver) and emit a distinct
error naming both arities. That is a purely additive check on a path that
already walks both signatures, it would have caught all 30 pairs above, and it
costs nothing at runtime.

Two follow-ups worth filing separately:

1. Collect *all* conformance failures for one impl before returning, instead of
   `return Err` on the first. The one-at-a-time reporting turned a three-method
   break into three sequential debugging rounds.
2. `validate_methods` (`src/compiler/25.traits/trait_impl.spl:120`) and
   `missing_trait_method` (`src/compiler/00.common/error.spl:516`) are the
   pure-Simple equivalents and have **no callers**. Either wire them up as the
   self-hosted conformance check — the right place for the arity comparison
   above, per *Fix .spl not Rust* — or delete them; leaving an uncalled
   validator next to a live Rust one invites the next reader to fix the wrong
   copy.

## Census (2026-08-04, supersedes the sweep above)

The sweep above reported **30 drifted pairs across 4 traits** and warned it was a
lower bound. It was not a lower bound — it was mostly **wrong in the other
direction**. Re-run as a full census against a pristine detached worktree at
`f4a4703f0fb`, the real Tier-A number is **2 records, which are one logical
defect duplicated across two identical files**. Three of the sweep's four traits
were bare-name collisions.

### Method

`impl T for Y:` blocks are what the live check at `interpreter_eval.rs:985`
actually gates, so they are scored as **Tier A**. Inherent `impl Y:` blocks are
never seen by that check, but a same-named inherent method on a conforming type
is still a dispatch hazard, so they are scored separately as **Tier B**.

Both tiers are parsed from every `*.spl` in the tree (`src/`, `test/`, all of
it — 35,253 files, `vendor/` excluded) by indentation rather than column-0
regex, which is what lets nested and indented declarations be seen. Four fixes
over the earlier sweep, each of which changed the answer:

1. **`me fn` was being dropped.** The earlier modifier set did not include `me`,
   silently discarding 801 method declarations — including most of the
   `os/services/vfs/` implementers.
2. **Traits are resolved by import, not by bare name.** For a trait name with
   more than one declaration, the declaration is chosen by (a) same file, then
   (b) the `use` lines of the impl's own file matched against the declaring
   file's module ids, then (c) same directory. Only if all three fail is the
   pair recorded as unscorable. This is the single change that dissolved most of
   the earlier 30.
3. **Generic commas no longer split a parameter.** `fn matches(actual:
   Result<Any, Any>)` was being read as two parameters, manufacturing a false
   `Matcher.matches` drift. Fragments are re-joined while `<` outnumbers `>`.
4. **Return types are scored,** cut at the first top-level `:` so that a
   one-liner body (`-> bool: true`) is not mistaken for the return type.

The scorer is checked against a **positive-control fixture** carrying a known
arity drift in each direction, a `me fn` drift, a return-type drift, and a
generic-comma parameter that must *not* fire. All four are detected and the
control does not false-positive. Without that control, "0 drift" would be
indistinguishable from a scorer that had stopped working — which is exactly how
the earlier sweep's numbers survived.

### Result

| tier | scored | drift |
|---|---|---|
| A — `impl T for Y:` vs trait decl | 2,300 method pairs, 875 impl blocks | **2 arity** (one defect, two duplicate files) |
| A — return type, arity-equal | same | 48 total, of which **39 are generic/associated-type substitution** (`Self`→`i64`, `Slice<T>`→`Slice<u8>`) and **9 are real divergence** |
| B — inherent `impl Y:` shadowing a trait method name | 5,365 blocks over 3,805 types | 9, of which **1 warrants an owner** |

Trait/impl population: 589 trait declarations under 318 distinct names (103
names declared more than once — this is why bare-name keying fails), 1,603 trait
method declarations, 2,737 trait-impl method definitions.

### What the earlier sweep got wrong, and why

| sweep claim | census finding |
|---|---|
| `BlockDevice.read_sector` 2-arg decl vs 1-arg impls ×9 | **Two distinct `trait BlockDevice` exist**: `src/lib/nogc_sync_mut/fs_driver/block_device.spl:6` declares `(lba)` and `src/os/drivers/nvme/block_device.spl:17` declares `(lba, buf_phys)`. Every impl's arity matches the trait its own `use` line imports — verified by listing all 32 implementers against their `use` lines. `src/os/services/block_device.spl` is a re-export of the 1-arg lib trait, not a third declaration. Real drift: **2 files** (below). |
| `RenderBackend3D` `bind_texture` / `create_pipeline` / `end_render_pass` ×12 | **No drift.** `fn bind_texture(self, rph, tex, slot)` at all 9 sites; `fn end_render_pass(self, rph)` at all 9. Confirmed by direct grep, independent of the parser. Five traits share the `RenderBackend3D*` prefix across three tiers; the sweep compared impls against the wrong one. |
| `RenderBackend.init` 2-arg decl vs 0-arg impls ×2 | **No drift.** Only `src/lib/common/ui/backend.spl:24` declares `init`, as `fn init() -> Result<bool, text>`, and its two implementers (`src/os/compositor/{browser,fb}_backend.spl`) define `fn init()`. The `fn init(self, width, height)` ×8 the sweep matched belong to the engine2d `RenderBackend`, whose trait declares no `init` at all. |
| `MirTextCodegen.translate_function` | Correct, and fixed in `f4a4703f0fb`. |

The lesson is narrower than "the sweep was sloppy": **a bare-name trait key is
not a conservative approximation.** It does not merely miss drift, it
manufactures it, and it manufactures it in proportion to how carefully a
codebase tiers the same abstraction across `common/`, `nogc_sync_mut/`,
`nogc_async_mut/` and `gc_async_mut/`. Every one of the three false families
came from exactly that tiering.

### Triage

**(a) Genuinely broken — 1 defect, 2 files. FIXED here.**

`MockFat32BlockDevice.read_sector`, in two byte-identical copies:
`test/02_integration/storage/dbfs/fat32_no_regression_spec.spl:53` and
`test/integration/storage/dbfs/fat32_no_regression_spec.spl:53`.

| | signature |
|---|---|
| trait (`src/lib/nogc_sync_mut/fs_driver/block_device.spl:6`, imported by the spec as `use std.fs_driver.block_device`) | `fn read_sector(lba: u64) -> Result<[u8], text>` |
| impl (before) | `fn read_sector(lba: u64, buffer: [u8]) -> Result<bool, text>` |

Both arity **and** return type diverge: the mock was written to the nvme
out-parameter convention while implementing the lib return-the-data convention.

What the nil sentinel would corrupt: the sole consumer is
`nvfs_raw_read_sector` (`src/lib/nogc_sync_mut/fs_driver/nvfs_superblock.spl:46`
and `nvfs_arena.spl:66`), which calls `dev.read_sector(lba)` with one argument
and binds `Result<[u8], text>`. Under JIT the missing `buffer` arrives as the
nil sentinel `3`; `buffer.len()` on a non-array yields `-1`, so
`while i < self.sector.len() and i < buffer.len()` never enters, the mock copies
nothing, and returns `Result.Ok(true)` — a **bool where the caller unwraps a
`[u8]`**. FAT32 superblock parsing would then read its boot-sector fields off a
boolean. In a spec named `fat32_no_regression_spec`, that is a false green with
the signature of a passing regression test.

**It is inert today, and that is an accident, not correctness** — the same shape
as the `MirTextCodegen` case above, where `span` was only read under
`if self.debug_info:`. This spec's own assertions
(`fat32_no_regression_spec.spl:78-103`) only exercise `driver_name()` and
source-text `contains(...)`; none of them reaches `read_sector`. The mock is
wrong and unexercised, not right. Recorded as class (a) because *enabling the
arity check turns it into a hard error at impl-registration time* — before any
assertion runs — so it breaks the spec outright whether or not anything calls it.

Fixed by rewriting both copies to the trait's convention, using the idiom
already established for the identically-named mock in
`test/01_unit/lib/fs_driver/fat32_core_test.spl:41`.

**(b) Benign — 8 of the 9 Tier B records.**

- `Drop.drop` (`src/compiler_rust/lib/std/src/core_immut/persistent.spl:113`) —
  `List.drop(n)`, the list-slicing operation, colliding by name with the `Drop`
  destructor trait. Unrelated methods.
- `Calculator.add` ×2 and `Filesystem.read` ×1 — declarations nested inside `it`
  blocks and inside a markdown fence in a docstring; scoped to their example,
  and partly an artifact of flat parsing.
- `Read.read` / `read_to_end` / `read_to_string` ×4 — trait name unresolvable
  (`Read` is declared in several tiers with no import to disambiguate), listed
  as uncertain rather than benign; see below.

**(c) Uncertain — for an owner, not for a blind edit.**

`Filesystem.mkdir` on `DbFsDriver`. `src/os/services/dbfs/dbfs_filesystem_ops.spl:112`
carries `impl Filesystem for DbFsDriver` and correctly matches the VFS trait's
`fn mkdir(path: text) -> Result<bool, text>`
(`src/os/services/vfs/vfs.spl:38`). Separately,
`src/lib/nogc_sync_mut/db/dbfs_driver/dbfs_driver.spl:1022` defines an inherent
`fn mkdir(path: text, mode: u32) -> Result<(), FsError>` — the POSIX-style API,
with a different arity *and* a different return type, on the same type name.
Tier B, so the arity check would not fire on it; but which `mkdir` a call site
binds is worth an owner's eye. Not touched here: this is a live VFS/DBFS lane
that cannot be exercised on this host.

The 9 real return-type divergences are recorded for completeness. None is
touched by the proposed arity check, and all but one live in
`src/app/interpreter/`, which specs cannot reach:
`Display.fmt` `text`→`String` (`parser.spl:17`, `core/value.spl:133`),
`Ord.cmp` `Ordering`→`i64` (`async_runtime/actor_scheduler.spl:102`,
`mailbox.spl:168`), `Display.to_string` `text`→`str` (trait_coherence_spec ×2),
`FsDriver.capabilities` `FsCapabilitySet`→`CapabilitySet`
(`src/os/services/nvfs/{driver,posix}/fs_driver_impl.spl`), and
`HardwareCodegen.compile_process` `text`→`Result<text, CompileError>`
(`src/compiler/70.backend/backend/vhdl_backend.spl:346`).

### Residual error modes of the census

> **Partly SUPERSEDED.** The first bullet's two unknowns (40 not-found traits,
> 20 unscorable pairs) are closed in *Steps 3-5 closed* below, and the guess
> that the 40 are "almost certainly built-in or Rust-side traits" was **wrong** —
> 37 are ordinary `.spl` declarations the census's regexes could not match.

Stated so the next reader can bound the claim rather than inherit it:

- **123 of 875 impl blocks are not fully scored.** 40 blocks name a trait with
  no declaration anywhere in the tree (`AsyncContextManager` ×8,
  `LanguageProvider` ×7, `Generator` ×7, `LanguageCompiler` ×6,
  `SnapshotFormatter` ×5, others) — these are almost certainly built-in or
  Rust-side traits, but the census cannot prove it. 63 more resolve to several
  same-named declarations that the `use` lines do not separate; of those, 20
  method pairs have genuinely divergent candidate signatures and are reported
  unscorable rather than guessed. **Any of those 20 could be a real drift.**
- **Parameter types are not compared**, only count and return type. A trait
  declaring `f(a: u64)` against an impl defining `f(a: text)` is invisible here.
- **`class Y(T):` conformance is approximated.** 21 such declarations exist; the
  census treats a capitalised base as a possible trait, which may over- or
  under-count Tier B.
- **Import resolution is textual**, matching `use` paths against candidate
  module ids including the `std.` tier-skipping alias. It is not the compiler's
  resolver, and `src/os/services/block_device.spl`-style `pub use` re-exports
  are followed only one hop.
- **Duplicated test trees inflate counts.** `test/02_integration/…` and
  `test/integration/…` (likewise `test/03_system` / `test/system`,
  `test/01_unit` / `test/unit`) hold byte-identical copies, so every finding in
  them is double-counted. Both copies must be fixed; there is one defect.

Scripts: `scratchpad/census2.py` (parser) and `scratchpad/score2.py` (scorer),
with the control fixture in `scratchpad/ctrl/`. **Superseded** — those violate
the repo's "ALL code in `.spl`/`.shs`" rule and each of the residual unknowns
above turned out to be an artefact of their parser. Replaced by
`scripts/check/check-trait-arity.spl`; see the next section.

## Steps 3-5 closed, and the census ported to Simple (2026-08-04)

Verified in a pristine detached worktree at origin tip `34e7d0f303b`.

### The checker

`scripts/check/check-trait-arity.spl` — pure Simple, ~940 lines, one file, no
dependencies beyond `std.nogc_sync_mut.io_runtime`. It scores **Tier A only**
(`impl T for Y:` against the trait declaration it resolves to), because Tier A
is exactly what the live check at `interpreter_eval.rs:985` gates; Tier B is a
dispatch advisory, not something arming the check would fire on.

    bin/simple run scripts/check/check-trait-arity.spl              # roots src test
    bin/simple run scripts/check/check-trait-arity.spl --selftest
    bin/simple run scripts/check/check-trait-arity.spl --list-unscorable

Verdict is the last line of stdout: `PASS`(0) / `FAIL`(1) / `ERROR — nothing was
scored`(2). Whole-tree run takes ~12s.

The positive control is **embedded in the checker and written to a temp
directory at run time**, not checked in — a deliberately-drifted `.spl` in the
repo would otherwise be picked up by lint or a tree sweep, and a checked-in
fixture can drift away from the checker it guards. It runs **before every scan
and is fatal**: nine planted cases, six that must fire (over-arity,
under-arity, `me fn`, bare `me`, `pub trait`, `extends`) and three that must
stay silent (generic-comma parameter, mixed `self`/`me` receivers, return-type-
only difference). Six independent sabotages of the implementation were each
confirmed to fail the control while the clean checker passes.

The control is a unit-level guard, so it was backed by an **end-to-end proof on
the real tree**: widening `Riscv64VirtioBlkAdapter.read_sector`
(`src/os/services/vfs/riscv64_virtio_blk_adapter.spl:23`) from one parameter to
two made the checker exit 1 with

    BlockDevice.read_sector on Riscv64VirtioBlkAdapter: trait=1 impl=2 [import] …:23
    FAIL -- 1 Tier-A arity drift(s)

and the tree was restored to 0 `src/` diff. The `[import]` resolution mode in
that line is itself the proof that the `pub use` re-export hop works: the impl
file names `os.services.block_device`, and only the hop reaches the declaring
module. The first attempt at this injection **silently did nothing** — the
`sed` pattern matched `fn read_sector` while the real declaration is `me fn
read_sector`, and the run came back PASS. A green result from an injection that
did not land looks exactly like a working checker.

One control case had to be redesigned: the generic-comma guard was originally
symmetric (`Result<Any, Any>` on both sides), and a sabotage that disabled the
re-join **still passed**, because both sides then miscounted identically and
the drift cancelled. The control now puts the generic on the trait side only.
A symmetric control case cannot detect a symmetric bug.

### Results, and what the Python census had wrong

| | census (`f4a4703f0fb`) | checker (`34e7d0f303b`) |
|---|---|---|
| files scanned | 35,253 | 35,254 (`.`) / 34,041 (`src test`) |
| trait declarations | 589 | 617 |
| `impl T for Y:` blocks | 875 | 913 |
| **Tier-A method pairs scored** | 2,300 | **3,928** |
| **Tier-A arity drift** | 0 (after 2 fixes) | **0** |
| unscorable | 20 | 4 |
| methods under a not-found trait | 40 (9 names) | 3 (2 names) |

The +1,628 newly scored pairs and the collapse of both unknown buckets come
from three declaration forms the census's regexes could not see. Each is now
covered by its own control case:

1. **`pub trait X:`** — `trait_hdr` was anchored `^(\s*)trait\s+`, with no `pub`
   alternative. 19 declarations repo-wide were invisible, including both generic
   `ContextManager<T>` declarations and six of the nine "not-found" trait names.
2. **`trait X extends A, B:`** — the header regex allowed `<...>` and `(...)`
   after the name but not `extends`. 1 declaration (`SdnHandler`).
3. **bare `me name(...)`** — `fn_start` required a literal `fn` keyword, so the
   receiver-shorthand method form was dropped entirely. ~19.5k such declarations
   exist in the tree. This is the single largest coverage gain, and it is a
   *different* bug from the `me fn` one the census already fixed.

Two further resolver defects were found and fixed while porting, both of which
silently *inflated* the unscorable count rather than hiding drift:

4. **A `./`-prefixed root defeated module-id derivation.** Running against `.`
   left paths as `./src/lib/...`, so the `src/` strip never fired, no `std.`
   tier-skipping alias was produced, and every multi-declaration trait fell
   through to AMBIGUOUS. Fixing it took unscorable from 38 to 12 and resolved
   the whole `RenderBackend3D` family.
5. **`pub use` re-exports were followed zero hops, not one.** The census claimed
   one hop; neither implementation had it. Adding a single hop took unscorable
   from 12 to 4 and resolved all eight remaining `src/os/**` `BlockDevice`
   records, which name `os.services.block_device` (a `pub use` shim) rather than
   the declaring module.

### Step 3 — the 20 unscorable pairs: all clean, 0 drift

Each was pinned by hand; the checker independently agrees.

| family | n | verdict |
|---|---|---|
| `Hash.hash` on `SymbolId`, `BinaryRef` | 2 | **clean** — impl arity 0 and *both* candidates arity 0, so the pair is decidable without pinning the declaration at all. (Return types differ, `u64` vs `i64`; not an arity matter.) |
| `ContextManager.__enter__` on `MmapRegion`/`File` | 5 | **clean** — resolves to `pub trait ContextManager<T>`, arity 0. |
| `ContextManager.__exit__` on `MmapRegion`/`File` | 5 | **clean** — the impls are `impl ContextManager<T> for …` and resolve to `pub trait ContextManager<T>`, whose `__exit__(exc)` is **arity 1**, matching. The census saw only the two *non-generic* `ContextManager` declarations (Python-style `__exit__(exc_type, exc_value, traceback)`, arity 3) because its regex rejected `pub`, which is what made this family look like a 1-vs-3 drift. Declarations: `src/compiler_rust/lib/std/src/file/context.spl:17` and `.../host/common/io/fs_types.spl:552`. |
| `Iterator.next` on `DirEntries` | 1 | **clean** — all 12 candidate declarations are arity 0. |
| `Deserializable.deserialize` on `Point` | 3 | **clean** — both candidates arity 1, matching. |
| `BlockDevice.read_sector` | 4 | **clean** — all four `use os.services.block_device.{BlockDevice}`, which is a one-hop `pub use` re-export of `src/lib/nogc_sync_mut/fs_driver/block_device.spl:6`, `fn read_sector(lba) -> Result<[u8], text>`. All four impls are arity 1 with that exact return type. |

**20 of 20 clean. No Tier-A drift was hiding in the unscorable set.**

The 4 that remain unscorable in the checker are the `ContextManager.__exit__`
records above: two arity-1 and two arity-3 declarations of the same trait name
are all reachable, and the impls' `use host.common.io.*` glob does not separate
them textually. Every one has impl arity 1, matching the generic declaration
the `impl ContextManager<T> for …` header names. Reviewed, not unknown.

### Step 4 — the 40 not-found traits: 37 found, 1 generated, 2 genuinely missing

| trait | methods | verdict |
|---|---|---|
| `AsyncContextManager` | 8 | **found** — `pub trait AsyncContextManager<T>` ×3 (`file/context.spl:22`, `host/common/io/fs_types.spl:557`, `host/common/net/tcp.spl:286`) |
| `LanguageProvider` | 7 | **found** — `pub trait`, `mcp/multi_lang/__init__.spl:42` |
| `Generator` | 7 | **found** — `pub trait Generator<T>`, `spec/property/generators.spl:9` |
| `LanguageCompiler` | 6 | **found** — `pub trait`, `tooling/compiler/compiler_interface_impl.spl:14` |
| `SnapshotFormatter` | 5 | **found** — `pub trait`, `spec/snapshot/formats.spl:9` |
| `ResourceProvider` | 3 | **found** — `pub trait`, `mcp/core/provider.spl:8` |
| `SdnHandler` | 1 | **found** — `trait SdnHandler extends DataHandler, OpHandler:`, `sdn/handler.spl:32` |
| `Greeter190` | 1 | **generated** — declared inside an `r"""…"""` fixture string in `test/03_system/compiler/trait_default_cross_module_codegen_regression_spec.spl:88`; the `impl` at `:109` is inside the same raw string. Source of a generated module, not tree source. Correctly unscorable. |
| `IntoAction` | 2 | **GENUINELY MISSING — new finding.** See below. |

None of the 37 is a compiler built-in; all are ordinary `.spl` declarations the
census's parser could not match. The doc's earlier guess — "almost certainly
built-in or Rust-side traits" — was wrong, and would have left the tree looking
cleaner than it is.

**`IntoAction` is declared nowhere.** `test/01_unit/app/ui/typed_action_spec.spl`
(and its byte-identical duplicate `test/unit/app/ui/typed_action_spec.spl`) has

    use common.ui.action.{Action, CommonAction, IntoAction}
    …
    impl IntoAction for AppAction:
        fn into_action(self) -> Action: …

but `src/lib/common/ui/action.spl` declares only `class Action:`. Neither
`IntoAction` nor `CommonAction` exists anywhere in the tree — the only two files
mentioning either name are the two copies of this spec. Because an unresolved
`use` is only a warning (exit 0), the spec has been passing while conforming to
a trait that does not exist. Filed as a separate defect rather than fixed here:
it is a UI-lane feature gap, not trait-arity work, and it is invisible to the
arity check either way (a trait with no declaration cannot drift from one).

### Step 5 — `Filesystem.mkdir` on `DbFsDriver`: DECIDED

The trait implementation is correct and the inherent method is **dead code**.

| | site | signature |
|---|---|---|
| VFS trait | `src/os/services/vfs/vfs.spl:38` | `fn mkdir(path: text) -> Result<bool, text>` |
| trait impl | `dbfs_filesystem_ops.spl:246` (in `impl Filesystem for DbFsDriver` at `:112`) | `me fn mkdir(path: text) -> Result<bool, text>` — matches; body calls `self.mkdir_path(path, 0o755)` |
| inherent | `dbfs_driver.spl:1022` (in `impl DbFsDriver:` at `:398`) | `fn mkdir(path: text, mode: u32) -> Result<(), FsError>`, docstring *"Alias for mkdir_path (direct driver API)"*, body `self.mkdir_path(path, mode)` |

The lane did not need to be exercised, because the ambiguity the census worried
about does not exist at any call site: **every caller of the two-argument POSIX
form calls `mkdir_path`, not `mkdir`** — `src/lib/nogc_async_mut/fs_driver/instance.spl:119`
and `mount_table.spl:94` both do `d.mkdir_path(path, mode)`. A repo-wide sweep
of `.mkdir(` finds no call on a `DbFsDriver` value at all. The two-argument
inherent `mkdir` therefore has **zero callers**; it is a pass-through alias
sitting on a trait method's name, and an identical uncalled alias exists at
`src/lib/nogc_sync_mut/db/dbfs_engine/fs_driver.spl:365`.

**Recommendation for the DBFS owner (not applied here):** delete both uncalled
`mkdir(path, mode)` aliases and keep `mkdir_path` as the direct driver API, per
*NEVER add unused code — delete completely*. It is not a blocker for arming the
arity check: it is Tier B, and the check never sees inherent `impl Y:` blocks.
Left to the DBFS lane's own change rather than edited blind from here.

### Residual error modes of the checker

Narrower than the census's, but not empty:

- **Parameter types are still not compared**, only arity. `f(a: u64)` against
  `f(a: text)` is invisible. Return types are parsed but not gated (the census's
  9 real return divergences are unchanged and untouched).
- **4 pairs remain unscorable** (`ContextManager.__exit__`, above) — reviewed and
  clean, but resolved by hand rather than by the tool.
- **Import resolution is textual**, one `pub use` hop, and is not the compiler's
  resolver. A glob (`use host.common.io.*`) is matched as a literal string, so
  it never separates same-named declarations.
- **Raw-string fixtures are parsed as source** (`Greeter190`). Harmless while
  such blocks only ever land in the not-found bucket.
- **Tier B is not scored at all.** The census's 9 Tier-B records stand as its
  last word on inherent-method shadowing.
- **Duplicated test trees still double-count** (`test/01_unit` vs `test/unit`,
  etc.). Both copies of any finding must be fixed; there is one defect.

## Before the arity check can be switched on

**Do not add the `params.len()` comparison at `interpreter_eval.rs:985` yet.**
The recommendation above is still right, but the ordering is load-bearing:
turning arity checking on while any drift remains converts every one of them
into a hard error at impl-registration time, which is how `main` was broken for
~60 commits before `4670db2d31f2` repaired it. Close the drifts first, then
arm the check. Checklist:

1. ~~Fix `MirTextCodegen.translate_function`~~ — done, `f4a4703f0fb`.
2. ~~Fix `MockFat32BlockDevice.read_sector` in both duplicate copies~~ — done here.
3. ~~Score the 20 unscorable pairs~~ — done. All 20 clean, 0 drift; 6 of the 9
   families were artefacts of the census's `pub trait` blind spot. See *Step 3*.
4. ~~Resolve the 40 not-found traits~~ — done. 37 found (ordinary `.spl`
   declarations, **not** built-ins), 1 generated fixture, 2 genuinely missing
   (`IntoAction`, filed separately). See *Step 4*.
5. ~~Decide `Filesystem.mkdir` on `DbFsDriver`~~ — done. Trait impl correct; the
   inherent 2-arg `mkdir` has zero callers. Deletion recommended to the DBFS
   owner; not a blocker (Tier B). See *Step 5*.
6. ~~Re-run the census and require 0 Tier-A arity drift, with the positive
   control passing in the same run~~ — done, by
   `scripts/check/check-trait-arity.spl`: **3,928 Tier-A pairs, 0 arity drift**,
   control fatal and run before the scan. 6 sabotages of the implementation each
   confirmed to fail the control.
7. ~~**Only then** add the comparison, with receiver normalisation on both
   sides~~ — done, see *The check is armed* below.
8. ~~**Collect all conformance failures per impl** rather than `return Err` on
   the first~~ — done, see *The check is armed* below.
9. **Expect the check to fire only on the interpreter path.** It does not close
   the JIT hole; the nil-sentinel-`3` silent-wrong-value behaviour under the
   default engine is a separate defect and is not addressed by any of this.
   **This remains explicitly OUT OF SCOPE here and is owned by another lane.**
   Arming the conformance check narrows nothing about call-site arity under the
   JIT: a missing call argument still reads as nil sentinel `3` rather than
   being rejected. Only trait-conformance *declarations* are now gated, and only
   where the interpreter registers the impl block.

A standing gate is worth more than a one-off census — **done**:
`scripts/check/check-trait-arity.spl` fails on any new Tier-A arity drift, so
this cannot re-accumulate between campaigns. It is pure Simple, not the Python
it replaces; the repo forbids Python and Bash outside the three bootstrap
scripts, and porting rather than copying is what surfaced the three declaration
forms the census could not parse.

**Steps 1-6 are closed; 7, 8 and 9 remain before the check is armed.** The two
that still gate arming are both in step 7 and step 8: receiver normalisation
must be applied on both sides (the checker's `is_receiver` is the reference
implementation — `self`, `me`, `&self`, `&mut self`, `mut self`), and the
first-failure-only `return Err` must become collect-all first, or the first
arity error will hide the next one exactly as the `MirTextCodegen` break did.

## The check is armed (2026-08-04)

**Steps 7 and 8 are now closed. Step 9 stands as a documented non-goal.** The
arity comparison is live in `src/compiler_rust/compiler/src/interpreter_eval.rs`
at the trait-implementation registration site.

### What changed

Two things, in one place:

1. **`return Err` on the first missing name became accumulate-then-report.** The
   loop now walks every trait method, pushes a description of each problem into
   a `Vec<String>`, and returns a single `CompileError::Semantic` joining them
   with `"; "` only after the whole trait has been scored. A three-method drift
   is now three sentences in one error, not three rebuilds. The single-missing-
   method wording is byte-identical to the old `factory::missing_trait_method`
   string, so `simple-type`'s `test_impl_missing_trait_method` is unaffected.
2. **The arity comparison itself**, via a new `trait_conformance_arity` helper.

### How the receiver was normalised

Not by stripping a fixed prefix — by **filtering parameters by name on both
sides**:

```rust
fn trait_conformance_arity(f: &FunctionDef) -> usize {
    f.params.iter().filter(|p| p.name != "self" && p.name != "me").count()
}
```

Filtering rather than head-stripping is load-bearing, because the two sides are
built by different parser paths and are *not* symmetric:

| side | where | receiver behaviour |
|------|-------|--------------------|
| impl | `parser/src/types_def/trait_impl_parsing.rs` `parse_indented_impl_body` | **auto-injects** a param literally named `self` at index 0 for every non-static method, whatever the source wrote (`fn f(self)`, `me fn f()`, `var fn f()`) |
| trait | `parser/src/types_def/trait_impl_parsing.rs` `parse_trait_method_after_fn` | **no injection at all** — params are exactly as written, so `fn f(self, a)` keeps the receiver and `fn f(a)` never had one |

So the same conforming pair can arrive as `[self, a]` vs `[a]`, or as
`[self, a]` vs `[self, a]`, depending only on how the trait was spelled. The
impl-side injection guard tests `params[0].name != "self"` and does **not**
exclude `"me"`, so a receiver written explicitly as `me` can survive as a
parameter named `me` alongside an injected `self` — which is why both names are
filtered, at any position, rather than one leading element being dropped.
This mirrors `is_receiver`/`pcount` in `scripts/check/check-trait-arity.spl`,
which is the reference implementation and the regression oracle. The `&self` /
`&mut self` / `mut self` spellings the `.spl` checker also accepts are text-level
forms that cannot reach the Rust AST: the lexer maps `self` to `TokenKind::Self_`
and `parse_parameters` records the name as plain `self`, with `mut` consumed as a
separate mutability flag.

### Verification

* **Positive, both directions** — a planted drift is rejected, naming trait,
  method and both counts:
  * trait 1-arg vs impl 2-arg → `error: semantic: type `Box` implements method
    `scale` from trait `Shape` with 2 parameter(s), but the trait declares 1`
  * trait 2-arg vs impl 1-arg → `error: semantic: type `Box` implements method
    `scale` from trait `Shape` with 1 parameter(s), but the trait declares 2`
* **Accumulate-then-report** — a fixture with one over-arity method, one missing
  method and one under-arity method reports all three in a single error.
* **Negative, `me fn`** — a trait declaring `fn bump(self, by)` / `fn reset(self)`
  implemented as `me fn bump(by)` / `me fn reset()` runs clean. Receiver
  normalisation works; this is the case that would have broken `main`.
* **Negative, generic comma** — `Result<Any, Any>` counts as ONE parameter, in
  both 1-param and 2-param positions. The Rust parser builds `Parameter`s from
  parsed types, so a comma inside `<>` cannot manufacture a count; unlike the
  text-scanning `.spl` checker, this needs no `split_params` equivalent.
* **Negative, trait without a written receiver** — trait `fn describe(label)`
  against impl `fn describe(self, label)` runs clean, covering the injection
  asymmetry above.
* **Whole repo, both checkers agree — no disagreement found.**
  `scripts/check/check-trait-arity.spl` reports `PASS -- 3928 Tier-A method
  pairs scored, 0 arity drift` (614 trait declarations, 909 impl blocks, control
  fixture passing in the same run). The armed compiler produced **zero** arity
  diagnostics across 651 executed spec files. Neither side flagged a pair the
  other cleared.
* **Gate** — `test/01_unit/lib/gc_async_mut/gpu/browser_engine/html_parser_gpu_flat_spec.spl`
  → `Results: 24 total, 24 passed, 0 failed`.
* **Rust suite** — `cargo test -p simple-compiler` was run on the armed tree AND
  on the pristine base for comparison, because the tree is not green at either.
  Armed: 3481 passed / 121 failed. Base: 3453 passed / 149 failed. Same 3602
  total, and the armed failure set is a **strict subset** of the base set — zero
  test names fail only under the armed build. The delta is pre-existing
  flakiness under load, not a regression. `cargo clippy` is clean; `cargo fmt
  --check` reports the same two pre-existing hunks in this file before and after
  the change, so the edit adds no formatting debt.

### What is still not covered

Everything in step 9. The check runs only where the **interpreter** registers an
impl block, so it does not fire on the JIT or native paths, and it does not
close the call-site hole where a missing argument reads as nil sentinel `3`.
It also compares **arity only** — parameter *types* are still never checked, so
a same-arity type drift remains invisible, exactly as the title of this bug
says. Both are separate lanes.

## Reproduction and engine A/B (2026-08-17)

Binary: `bin/release/x86_64-unknown-linux-gnu/simple`, 59536728 bytes,
mtime 2026-08-16 22:59:37 (Rust seed; prints the seed banner). One binary, one
tree, one toggle — `SIMPLE_EXECUTION_MODE` — over
`test/01_unit/compiler/traits/conformance/probe_wrong_arity.spl` (trait declares
`greet(name, punctuation)`, impl defines `greet(name)`):

| engine | rc | observed |
|--------|----|----------|
| `interpreter` | 1 | ``error: semantic: type `Rude` implements method `greet` from trait `Greeter` with 1 parameter(s), but the trait declares 2`` |
| `jit`         | 0 | no diagnostic; the impl body RUNS and prints `FIXTURE_RAN_WRONG_ARITY` |

A bare `bin/simple run <fixture>` (no env pin) matches the `jit` row — so the
DEFAULT engine for ordinary programs silently accepts a non-conforming impl.
This confirms the status line's "fires only on the interpreter path" with a
direct measurement rather than by inspection.

### Trap that hid this, worth knowing

`bin/simple test` exports interpreter mode to its child processes. A subprocess
spec that shells out WITHOUT pinning `SIMPLE_EXECUTION_MODE` therefore measures
the interpreter twice and reports green while the JIT lane is broken. Both specs
below were written unpinned first and passed `Results: 2 total, 2 passed,
0 failed` / `3 total, 3 passed, 0 failed` — a false green over a live defect.
Pin the engine explicitly in any conformance subprocess spec.

### Pure-Simple side: the checker has no callers

`src/compiler/25.traits/trait_impl.spl::validate_methods` is the pure-Simple
conformance checker. `grep -rn validate_methods src/compiler src/app` returns
exactly ONE line — its own definition. Likewise `TraitError.MissingMethod`
(`src/compiler/25.traits/trait_validation.spl:22`) is matched on by two driver
files that RENDER it but is never CONSTRUCTED anywhere. Both mechanisms are
inert on the self-hosted path, the same shape as `interface_digest_of`. Arity
and a conservative primitive-parameter-type comparison are now implemented in
`validate_methods`; WIRING it into the semantic pass remains open.

### Specs

- `test/01_unit/compiler/traits/conformance/trait_impl_arity_conformance_spec.spl`
  (reproducing) — interpreter arm GREEN, **JIT arm expected RED**, conforming
  control arm GREEN on both engines.
- `test/01_unit/compiler/traits/conformance/trait_conformance_enforced_class_spec.spl`
  (similar-problem detection) — generalises to the class "a semantic conformance
  obligation enforced on one engine and skipped on another", covering BOTH
  violation axes (missing required method, wrong arity) against BOTH engines, so
  a single-engine or single-axis fix cannot turn it green.

Do not weaken the RED examples to make them pass; the unblock condition is a
JIT-path conformance check (or hoisting the check ahead of engine selection).

### Runtime hazard

The class spec runs 10 nested compiles and was SIGTERMed (`rc=143`) at the
shared 600s kill-monitor threshold. It needs a raised threshold or a split to
produce a verdict on a loaded host; its arms are individually verified by the
A/B table above.
