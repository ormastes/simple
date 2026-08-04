# Trait conformance check is name-only — arity and parameter types are never compared

- **Status:** OPEN — mechanism confirmed; drift census complete and closed to 0
  known Tier-A pairs. The check itself is still **not armed**; see
  *Before the arity check can be switched on* at the end of this file.
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
with the control fixture in `scratchpad/ctrl/`.

## Before the arity check can be switched on

**Do not add the `params.len()` comparison at `interpreter_eval.rs:985` yet.**
The recommendation above is still right, but the ordering is load-bearing:
turning arity checking on while any drift remains converts every one of them
into a hard error at impl-registration time, which is how `main` was broken for
~60 commits before `4670db2d31f2` repaired it. Close the drifts first, then
arm the check. Checklist:

1. ~~Fix `MirTextCodegen.translate_function`~~ — done, `f4a4703f0fb`.
2. ~~Fix `MockFat32BlockDevice.read_sector` in both duplicate copies~~ — done here.
3. **Score the 20 unscorable pairs.** They are the only place a Tier-A drift can
   still be hiding. Each needs its trait declaration pinned by hand
   (`ContextManager.__enter__`/`__exit__` on `MmapRegion`/`File`, `Hash.hash` on
   `SymbolId`/`BinaryRef`, `Iterator.next` on `DirEntries`, and the rest listed
   in `scratchpad/drift2.json`).
4. **Resolve the 40 not-found traits.** Confirm they are compiler built-ins with
   no `.spl` declaration; if any is a real trait the census failed to parse, it
   is unscored, not clean.
5. **Decide `Filesystem.mkdir` on `DbFsDriver`** (class (c) above).
6. **Re-run the census and require 0 Tier-A arity drift**, with the positive
   control passing in the same run. A zero from a scorer whose control was not
   also exercised proves nothing.
7. **Only then** add the comparison, and add it with the receiver normalisation
   the census uses (`self`/`me`/`&self`/`&mut self` dropped from both sides) —
   the two receiver conventions are both live and a naive `params.len()` would
   red-flag every `me fn` implementer of a `fn f(self, …)` trait.
8. **Land the check behind the follow-ups already filed**: collect all
   conformance failures per impl rather than `return Err` on the first, or the
   first arity error will again hide the next one.
9. **Expect the check to fire only on the interpreter path.** It does not close
   the JIT hole; the nil-sentinel-`3` silent-wrong-value behaviour under the
   default engine is a separate defect and is not addressed by any of this.

A standing gate is worth more than a one-off census: `scratchpad/census2.py` +
`score2.py` should become a `scripts/check/` lint that fails on any new Tier-A
arity drift, so this cannot re-accumulate between campaigns.
