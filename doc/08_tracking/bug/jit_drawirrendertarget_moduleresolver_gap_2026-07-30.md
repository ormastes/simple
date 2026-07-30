# JIT `Unknown type: DrawIrRenderTarget` — resolved by trait pre-registration

**Date:** 2026-07-30
**Status:** `DrawIrRenderTarget` RESOLVED (confirmed independently this pass,
fresh pristine worktree + rebuilt seed including `7935e971737`) — HIR Pass 0
now pre-registers trait names before declaration lowering. The next blocker,
`CastElse` (the second gap from the original assignment), is now also
ROOT-CAUSED AND FIXED (6 real `.spl`-only fixes landed, 22/22 relevant specs
passing, plus a dedicated pinning spec for the dual-engine `nil` correctness
bug). The **third** gap (`Unknown variable: text_align_v` in `tag_defaults`)
is now ALSO ROOT-CAUSED AND FIXED (a genuine, pre-existing, JIT-independent
dead-code bug: an undeclared local plus a final constructor that read the
wrong field, so `<caption>`/`<th>` centering silently never applied under
either engine). JIT now advances to a **fourth** gap
(`Memory safety error [W1006]` in `_take`, `ot_layout_context.spl`) —
found, precisely reported, deliberately **not** fixed (no established
capability-annotation syntax to safely mirror, and an unresolved
`_take`-vs-`_take_many` discrepancy). The JIT-enablement task is not fully
complete, but has advanced past three real gaps with verified fixes and a
regression pin.
**Component:** `src/compiler_rust/driver/src/exec_core.rs` (`run_file_jit`),
`src/compiler_rust/compiler/src/module_resolver/*`,
`src/compiler_rust/compiler/src/hir/lower/type_registration.rs` (`register_trait`),
`src/compiler_rust/compiler/src/hir/lower/type_resolver.rs` (`resolve_type`)

## Reproduction (PROVED, from a pristine worktree)

Per the coordinator's correction on the sibling `ot_layout_shaper.spl` doc
(the shared WC was contaminated by another session; this investigation was
redone from a fresh `git worktree add --detach` at the SSH-fetched origin
tip, never the shared WC):

```
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 \
bin/release/x86_64-unknown-linux-gnu/simple run examples/06_io/ui/web_render_file_gui.spl
```

```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error: Unknown type: DrawIrRenderTarget
```

This confirms the `web_style_producer_4s_per_node_interpreted_lane_2026-07-29.md`
finding is accurate and current — `DrawIrRenderTarget` genuinely is the
first blocker forcing JIT hits, from a pristine checkout, today.

`DrawIrRenderTarget` is a **trait**, not a plain class/struct (`trait
DrawIrRenderTarget:`, `src/lib/gc_async_mut/gpu/engine2d/draw_ir_target.spl:28`),
implemented by `Engine2D` (`engine.spl:181`) and `MetalDrawIrRenderTarget`
(`draw_ir_target_metal.spl:32`).

## Resolution correction (2026-07-30)

The original architectural conclusion below was incomplete. The JIT path
does load imported traits through `hir/lower/import_loader.rs`; the actual
ordering defect was that both HIR Pass 0 variants pre-registered
struct/class/enum/actor names but omitted traits. Flattened imports can put
`class Engine2D with DrawIrRenderTarget` before the trait declaration, so
declaration registration attempted to resolve a name that had not yet entered
the type registry.

The fix adds trait aliases to the existing pre-registration passes and to the
shared imported-type placeholder helper. Regression:
`test_trait_type_can_be_used_before_declaration`.

Validation:

- focused Rust compiler regression: PASS (1 passed)
- original web GUI JIT command: advances past `DrawIrRenderTarget`; the example
  runner reaches its configured timeout without that HIR fallback

## Root cause (PROVED by code reading) — a real, confirmed asymmetry

`register_trait` (`type_registration.rs:446-483`) registers a trait's name
as a `TypeId::ANY` alias (`self.module.types.register_alias(t.name.clone(),
TypeId::ANY)`, line 480) — but **only in the local type table of the module
that defines the trait** (`self.module.types`, per-`Lowerer`-instance state).

`resolve_type` (`type_resolver.rs:113-247`), when a type name isn't found in
the current module's own table (`self.module.types.lookup(name)`, line 138),
has an explicit **cross-module fallback for struct names** (lines 144-168,
`self.global_struct_defs`) — "This handles files that use a struct type by
name... without an explicit `use` statement." **There is no equivalent
fallback for trait names.** A module that references a trait as a type (a
parameter annotation, a return type) without itself running `register_trait`
for it locally (i.e. without itself implementing/declaring that trait) falls
through every branch to the final `UnknownType` error — exactly the observed
symptom, and exactly the class of gap `global_struct_defs` was built to
close for structs.

This asymmetry is a real, confirmed, precisely-located gap in
`compile_file_to_object`'s pipeline (`native_project/compiler.rs`,
`hir/lower/*`) — but see "Why not fixed" below for why it turned out not to
be the operative blocker for the assigned repro.

## Fix attempted, validated safe, but reverted — unverified necessity

Implemented a mirror of the existing `global_struct_defs` mechanism for
traits: added `trait_defs: HashSet<String>` alongside `struct_defs` in
`ImportMapResult` (`imports.rs`, populated for free — `trait_def_names` was
**already being collected** during the same discovery walk, just never
exposed), threaded it through `ModuleImports` (`mod.rs`) and
`compiler.rs`'s existing `imports.populate_global_struct_defs` gate, added
`global_trait_defs`/`set_global_trait_defs`/`global_trait_defs()` to
`Lowerer` (`lowerer.rs`, mirroring `global_struct_defs` exactly), and
consulted it in `resolve_type`'s fallback chain (`type_resolver.rs`,
registering `TypeId::ANY` on hit — the same choice `register_trait` itself
makes locally).

**Validation (PROVED):**
- `cargo build --release`: clean, same 16 pre-existing warnings, zero new,
  none in the 6 touched files.
- `rustfmt --check` on all 6 touched files: clean, zero diffs.
- Byte-identical-archive check on an unaffected fixture (old seed vs.
  patched seed, `check4_test.spl`, `--entry-closure --emit-archive --target
  x86_64-unknown-none --backend cranelift`): sha256-identical
  (`a6994edb73067fdd16041e1e41db89e156f4a84029c9658e3a1a01b9a0aca202`, both
  builds) — zero collateral codegen change.

**But: could not construct a positive-proof test.** A fixture built to
exercise exactly this gap (`fn touch(target: DrawIrRenderTarget)` in a file
that imports `Engine2D`, i.e. `class Engine2D with DrawIrRenderTarget:`,
without itself declaring/implementing the trait) compiled successfully
under **both** the old (unpatched) and new (patched) seed via
`native-build --entry-closure` — meaning either that fixture doesn't
actually trigger the gap the fix targets (the `native_project::compiler.rs`
pipeline may already resolve this case through some other path not
identified this pass), or the gap this fix closes was already unreachable
in that pipeline. **Most importantly: re-running the actual assigned
reproduction command (`simple run --jit` on the web example) with the
patched seed showed the identical, unchanged error** — the fix had no
effect on the actual failing path.

**Given the fix could not be shown to do anything (no failing-before/passing-
after pair found, and it did not move the assigned repro), it was reverted**
(`git checkout --` on all 6 touched files) rather than landed unverified —
per the project's "never add unused code" rule and this session's own
established validate-before-land discipline. The asymmetry itself
(struct fallback exists, trait fallback doesn't) remains real and worth
someone eventually closing, but the revert reflects that this specific
implementation's necessity/correctness was not established.

## Why not fixed — the real, architectural blocker (PROVED)

`simple run --jit`'s actual code path (`exec_core.rs::run_file_jit`, ~line
676) does **not** go through `native_project::compiler.rs` /
`build_import_map` / the `ModuleImports` struct at all. It calls
`hir::lower_with_context_and_project_hint` (`hir/lower/mod.rs:131-140`),
which constructs `Lowerer::with_module_resolver(...)` directly — **no call
to `set_global_struct_defs` or (the now-reverted) `set_global_trait_defs`
anywhere in this path.** Cross-module type resolution here relies entirely
on `ModuleResolver` (`src/compiler_rust/compiler/src/module_resolver/*`), a
different, presumably on-demand/lazy per-import mechanism — **confirmed
(PROVED, grep) to have zero references to `TraitDef` or `register_trait`
anywhere in its four source files** (`manifest.rs`, `mod.rs`,
`resolution.rs`, `types.rs`, `var_overlay.rs`). This is a **second, wholly
separate lowering/JIT pipeline** from the one `native-build`/`compile` use,
with no whole-program cross-module type-fallback infrastructure of its own
— not just missing trait support, but architecturally distinct from where
the (reverted) fix was implemented.

This is exactly the kind of gap that is "architectural" per this task's own
instruction 5: closing it requires understanding and extending
`ModuleResolver`'s on-demand type-loading mechanism (a different subsystem
with different data flow than the whole-program pre-scan `build_import_map`
performs), not a small mirrored addition. Not attempted this pass — no time
remained to safely trace and verify a fix in unfamiliar territory.

## CastElse gap — confirmed as the next blocker, ROOT-CAUSED AND FIXED (2026-07-30, follow-up pass)

Re-tested per the coordinator's follow-up: another session landed
`7935e971737` ("fix(jit): preregister trait types before declarations"),
touching `hir/lower/import_loader.rs` and
`hir/lower/module_lowering/module_pass.rs` — the actual HIR Pass 0/import
pre-registration passes, shared by **both** the `native_project` pipeline
and `run_file_jit`'s `ModuleResolver`-based path (unlike this doc's own
reverted fix, which only touched the `native_project`-specific whole-program
pre-scan). Rebuilt the Rust seed from a **fresh, second pristine worktree**
at the SSH-fetched tip (`ea63b6e2ec3`+, never the shared WC) and re-ran the
exact assigned repro:

```
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 \
bin/simple run examples/06_io/ui/web_render_file_gui.spl
```

**`Unknown type: DrawIrRenderTarget` is GONE (PROVED).** The next error is
exactly the documented `CastElse` gap, confirming the perf lane's
expectation precisely:

```
HIR lowering error: Unsupported feature: CastElse { expr: Call { callee: Identifier("read_u32_be"), ... },
  target_type: Simple("i64"), fallback_fn: Integer(0) }
```
at `src/lib/skia/feature/glyph/ot_parser_layout.spl:280`.

### Root cause (PROVED by code reading) — NOT a desugared if/else; a genuine dedicated syntax form the parser mis-scopes

`CastElse` is not what it first appears. It is a **dedicated postfix syntax
form**: `<expr> as <Type> else: <fallback>` (parser construction site:
`src/compiler_rust/parser/src/expressions/postfix.rs:586-596`,
AST node: `parser/src/ast/nodes/core.rs:702`). The catch is **parser
precedence**: when `as <Type>` is immediately followed by `else:`, the
parser **always** binds that `else:` to the cast (producing `CastElse`),
even when the cast sits inside an **outer** `if <cond>: <expr> as T else:
<fallback>` where the `else:` was clearly meant for the outer `if`. This
produces an **`if` with only a then-branch** whose value is the `CastElse`
node — confirmed by a minimal repro (`castelse_probe2.spl`):

```
fn h(cond: bool, x: i64) -> i64:
    if cond: x as i64 else: 0
```

Under the **interpreter** (not just JIT), `h(true, 5)` correctly returns
`5`, but **`h(false, 5)` silently returns `nil`, not `0`** — a real, silent,
confirmed correctness bug in the interpreter too, not merely a JIT
compilation gap. `Expr::CastElse` has **no HIR lowering implementation at
all** (`hir/lower/expr/mod.rs`'s `lower_expr` dispatch match, lines
104-208, has no `CastElse` arm), so it falls into the generic catch-all
(line 209-218) and errors under strict/JIT lowering, or silently becomes
`Nil`/`ANY` under `lenient_types` (interpreter) — explaining why the
interpreter doesn't crash but silently produces the wrong value.

**Fix (PROVED, applied and verified — source-only, no Rust compiler
changes):** parenthesizing the cast expression, `(expr as T) else:
fallback`, removes the ambiguity — the outer `if`'s `else:` is then
unambiguous, and `CastElse` never gets constructed. Verified directly:

```
fn h(cond: bool, x: i64) -> i64:
    if cond: (x as i64) else: 0
```

compiles clean under JIT (no HIR error at all) **and** returns the correct
value for both branches (`5`, `0` — not `nil`).

**Six real sites fixed** across three files (source-only `.spl` changes,
zero Rust changes this pass), each verified individually via a fix →
re-run → next-error-surfaces loop against the real web pipeline repro:

- `src/lib/skia/feature/glyph/ot_parser_layout.spl` — 4 identical-shape
  sites (`parse_gsub_skeleton` ×1, a lookup-flag site ×1,
  `parse_gpos_skeleton` ×1, `_active_layout_lookup_indices` ×1 — the first
  3 were byte-identical strings, fixed via one `replace_all`; the 4th
  matched the same pattern).
- `src/lib/skia/feature/shaper/ot_layout_apply.spl` — 1 site
  (`_apply_context_at`, `record_count: if ... else: 0`).
- `src/lib/skia/feature/shaper/ot_layout_gpos.spl` — 1 site (`_mark`, a
  nested `if kind == 5u32: target_array + read_u16_be(...) as i64 else:
  target_array` where the **outer** `if`'s `else:` was being swallowed by
  the inner cast, losing the `+ anchor_offset` semantics for the `false`
  branch — same class of bug as the minimal repro's `nil` result, just one
  level deeper).

**Bonus, unrelated, real bug found and fixed along the way (PROVED):**
`ot_layout_gpos.spl:750`, `_lookup`'s `budget: _Budget` parameter — `_Budget`
is not defined **anywhere** in the codebase (confirmed via
whole-repo grep); the real type, `GposDataBudget` (already imported at the
top of the same file, `ot_layout_gpos_data.spl`'s export), is what every
sibling function in the same file and its callers actually use
(`gpos_data_glyph_class(font, glyph, budget: GposDataBudget)`). This reads
as a stale rename artifact. Fixed: `budget: _Budget` → `budget:
GposDataBudget`.

**Validation (PROVED):**
- Fix-and-rerun loop against the real `SIMPLE_EXECUTION_MODE=jit` web
  pipeline repro: every `CastElse` error (5 occurrences across 3 files) and
  the `_Budget` unknown-type error cleared in sequence, confirmed by
  re-running the exact command after each fix.
- `bin/simple test` on the four directly-relevant existing spec files
  (`ot_layout_apply_spec.spl`, `ot_layout_gpos_spec.spl`,
  `ot_layout_gpos_variation_spec.spl`, `ot_parser_layout_selector_spec.spl`):
  **22 examples, 0 failures** — no regression from any of the six fixes.
- `git diff --stat`: 3 files changed, source-only, no Rust/compiler changes
  this pass (unlike the earlier, reverted `DrawIrRenderTarget` attempt).

### What blocks NEXT (found, not fixed — new gap beyond the assigned two)

After all `CastElse`/`_Budget` fixes, the web pipeline JIT attempt advances
to a **new, different, third gap**, confirming this is genuinely an
iceberg (matching the perf lane's framing — "a bigger web-cell win than
caching" implies many more such gaps remain):

```
HIR lowering error: Unknown variable: text_align_v while lowering tag_defaults
```

Located (PROVED): `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl`,
function `tag_defaults` (starts line 2590), which assigns `text_align_v =
"center"` at lines 2694/2703 without that variable being declared within
`tag_defaults`'s own scope — a *different* function in the same file (line
679) has its own, unrelated local `text_align_v`. This looks like either a
genuine missing-declaration bug or a JIT-specific static-scoping
requirement the interpreter doesn't enforce (matching the
`lenient_types`-tolerant-vs-strict-JIT pattern already established in this
doc for `UnknownType`). **Not investigated further or fixed this pass** —
found via the same fix-and-rerun loop, reported per the "report what blocks
next" instruction, out of scope for further root-causing given time spent
on the six fixes above.

## Recommended next steps

1. Root-cause and fix the `text_align_v` / `tag_defaults` "Unknown
   variable" gap the same way this pass closed `CastElse` — likely another
   short, contained `.spl`-only fix (missing local declaration), but not
   confirmed.
2. Consider a repo-wide survey for the `CastElse`-prone shape (`if <cond>:
   <expr> as <Type> else: <fallback>` without parens around the cast) —
   this pass's own grep found **33 occurrences across 18 files**, most
   outside the web pipeline's closure (kernel/`os` code, unrelated apps) and
   not fixed here; only the 6 sites actually blocking this specific repro
   were touched. `src/lib/common/encoding/sfnt_glyf.spl:391` already
   documents this exact class independently (a different workaround:
   hoisting the cast outside the `if`/`else` rather than parenthesizing it)
   — worth cross-referencing when doing that survey.
3. This survey-worthy shape is itself a **real interpreter correctness bug**
   (not just a JIT gap) per the minimal repro above (`nil` instead of `0`)
   — worth flagging independently of the JIT-enablement goal, since it can
   silently corrupt values under normal (non-JIT) execution today.
4. Continue the fix-and-rerun loop against the real pipeline for however
   many further gaps remain until `SIMPLE_EXECUTION_MODE=jit` on the web
   example either succeeds or reaches a genuinely architectural blocker
   worth stopping at (per this doc's own earlier `ModuleResolver` finding
   for `DrawIrRenderTarget`, now resolved by `7935e971737`).

## Validation performed this pass

- Reproduction (both the original `DrawIrRenderTarget` disappearance and
  the new `CastElse`/`_Budget`/`text_align_v` sequence): PROVED, from a
  fresh pristine worktree, exact assigned command, rebuilt seed including
  `7935e971737`.
- `CastElse` root cause (dedicated postfix syntax + parser precedence
  mis-scoping the outer `if`'s `else:`, plus a missing HIR lowering arm):
  PROVED by code reading and a minimal repro showing both the JIT error and
  a **silent interpreter correctness bug** (`nil` instead of `0`).
- Six fixes (5 `CastElse` parenthesizations + 1 `_Budget`→`GposDataBudget`
  typo): PROVED — each individually confirmed to clear its error via the
  real pipeline repro; existing spec suite for the touched files:
  22/22 passing, no regressions.
- `text_align_v`/`tag_defaults` gap: ROOT-CAUSED AND FIXED this follow-up
  pass — see below.
- Earlier `DrawIrRenderTarget` fix/revert history (this session's own
  reverted attempt, and the architectural `ModuleResolver` finding):
  unchanged from the prior version of this doc, left intact above for
  the record.

## `text_align_v` gap — ROOT-CAUSED AND FIXED (2026-07-30, second follow-up pass)

Re-tested from a **fresh, rebased pristine worktree** at the new SSH tip
(`5a6ea50b383`+, `git checkout --detach` in place of the existing worktree —
several upstream web commits had landed) using the already-built seed
(unaffected, since this gap and its fix are `.spl`-source-only, no Rust
rebuild needed).

**Root cause (PROVED by code reading) — none of the three candidate
mechanisms flagged up front; a plain, contained source bug.** Not a
module-level global/constant, not an enum/soft-keyword resolution
difference, not import-order sensitivity. `tag_defaults` (`fn tag_defaults(st:
Style, tag: text) -> Style:`,
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer_declarations.spl:2590`)
declares a full set of local `_v` shadow variables for every field it might
override (`var display_v = st.display`, `var font_size_v = st.font_size`,
… 18 of them) — **except `text_align_v`, which is never declared**, yet is
assigned at two tag-specific branches (`elif tag == "caption": ... text_align_v
= "center"`, `elif tag == "td" or tag == "th": ... if tag == "th": ...
text_align_v = "center"`). **Worse: even where declared correctly for its
siblings, the function's final `Style(...)` constructor read `text_align:
st.text_align`** (the original, unmodified field) **instead of
`text_align: text_align_v`** — so even had the variable been declared, its
value was never wired into the returned `Style`. This is a genuine,
pre-existing **dead-code / silent no-op bug independent of JIT**: `<caption>`
and `<th>` elements have never actually received `text-align: center`
styling under **either** engine — the interpreter tolerates the undeclared
assignment (auto-vivifying an untracked, thrown-away local), so it never
crashed, it just silently did nothing.

**Fix (PROVED, applied and re-verified — source-only, no Rust changes):**

1. Added the missing declaration alongside its siblings:
   `var text_align_v = st.text_align`.
2. Changed the final `Style(...)` constructor's `text_align: st.text_align`
   (the **one** occurrence at the actual end-of-function return, distinct
   from the unrelated early `is_non_rendered_tag` return which correctly
   still uses `st.text_align` since no tag-specific branch has run yet) to
   `text_align: text_align_v`.

**Validation:** re-ran the exact `SIMPLE_EXECUTION_MODE=jit` web pipeline
repro — `Unknown variable: text_align_v` is **gone** (PROVED).

### What blocks NEXT — a fourth gap found, NOT fixed this pass

JIT now advances to a new, different, **fourth** gap:

```
HIR lowering error: Memory safety error [W1006]: mutation without mut capability (field_0):
  mutation requires `mut` capability on the receiver while lowering _take at 29:22
```

Located (PROVED): `src/lib/skia/feature/shaper/ot_layout_context.spl:27-30`:

```
fn _take(budget: _LayoutBudget, amount: i64) -> bool:
    if amount < 0 or budget.remaining < amount: return false
    budget.remaining = budget.remaining - amount
    true
```

`budget: _LayoutBudget` (a plain `class` parameter, no `mut` annotation) has
its field mutated at line 29 (`budget.remaining = ...`) — matching the
error's "(field_0)" (the class's first declared field, `remaining`).
**However, checked and confirmed this is NOT simply "this codegen path
requires `mut` everywhere":** the structurally **identical** pattern exists,
unfixed, unflagged, in `src/lib/skia/feature/shaper/ot_layout_gpos_data.spl:52-55`
(`fn _take_many(budget: GposDataBudget, count: i64) -> bool: ... budget.remaining
= budget.remaining - count`) — same shape, same missing annotation, and the
JIT compile got **past** that file without error before reaching this one.
Grepped the whole `src/lib/skia` tree for any precedent of a `mut`-annotated
class parameter (`budget: mut _LayoutBudget` or similar) to find the correct
fix syntax: **zero results** — this exact mutate-a-class-parameter-in-place
pattern is the codebase's normal, apparently-accepted idiom throughout, with
no established `mut`-parameter syntax to mirror.

**This is reported as the next blocker, not fixed, per the standing
constraint and this session's own "don't guess at unfamiliar
capability-system syntax" discipline** — the discrepancy between `_take` and
the seemingly-identical `_take_many` (one errors, one doesn't) suggests
either a real aliasing/capability-inference difference specific to this call
site that isn't visible from the two functions' text alone (worth a
`SIMPLE_DEBUG`-style trace of the capability inference pass, not attempted
this pass), or a JIT-lowering-specific false positive. **No source-side
parenthesization-style workaround is known for this class** (unlike
`CastElse`) — this is a `ReferenceCapability`/memory-safety-pass question,
not a parser-precedence one, and guessing at `mut`-syntax without a working
precedent risks introducing a worse, silently-wrong capability annotation.

### Pinning spec landed for the `CastElse` dual-engine correctness bug

Per instruction, added
`test/01_unit/bugs/cast_else_swallows_outer_if_spec.spl` — 4 examples: the
naked (buggy) form's true-branch behavior, the naked form's false-branch
**wrong** behavior (asserted as `!= 0`, a deliberate "vacuity probe": if a
future parser fix ever makes this equal `0`, the assertion flips and the
spec must be updated, rather than silently staying green for the wrong
reason), and the parenthesized workaround's both branches (asserted
correct). **Run via the real test runner (PROVED): 4 examples, 0
failures.**

## Validation performed this follow-up pass

- `text_align_v` root cause and fix: PROVED (code reading, direct
  before/after repro against the real pipeline).
- Fourth gap (`W1006` mutation-capability error in `_take`): PROVED to
  exist and block; root cause NOT established (the `_take`-vs-`_take_many`
  discrepancy is a real, unresolved puzzle, reported precisely rather than
  guessed at).
- Pinning spec: PROVED — 4/4 passing via the real test runner, and its
  underlying assertions independently cross-checked against a raw
  interpreter run showing `nil` for the naked false-branch and `0` for the
  parenthesized one.
