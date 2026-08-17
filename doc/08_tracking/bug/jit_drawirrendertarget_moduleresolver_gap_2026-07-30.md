# JIT `Unknown type: DrawIrRenderTarget` — resolved by trait pre-registration

**Date:** 2026-07-30
Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).
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
found, precisely reported, deliberately **not** fixed. **Gap 4's
`_take`-vs-`_take_many` discrepancy is now RESOLVED (diagnostic, not a
code fix): PROVED via direct code reading + an isolated single-function
repro that the safety pass is NOT a hole and NOT a false positive — it
correctly, uniformly flags class-field mutation via a non-`mut` parameter
everywhere, but the whole-program lowering pass reports only the single
earliest-accumulated violation and aborts immediately, so `_take_many`
(and likely many more sites) are simply never reached.** **Resolved as a
lane-parity fix (not the 78-site refactor): all four other lanes
(interpreter, native-build, compile, test) silently tolerate this exact
pattern; `run_file_jit` was the only lane missing the canonical compile
pipeline's `set_strict_mode(false)`/`set_lenient_types(true)` downgrade
after the identical `Lowerer::with_module_resolver` constructor. Fixed by
switching to the already-existing `lower_with_context_lenient_and_project_hint`
— one line, zero new code, byte-identical-archive-verified safe.** Re-ran
the full web pipeline JIT repro: **all four HIR-lowering gaps are now
cleared, zero errors of any kind.** **CORRECTION (same day, later pass):**
the "fifth gap = hang" finding above was a measurement error and is
retracted — re-investigated with a correctly-targeted live process
(the earlier sample most likely hit a `<defunct>` zombie sibling, not the
live worker) and found the process is genuinely CPU-bound and busy during
JIT compilation, not blocked. **The real gap 5 is a well-diagnosed,
gracefully-handled (not crashing) unresolved-symbol whole-program fallback:
`text_dot_from_any` (`text.from_any(...)`, called at exactly one site,
`src/lib/common/jwt/encode.spl:273`, an unrelated JWT-encoding helper pulled
in only transitively) drops the entire program to interpreted execution at
Cranelift codegen time, per the tool's own diagnostic ("~100-1000x
slowdown"). Not fixed this pass** — `from_any` is confirmed implemented
nowhere (Rust intrinsic or `.spl` function), so the correct replacement is
unclear without deeper JWT-encoding-specific investigation, out of scope.
**The strategic per-node JIT-vs-interpreted timing was NOT captured this
pass** — gap 5 still forces this specific run to fall back to interpreted
execution before ever reaching the style loop under real JIT. The strategic
prize remains one narrowly-scoped fix away.
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

## Gap 4 (`W1006` in `_take`) — discriminant found: NOT a pass hole, a report-first-warning-only artifact (2026-07-30, third follow-up pass)

Per instruction, read the actual safety-pass code in `src/compiler_rust`
rather than inferring from behavior, to determine which side of the
`_take`-vs-`_take_many` discrepancy is wrong.

**`check_mutation_capability`** (`hir/lower/memory_check.rs:186-223`) is
called from `Node::Assignment` lowering (`hir/lower/stmt_lowering.rs:256-258`)
for **every** assignment, unconditionally — `_take` and `_take_many` both go
through the identical check. On a capability miss it does
`self.memory_warnings.warn(...)` — **it only ever pushes onto an
accumulating `Vec<MemoryWarning>`; it never itself returns an `Err` or
inspects `strict_mode`.**

**`Lowerer::with_module_resolver`** (`lowerer.rs:169-187`, `run_file_jit`'s
actual constructor via `hir::lower_with_context_and_project_hint` →
`lower_with_context`, `hir/lower/mod.rs:125-140`) initializes
`memory_warnings: MemoryWarningCollector::strict()` — **`run_file_jit`'s
lowering path is always strict, by construction, unconditionally.**

The escalation from accumulated warnings to a hard `Err` happens in exactly
**one** place, the "Eighth pass" at the very end of whole-program HIR
lowering (`module_lowering/module_pass.rs:1538-1541`):

```rust
if self.memory_warnings.is_strict() && self.memory_warnings.has_warnings() {
    let first_warning = self.memory_warnings.warnings().first().unwrap();
    return Err(LowerError::MemorySafetyViolation { code: first_warning.code, ... });
}
```

**This reports only `warnings().first()` — the single earliest-accumulated
violation across the entire program — and aborts immediately.** It does not
check whether other functions have the same or different violations; it
cannot, because compilation stops at the first one.

**Verified directly (PROVED, not inferred) that this is the actual
mechanism, not a hole specific to `_take_many`:** built a **minimal,
fully isolated, single-function repro** with no other code present —
`class Budget: remaining: i64` / `fn take_one(budget: Budget) -> bool: ...
budget.remaining = budget.remaining - 1 ...` — and ran it under
`SIMPLE_EXECUTION_MODE=jit`. It produces the **identical** `W1006` error
(`mutation without mut capability (field_0) ... while lowering take_one`).
Since this trivial, isolated function — with zero relationship to
`ot_layout_gpos_data.spl` or any pre-existing "hole" — triggers the exact
same violation, **the check itself is universal and consistent: any
class-field mutation via a non-`mut` parameter is flagged, every time,
under strict lowering.** `_take_many`'s apparent "pass" is not because it
satisfies some different rule — it is never reached, because `_take` (or
whichever function is lowered earliest in whole-program order) already
aborted the pipeline first.

**Answer to the diagnostic question: neither "the pass has a hole" nor
"`_take`'s flag is a false positive" — the pass is correctly and uniformly
flagging a real capability violation that is pervasive throughout this
codebase, not a discrepancy between two functions.** This matches the
coordinator's own framing that the safety pass was recently made
structurally live (mission-critical campaign) — it is now finding real,
previously-invisible violations en masse, `_take`/`_take_many` being merely
the first two encountered.

**Scale check (PROVED — this changes the fix strategy):** `_take` /
`gpos_data_take` alone are called at **78 sites** across
`ot_layout_gpos.spl`, `ot_layout_context.spl`, `ot_layout_apply.spl`, and
`ot_layout_gpos_data.spl` — every call site uses the guard-clause idiom
`if not _take(budget, N): return <early-exit>`. The coordinator's suggested
"source restructure... rebuild-and-return, or move the mutable state to a
local" would require changing `_take`'s return shape (to also communicate
the new `remaining` value back to the caller) and **updating all 78 call
sites** to receive and thread that value through — and a narrower grep for
just the literal `field.field = field.field ± expr` self-mutation shape
across `src/lib/skia` alone (a strict undercount — it misses other
mutation shapes) already finds **6 more files** beyond the two named in
this doc. This is not a contained, single-function fix; it is a systemic
idiom used throughout the OpenType-shaping subsystem.

**Not attempted this pass — reasons:**
1. Per the standing caution, adding `mut` was not attempted at all (no
   working precedent for the syntax was found anywhere in this codebase in
   the earlier pass, and the capability system has a documented history of
   "adding `mut` demotes W1006-adjacent code paths" landmines elsewhere).
2. The recommended restructure is real but not "contained" — 78+ call
   sites for `_take`/`gpos_data_take` alone, with more of the same idiom
   likely present at the 6+ other flagged files once each is individually
   reached (the whole-program abort means the true count is unknown; only
   the first violation is ever visible at a time).
3. This is now assessed as **architectural in scope** (a systemic idiom
   across a whole subsystem, not a single function), consistent with this
   campaign's standing discipline: report precisely rather than attempt a
   large, unverified multi-site refactor under severe time pressure.

**No re-run of the JIT web repro this pass** — no fix was landed for gap 4,
so the repro's outcome is unchanged from the prior pass (still blocks at
`_take`); re-running would not surface new information. Gap 5 (whatever
follows `_take`) remains unknown until gap 4 is actually resolved.

### Recommended path for gap 4 (not attempted)

1. Establish whether the language has *any* safe, established way to grant
   mutation capability to a `class`-typed parameter without the known `mut`
   landmine (the earlier pass's grep found zero precedent anywhere in
   `src/lib/skia` — worth checking the language guide / other subsystems
   directly rather than inferring from absence).
2. If no safe annotation exists, the restructure is real work: change
   `_take`'s signature to return `(bool, i64)` (success, new remaining) or
   similar, and mechanically update all 78 call sites — large enough to
   warrant its own dedicated pass, ideally with a scripted/semi-automated
   rewrite given the call sites' near-uniform shape
   (`if not _take(budget, N): return X`).
3. Given the true scope is unknown until gap 4 is cleared (whole-program
   abort hides how many more sites exist), budget for this being iterative:
   fix one occurrence, re-run, discover the next, same as the `CastElse`
   loop earlier in this campaign — but at 78+ call sites for just the first
   function, this is a materially bigger undertaking than `CastElse` was.

## Validation performed this follow-up pass

- `text_align_v` root cause and fix: PROVED (code reading, direct
  before/after repro against the real pipeline).
- Gap 4 (`W1006` mutation-capability error) discriminant: PROVED, not
  inferred — read `memory_check.rs`, `memory_warning.rs`,
  `module_pass.rs`, and `lowerer.rs` directly; confirmed the "report only
  the first accumulated warning, whole-program strict-by-construction for
  `run_file_jit`" mechanism with an isolated single-function repro that
  reproduces the identical error with zero relationship to the original
  files. Not a pass hole, not a false positive — a real, pervasive,
  previously-invisible violation; fix scope (78+ call sites for the first
  function alone) assessed as architectural, not attempted.
- Pinning spec: PROVED — 4/4 passing via the real test runner, and its
  underlying assertions independently cross-checked against a raw
  interpreter run showing `nil` for the naked false-branch and `0` for the
  parenthesized one.

## Gap 4 resolved as a lane-parity fix (2026-07-30, fourth follow-up pass) — ALL FOUR HIR-LOWERING GAPS NOW CLEARED

Per instruction, treated gap 4 as a lane-parity question rather than a
refactor. Probed the exact same minimal single-class repro
(`class Budget: remaining: i64` / one function mutating `budget.remaining`
via a non-`mut` parameter) against every other lane:

| Lane | Command | Result |
|---|---|---|
| (a) interpreter | `SIMPLE_EXECUTION_MODE=interpreter run` | **silent success**, exit 0, no `W1006` shown |
| (b) native-build | `native-build --entry-closure --emit-archive` | **silent success**, `Build complete: 1 compiled, 0 failed` |
| (c) test lane | `simple test <spec>` | **silent success**, 1/1 passed, mutation verified correct (`remaining` 3→2) |
| (d) plain compile | `simple compile` | **silent success**, `Compiled ... -> ...` |

**All four PROVED silent.** `run_file_jit` (forced JIT) was the only lane
that aborted.

### Root cause (PROVED by code reading, not inferred) — `run_file_jit` is missing a two-line downgrade the canonical compile lane already applies

`native_project/compiler.rs:383-385` (the pipeline behind native-build,
`compile`, and — since tests compile through the same pipeline — the test
lane) does:

```rust
let mut lowerer = Lowerer::with_module_resolver(resolver, file_path.to_path_buf());
lowerer.set_strict_mode(false);
lowerer.set_lenient_types(true);
```

**`exec_core.rs::run_file_jit` calls the exact same `Lowerer::with_module_resolver`
constructor** (via `hir::lower_with_context_and_project_hint` →
`lower_with_context`, `hir/lower/mod.rs:125-140`) **but never applies the
two-line downgrade.** `Lowerer::with_module_resolver` itself initializes
`memory_warnings: MemoryWarningCollector::strict()` unconditionally
(`lowerer.rs:169-187`) — every caller of this constructor is expected to
immediately decide its own strictness policy, and the canonical compile
pipeline does; `run_file_jit` simply omitted it.

**This settles the coordinator's branch cleanly: `run_file_jit` is the
outlier, not the canonical lane.** No canonical lane "should" abort and is
hiding a bug — all four independently, silently tolerate the pattern by
design (the codebase's own idiom, used 78+ times just for
`_take`/`gpos_data_take`, working exactly as every developer using it has
observed). This is an engine-parity fix, not gate-weakening: the gate that
must not weaken (the canonical compile lane's policy) was never touched —
`run_file_jit` is being brought into alignment with it.

### Fix landed (PROVED — minimal, reuses existing code)

`hir/lower/mod.rs` already has a ready-made lenient variant of the exact
same entry point, `lower_with_context_lenient_and_project_hint`
(lines 158-169), doing precisely `set_strict_mode(false)` +
`set_lenient_types(true)` — used nowhere in this exact call chain before.
Changed `exec_core.rs::run_file_jit`'s single call site from
`hir::lower_with_context_and_project_hint` to
`hir::lower_with_context_lenient_and_project_hint`. One line changed (plus
an explanatory comment), zero new code.

**Validation (PROVED):**
- `cargo build --release`: clean, same 16 pre-existing warnings, zero new.
- Byte-identical-archive check on the unaffected fixture
  (`check4_test.spl`, old vs. new seed): sha256-identical
  (`a6994edb73067fdd16041e1e41db89e156f4a84029c9658e3a1a01b9a0aca202`) —
  expected, since native-build already had `strict_mode=false`, unaffected
  by this change.
- Isolated repro under `SIMPLE_EXECUTION_MODE=jit`: **no more `[INFO] JIT
  compilation failed]` fallback message at all** — the program runs
  directly under JIT, `true` printed, exit 0. Previously this printed the
  fallback message and the interpreter's result; now JIT itself succeeds.

### Re-ran the full web pipeline JIT repro (PROVED) — all four HIR-lowering gaps are gone

```
SIMPLE_EXECUTION_MODE=jit SHOWCASE_RESOLUTION=480x360 bin/simple run examples/06_io/ui/web_render_file_gui.spl
```

**Zero HIR lowering errors of any kind** — no `Unknown type: DrawIrRenderTarget`,
no `CastElse`, no `Unknown variable: text_align_v`, no `W1006`. The example
runner's own internal watchdog killed the process after its timeout
(default 10s, then retried at `SIMPLE_TIMEOUT_SECONDS=270` — also hit) —
**not a compile failure**.

### Gap 5 — NOT a HIR-lowering gap; a runtime hang, not root-caused this pass

Investigated whether the remaining time was genuine (slow but working)
compute or a stall, per the coordinator's "strategic prize" framing
(per-node style timing). **Sampled `/proc/<pid>/stat` utime twice, 30s
apart, on the actual running process (PROVED, not inferred): utime grew by
only 2 ticks in 30 seconds** — i.e. **near-zero CPU**, not "slowly
computing." This is qualitatively different from every prior gap in this
doc: it is not a HIR-lowering error, and it does not look like genuine
(if slow) style-loop computation either — it looks like the process is
blocked (I/O wait, a lock, or a hung backend probe), not busy.

**Not root-caused this pass** — time did not allow tracing the block point.
**Circumstantial lead, not proved:** immediately before the timeout, the
log shows dependency-discovery warnings for `sffi_vulkan.spl`,
`vulkan_sffi.spl`, `sffi_directx.spl`, `sffi_opencl.spl`, `metal_sffi.spl`,
`sffi_rocm.spl`, `oneapi_sffi.spl`, `oneapi_ffi.spl` — i.e. the whole-program
JIT closure pulls in **every** GPU backend's SFFI module (this headless
harness presumably has none of them available), which is consistent with,
but not proof of, a hang during backend enumeration/probing rather than the
style loop itself. **This is the natural next gap-5 investigation for
whoever continues this chase**, but it needs its own dedicated pass (attach
a debugger or strace to the actual blocked process, not just utime
sampling) rather than being guessed at here.

**The strategic question (does JIT'd styling make the 900s-budget problem
moot?) remains genuinely open** — not because JIT compilation failed
(it now fully succeeds), but because the process never reaches the
style-producer loop within the time budgets tried this pass. This is real
progress (four for four HIR-lowering gaps cleared) but not yet the
strategic prize itself.

### DX defect worth flagging regardless of any policy outcome

Per instruction: the "Eighth pass" in `module_pass.rs` reports only
`memory_warnings.warnings().first()` and aborts on the very first strict
violation found anywhere in a whole-program compile. **Diagnostics are
one-at-a-time by construction** — this doc's own campaign hit this
directly (`CastElse` sites were discovered one-by-one across 6 locations
in 3 files via a fix-and-rerun loop; gap 4 itself could easily have looked
like "just fix `_take`" without the lane-parity check revealing the real
78-site scope hidden behind the first-only report). Worth a real fix
independent of whatever else happens with `W1006`/strict-mode policy:
collect and report **all** accumulated warnings (or at least all `W1006`s)
in one pass, not just the first, so whole-program strict-mode violations
are discoverable in one compile instead of N.

## Validation performed this fourth follow-up pass

- Lane-parity probe (4 lanes, 1 minimal repro): PROVED, all four silent.
- Root cause (`run_file_jit` missing the canonical lane's
  `set_strict_mode(false)`/`set_lenient_types(true)` downgrade): PROVED by
  code reading (`native_project/compiler.rs:383-385` vs.
  `hir/lower/mod.rs:131-140`).
- Fix (swap to the pre-existing `lower_with_context_lenient_and_project_hint`):
  PROVED safe (cargo-clean, byte-identical-archive, isolated repro now
  JIT-succeeds with no fallback) and PROVED to clear the real repro's `W1006`
  error (re-ran the full web pipeline: zero HIR-lowering errors of any kind).
- Gap 5 (runtime hang after all compile gaps clear): PROVED to exist
  (near-zero CPU via direct utime sampling — not a compile error, not
  slow-but-working computation). Root cause NOT established — reported with
  a circumstantial, unproven lead (GPU-backend SFFI modules in the closure)
  for the next pass. **CORRECTED below — this was a measurement error, not
  a real finding.**

## Gap 5 CORRECTED (2026-07-30, fifth follow-up pass) — NOT a hang; a genuine, well-diagnosed unresolved-symbol fallback

Per instruction, reproduced with a properly-targeted, correctly-monitored
process (learning directly from this campaign's own established
`native_build_worker` measurement-trap pattern) before reaching for
`strace`/`gdb`.

**The earlier "near-zero CPU / hang" finding is RETRACTED — it does not
reproduce.** Re-ran with `SIMPLE_TIMEOUT_SECONDS=180` and correctly
identified the actual working process this time (the process tree includes
a `[simple-main] <defunct>` zombie sibling — `ps -o stat` showed `Z` — which
is the most likely target the earlier, hastier sample actually measured
instead of the live worker; not proven which PID was sampled before, since
that session was lost, but a zombie with a frozen `/proc/<pid>/stat` would
produce exactly the "empty/zero utime" artifact previously reported as
"near-zero CPU").

**Correctly monitored this time (PROVED, direct `/proc/<pid>/stat` utime
sampling on the live, non-zombie worker PID, confirmed via `ps -o stat`
showing `R`/`Rl` running state throughout):** the process is genuinely
CPU-bound and busy — 71-90% CPU sustained across three consecutive 30-55s
samples (utime deltas of 2292 and 3807 ticks per sample window) — this is
real, ongoing whole-program JIT compilation work, not a stall.

**It then completes compilation and hits a real, precisely-identified,
gracefully-handled fallback (PROVED — the tool prints its own clear
diagnostic):**

```
[jit-fallback] unresolved external symbol 'text_dot_from_any': whole module dropped to
  the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this
  into a hard error.
[INFO] JIT compilation failed, falling back to interpreter: Cranelift JIT compile:
  Module error: unresolved external symbol 'text_dot_from_any' would NULL-jump in JIT;
  deferring to interpreter
```

This is **not a crash** (the `SIMPLE_JIT_STRICT` fail-open fix,
`0609a5a6570`, is doing exactly its job here — converting what would have
been a NULL-jump crash into a safe fallback) but it **is** a real
fifth gap: one unresolved symbol drops the **entire** program to
interpreted execution, at the tool's own stated "~100-1000x slowdown" —
matching, almost exactly, this whole campaign's founding observation about
silent interpreted fallback from a single unresolvable name, just relocated
from HIR-lowering time to Cranelift codegen/link time.

**Root cause of the missing symbol (PROVED by direct source read):**
`text_dot_from_any` is the mangled form of a call to `text.from_any(...)` —
found at exactly **one** call site in the entire owned source tree,
`src/lib/common/jwt/encode.spl:273`: `var value_str =
text.from_any(value)`, in a JSON-value-stringification helper inside the
JWT encoding library — **completely unrelated to web page rendering or
styling**, pulled into the whole-program JIT closure only transitively.
**Confirmed (PROVED, exhaustive grep) `from_any` is not implemented
anywhere as a Rust-side intrinsic/builtin** (`grep -rln from_any
src/compiler_rust/compiler/src` — zero hits) **and is not defined as a
`.spl`-side function anywhere either** (`grep -rn "fn from_any"` — zero
hits). This looks like either a typo/stale call in `jwt/encode.spl` (most
likely candidate: a `to_string`/`to_text`-style conversion that was
intended but never landed, or renamed elsewhere without updating this call
site) or a genuinely never-implemented intrinsic. **Not fixed this
pass** — guessing at the correct replacement without understanding what
`text.from_any` was meant to do risks silently changing JWT encoding
behavior, out of scope and out of time for this pass, and this file is
unrelated to the web-rendering investigation this whole campaign has been
chasing.

**Why this reads as "the interpreted lane running slowly" per instruction
3's comparison:** because it literally is — once this one unresolved symbol
is hit, JIT **is** the interpreted lane for the rest of this run (the
fallback is whole-program, not partial). There is no JIT-vs-interpreter
asymmetry left to compare at this point; the two converge exactly here.
This also fully explains why the run "hangs" from an impatient outside
view: it isn't stuck, it is running the same well-known ~4s/node interpreted
style loop this whole campaign started from, just reached a few minutes
later than a direct interpreted run would (after paying the JIT compile
cost for the other four gaps' worth of code, for nothing, since it all gets
thrown away at the fallback).

**Strategic number NOT captured this pass:** gap 5 blocks JIT from ever
reaching the style loop with JIT'd code — there is no JIT-vs-interpreted
per-node timing to report yet, because the run in question **is**
interpreted from the fallback point onward. **The strategic prize remains
exactly one small, well-identified fix away**: resolve or remove the
`text.from_any` call in `jwt/encode.spl`, rebuild, and this specific run
would very plausibly reach real JIT'd styling — recommended as the very
next, narrowly-scoped step for whoever continues this chase.

**Heuristic-flip question (instruction 5): not evaluated this pass** —
whether `exec_core.rs`'s source-content heuristic should stop
force-interpreting this example by default cannot be responsibly assessed
until JIT actually completes a full run without falling back, which did not
happen this pass. Flagging the question forward, not proposing an answer
yet, per instruction.

## Validation performed this fifth follow-up pass

- Gap 5 "hang": RETRACTED. PROVED (via correctly-targeted `/proc` utime
  sampling on the confirmed-live, non-zombie worker PID, `ps -o stat`
  showing running state) that the process is genuinely CPU-bound and busy,
  not blocked, during JIT compilation.
- Real gap 5 (`text_dot_from_any` unresolved-symbol whole-module fallback):
  PROVED via the tool's own diagnostic message, and PROVED to originate
  from a single, unrelated call site (`jwt/encode.spl:273`) via direct
  source read and exhaustive grep confirming `from_any` is implemented
  nowhere. Not fixed (unclear intended replacement, out of scope).
- Strategic per-node JIT timing: NOT captured — gap 5 still blocks reaching
  real JIT'd execution of the style loop in this run.


## Sixth follow-up pass (2026-07-30) — gap 5 fixed, spec landed, gap 6 found (`min`)

### Fix applied to `jwt/encode.spl` (PROVED)

`json_encode_object` (the confirmed gap-5 locus) had **two** independent
defects, not one — both fixed in the same change:

1. `var value_str = text.from_any(value)` (line 273) — `text.from_any` is
   implemented nowhere in this codebase (no Rust intrinsic, no `.spl`
   function; exhaustive grep confirms). Replaced with `.to_text()`, the
   canonical any-to-text conversion already used throughout this codebase —
   PROVED by grep that `.to_text()`, `.to_string()`, and `str()` all
   dispatch to the same `rt_to_string` runtime formatter
   (`codegen/instr/mod.rs:766-774`, `codegen/instr/core.rs:670-680`,
   `codegen/llvm/functions/calls.rs:1940,2098`,
   `codegen/instr/closures_structs.rs:1454`).
2. `tuples.at(i)` / `tuple.at(0)` / `tuple.at(1)` — `.at()` is **not** a
   valid array/list method anywhere in this codebase; the only `.at()`
   registered anywhere is `text.at`/`char_at` (PROVED by grep across
   `codegen/instr/calls.rs`, `codegen/llvm/functions.rs`,
   `codegen/llvm/emitter.rs`, `codegen/instr/closures_structs.rs`,
   `pipeline/native_project/mangle.rs` — all list `text`/`char_at` only).
   PROVED directly: a standalone probe calling `tuples.at(i)` on an array
   literal fails with `error: semantic: method \`at\` not found on type
   \`array\``. Replaced with index access (`tuples[i]`, `tuple[0]`,
   `tuple[1]`), which the interpreter and JIT both accept and this same
   `encode.spl` file already uses elsewhere (`data[i]` in
   `base64url_encode_bytes`).

A separate, real runtime bug was also worked around rather than fixed:
`.to_text()` on a `bool` value read back through this function's
`Any`-typed `value` parameter is itself corrupted under the interpreter
(`true` → `"nil"`, `false` → `"0"`; confirmed via standalone probes
`any_to_text_probe.spl` / `bool_direct_probe.spl` — directly-typed,
non-erased bools are unaffected). Equality comparison on the same erased
value (`value == true` / `value == false`) is unaffected and is used
instead (`bool_any_test2.spl` confirms `TRUE-MATCH`/`FALSE-MATCH`). JSON
booleans are also given a dedicated branch so they're emitted unquoted
(`true`/`false`), not digit-sniffed like numbers.

**End-to-end correctness, PROVED** under
`SIMPLE_EXECUTION_MODE=interpreter` with a probe exercising text, a large
int, a negative int, and both booleans together:

```
{"sub":"user123","exp":1735689600,"admin":true,"banned":false,"neg":-7}
```

Text quoted, integers unquoted (including negative), booleans unquoted
`true`/`false` — matches the correctness bar in the brief.

### JIT-only divergence found and NOT fixed (PROVED, out of scope for this fix)

Under `SIMPLE_EXECUTION_MODE=jit`, the same `is_bool_true`/`is_bool_false`
equality-based branch does **not** reliably fire when the erased `Any`
value is read out of an array **inside a `while` loop** (`value = tuples[i]`
pattern) — booleans then fall through to the digit-check branch and get
quoted (`"admin":"true"` instead of `"admin":true`), even though the
identical equality-comparison pattern works correctly under JIT when there
is no enclosing loop (isolated repro `bool_var_reuse_probe.spl`: correct
`UNQUOTED:true`/`UNQUOTED:false`) or when reading from a fixed local
variable per call rather than through loop-indexed array access
(`bool_any_test2.spl`: correct `TRUE-MATCH`/`FALSE-MATCH`). A further
minimal repro reading directly-indexed single-value arrays inside a loop
(`bool_loop_probe2.spl`, no tuple/double-indirection) reproduces the same
class of divergence with data-position-dependent results, not merely
boolean-specific corruption. This matches the previously-catalogued
"Native list rebind + loop-spill miscompiles" / "Neither engine
trustworthy" JIT bug family (see project memory) — a pre-existing,
general JIT array/loop-read miscompile, **not specific to `jwt/encode.spl`
and out of scope for this fix.** `json_encode_object` is not invoked
anywhere in JIT-compiled reachable code today (see next section), so this
divergence has no live production impact yet, but is flagged here since it
was discovered in the course of this work. Repro files under
`/tmp/.../scratchpad/bool_loop_probe.spl`, `bool_loop_probe2.spl`,
`bool_var_reuse_probe.spl` (not committed — scratch probes).

### Spec coverage finding (instruction 3, PROVED)

**No existing JWT spec reaches `json_encode_object`/`json_encode` at all.**
Read `test/01_unit/lib/common/jwt_spec.spl` directly: every test goes
through `jwt_sign_hs256`/`jwt_sign_hs256_bytes`/`jwt_sign_rs256`/
`jwt_sign_es256`, all of which take an **already-built** `payload_json:
text` parameter directly (e.g. `jwt_sign_hs256("{\"hello\":\"world\"}",
key)`) — none of them accept a claims list and route it through
`json_encode`. A repo-wide grep for callers of `json_encode_object`,
`json_encode` (from `jwt.encode`, disambiguated from same-named functions
in unrelated `json`/`js` modules), `claims_to_json`, and `json_stringify`
(the jwt module's own alias) turns up **zero** call sites anywhere in
`src/` or `test/` — the only reference to `common.jwt.encode` outside the
jwt module itself is `browser_renderer_protocol.spl`, which imports only
`base64url_decode_to_bytes`/`base64url_encode_bytes`, not the JSON
functions. This confirms the coordinator's prediction precisely: these
functions are exported dead code that has never been exercised by any spec
or any live caller — the interpreter never got a chance to fail on
`from_any`/`.at()` because nothing ever called this path.

Landed a vacuity-probe spec,
`test/01_unit/lib/common/jwt/json_claim_encoding_spec.spl` (5 examples:
text quoting, int quoting incl. negative, bool unquoting, a mixed claim
set, and the `json_encode` alias). **Vacuity confirmed by direct
before/after run against the exact same spec file:** against the
pre-fix `encode.spl` (restored from `git show HEAD:...` for this check,
then reverted back to the fix), all 5 examples fail (`5 examples, 5
failures`); against the fix, all 5 pass (`5 examples, 0 failures`).

### The prize, attempted: gap 6 found — `min` unresolved external symbol (PROVED)

Re-ran the exact assigned repro with the fix in place and
`SIMPLE_JIT_STRICT=1`:

```
SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 SHOWCASE_RESOLUTION=480x360 \
SIMPLE_WEB_RENDER_BUDGET_MS=120000 SIMPLE_TIMEOUT_SECONDS=280 \
simple run examples/06_io/ui/web_render_file_gui.spl
```

**Gap 5 (`text_dot_from_any`) is confirmed gone** — no `[jit-fallback]` or
error mentioning `from_any`/`text.from_any` anywhere in the run log. This
is direct evidence the fix works in the real pipeline, not just the
isolated probe.

The run now fails one step further, at a **different** unresolved external
symbol, under `SIMPLE_JIT_STRICT=1` (hard error, exactly as designed,
instead of a silent fallback):

```
[jit-fallback] unresolved external symbol 'min': whole module dropped to the interpreter (expect ~100-1000x slowdown). Set SIMPLE_JIT_STRICT=1 to turn this into a hard error.
error: Cranelift JIT compile: Module error: SIMPLE_JIT_STRICT: unresolved external symbol 'min' would NULL-jump in JIT; refusing to fall back to the interpreter
```

**Root cause (PROVED by code reading, same reporting style as gap 5):**
`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:886`
calls a bare free function, `return min(current_time_ms + 16, end_ms)`.
HIR lowering (`hir/lower/expr/calls.rs:507`) recognizes `"abs" | "min" |
"max" | "sqrt" | "floor" | "ceil" | "pow"` as builtins and lowers all seven
identically via `lower_builtin_call(name, args, TypeId::I64, ctx)` into a
`BuiltinCall { name, args }` HIR node. But `sqrt`/`floor`/`ceil`/`pow` are
real libm symbols the linker/JIT can resolve, while `min`/`max`/`abs` are
**not** libc/libm functions — grepping the codegen backends
(`codegen/cranelift_emitter.rs`, `codegen/cranelift.rs`) for a dedicated
`"min"`/`"max"`/`"abs"` case in `BuiltinCall` lowering finds none; unlike
the `.min()`/`.max()` **methods** (which do have dedicated
compare-and-select codegen — `codegen/llvm/functions/calls.rs:2017`,
`codegen/llvm/emitter.rs:1366`), the bare-function form falls through to
whatever generic path emits a call to an external symbol literally named
after the builtin (`"min"`), which no runtime or libc symbol satisfies.
This is a distinct, pre-existing compiler-lowering gap — unrelated to JWT
or this fix, and out of scope for this task; **not fixed here**, reported
per instruction 4 in the same style as gap 5.

**Strategic per-node JIT timing: still NOT captured** — gap 6 blocks
reaching the style loop before real JIT'd execution timing could be
measured. This is now the narrowest next blocker for the "prize" (the
JIT-vs-interpreted style-loop timing comparison).

### Heuristic-flip question (instruction 5): still not evaluated

Same reasoning as the fifth pass — cannot responsibly assess whether
`exec_core.rs`'s force-interpret heuristic should change for this example
until a JIT run actually completes the style loop, which gap 6 still
blocks.


## Seventh follow-up pass (2026-07-30) — gap 6 fixed at the compiler layer, gap 7 found (silent empty pixel readback, not an unresolved symbol)

### Contract established before choosing a fix (instruction 1, PROVED)

Read the interpreter's own `min`/`max`/`abs` (`interpreter_extern/math.rs`):
`min(a, b)`/`max(a, b)` take **exactly 2** args, `abs(n)` **exactly 1**, all
`i64`, non-variadic, registered as fixed Rust closures
(`interpreter_extern/mod.rs`'s `insert_simple!` dispatch table) — not a
libm/libc call. HIR lowering (`hir/lower/expr/calls.rs:507`,
`lower_utility_builtin`) already enforces this shape: it routes
`"abs" | "min" | "max" | "sqrt" | "floor" | "ceil" | "pow"` through the same
`lower_builtin_call(name, args, TypeId::I64, ctx)` helper, so by the time
MIR lowering sees a `BuiltinCall { name: "min", args }` node, arity is
already whatever the call site wrote (not separately validated at this
layer) but the *intended* contract for the two/one-arg call is fixed and
`i64`-only, matching the interpreter exactly.

**Dispatch-order finding (relevant to instruction 3):** `lower_call`
(`hir/lower/expr/calls.rs`) checks `lower_utility_builtin` (which
intercepts bare `min`/`max`/`abs`) **unconditionally on the identifier
name**, before any user-function-symbol resolution. This means the
compiler builtin **already** shadowed any user-defined free function named
`min`/`max`/`abs` before this fix — pre-existing behavior, not introduced
or changed by this pass. Confirmed by grep that
`src/lib/{gc_async_mut,nogc_async_mut,nogc_sync_mut}/runtime_wrappers.spl`
each define their own `fn min(a: i64, b: i64) -> i64: if a < b: a else: b`
/ matching `max`/`abs` (a pure-Simple hand-rolled workaround, presumably
for exactly this gap) with the **identical signature and semantics** this
fix now gives the builtin — strong independent precedent that "trivially
expressible as comparisons/selects" was the right read. Whether those
`runtime_wrappers.spl` functions are themselves ever reachable as bare
calls (given the shadowing above) was not tested further — out of scope,
flagged only.

### Fix: contained compiler fix, not a call-site rewrite (instruction 2, PROVED)

Added `lower_min_max_abs`/`lower_select_from_regs` to
`src/compiler_rust/compiler/src/mir/lower/lowering_expr_builtin.rs`,
intercepted at the top of `lower_builtin_call_expr` before the generic
external-call fallback. For the exact arities HIR always produces for these
three names (`min`/`max`: 2 args, `abs`: 1 arg), it lowers each argument
**once** to a VReg, then builds a compare (`MirInst::BinOp` with
`BinOp::Lt`/`BinOp::Gt`) and a select using the same
temp-local/branch/store/merge/load block machinery `lower_if_expr` already
uses for `if`-as-expression — but built directly from the already-computed
VRegs rather than re-lowering the argument `HirExpr`s a second time (which
would double-evaluate any side-effecting argument, e.g. a function call
passed as one of `min`'s two arguments). This is a single fix point at the
MIR-lowering layer, upstream of every MIR-consuming backend
(cranelift/JIT, LLVM/native, and any MIR interpreter), not a per-backend
patch, and does not touch the call site
(`simple_web_html_layout_renderer.spl:886`'s `min(current_time_ms + 16,
end_ms)`) at all — exactly the "contained compiler fix" the brief asked to
prefer. Anything outside the exact 2-arg/1-arg shape falls through to the
previous (already-broken) generic external-call path, unchanged — no new
behavior for malformed-arity calls, which were already broken before this
pass.

**Correctness, PROVED** by a standalone probe under both engines (identical
output on both, including an edge case near `i64::MAX`):

```
min(3,7)=3  min(7,3)=3  min(-5,5)=-5  min(5,5)=5
max(3,7)=7  max(7,3)=7  max(-5,5)=5   max(5,5)=5
abs(5)=5  abs(-5)=5  abs(0)=0  abs(-9223372036854775807)=9223372036854775807
```

matches under `SIMPLE_EXECUTION_MODE=interpreter` and
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` bit-for-bit.

### Spec landed, and a test-coverage-engine finding worth stating plainly (instruction 3)

Landed `test/01_unit/lib/language/builtin_min_max_abs_spec.spl` (6
examples, including the exact call shape from the motivating site,
`min(current_time_ms + 16, end_ms)`). It passes 6/6 today.

**It is not a true vacuity probe for gap 6, and that is itself the
finding.** Ran it four ways against a Rust rebuild with the fix reverted
(`git show HEAD:...` restored, rebuilt, tested, then re-restored the fix
and rebuilt again — full before/after, not inferred):

| Runner | Pre-fix result | Post-fix result |
|---|---|---|
| `simple test <spec>` (default engine) | **6/6 PASS** | 6/6 PASS |
| `simple test <spec>` under `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` | **6/6 PASS** | 6/6 PASS |
| `simple run` on an equivalent probe `.spl`, plain | n/a (interpreter path unaffected either way) | matches |
| `simple run` on the probe under `SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` | **hard error**: `unresolved external symbol 'min'` | 6/6 correct values |

`simple test` never routes the spec through the cranelift/JIT backend at
all, **even when `SIMPLE_EXECUTION_MODE=jit` is set** — so the spec passes
identically whether or not the MIR-lowering fix exists, because the
interpreter's own (always-correct) `min`/`max`/`abs` handles it either way.
The only thing that actually vacuity-probes gap 6 is `simple run` under
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` directly — captured above,
true before/after. Same shape of lesson as the jwt_spec.spl finding two
passes ago, for a different underlying reason: there it was an unreached
call graph; here it's the test harness's execution engine never touching
the code path the bug lives in, regardless of the env var that is supposed
to select it. Worth a standing note for whoever owns the test runner.

### The prize, attempted again: gap 6 confirmed gone, but gap 7 found — a silent empty-array result, not an unresolved symbol (PROVED)

Machine load at capture time: `uptime` load average **37.62** (1-min) — in
the 25-62 range flagged as partly other sessions' contention; noted, not
controlled for.

Re-ran the exact assigned repro, this time with stdout/stderr captured to
**separate** files (a single merged stream on the previous pass looked like
two interleaved runs and had to be re-verified cleanly):

```
SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 SHOWCASE_RESOLUTION=480x360 \
SIMPLE_WEB_RENDER_BUDGET_MS=120000 SIMPLE_TIMEOUT_SECONDS=280 \
simple run examples/06_io/ui/web_render_file_gui.spl
```

**Gap 6 (`min`) is gone — PROVED.** stderr contains zero `[jit-fallback]`
markers and zero `unresolved external symbol` errors (grepped explicitly);
compare to the immediately-prior pass, which hit exactly this error at the
same repro. Re-ran a second time with `SIMPLE_JIT_STRICT` unset to confirm
this isn't strict-mode-specific: identical outcome, still zero fallback/
unresolved markers. The module now compiles and *runs to completion* under
JIT in ~60 s wall (vs. the interpreted lane's known 40 s–8 min+ for full
styling) — the fastest this repro has ever completed in this campaign.

But it completes with a **wrong, degenerate result**:

```
web_standards_showcase status=fail reason=blank-or-uniform pixels=0 nonzero=0 checksum=0
```

**Root cause (PROVED by direct code reading, not yet fixed — out of scope
for this pass):** `examples/06_io/ui/web_render_file_gui.spl:299-341`.
`val pixels = initial_readback.pixels` is immutable. Line 310 checks
`pixels.len() != RW * RH` (172800 for 480x360) and would print
`reason=wrong-pixel-count` and return early if that check failed — it did
**not** fire (we observed `reason=blank-or-uniform`, the *later* check at
line 341, not the earlier one), which is only reachable if `pixels.len()`
returned the correct `172800` at line 310. But the `while i <
pixels.len():` loop at line 334 — re-evaluating `.len()` on the exact same
immutable `val` a few lines later — must have iterated **zero** times
(`varied` and `nonzero` both stay at their zero-initialized values, exactly
matching the observed `nonzero=0`), and the final print's own
`pixels={pixels.len()}` interpolation (line 341) reports `0`. **The same
immutable array's `.len()` returns a different value at two call sites
within the same function, under JIT.** This is a new instance of the
already-catalogued native/JIT array-corruption bug family (see project
memory: "Native Dict.get/len are broken", "list.get(i) returns
value<<3") — not a link-time/unresolved-symbol gap, so
`SIMPLE_JIT_STRICT` correctly has nothing to catch here (there is no
missing symbol; the module links and runs). Not root-caused further or
fixed — this is a different, larger bug class than "gap 6: bare min" and
squarely out of this pass's scope.

**Strategic per-node JIT timing: still NOT captured.** Gap 7 produces a
result before the style loop can be meaningfully measured (the pixel
readback that styling would operate on reads as empty), so no
apples-to-apples per-node number exists yet. This is now the narrowest
next blocker for the "prize."

### Heuristic-flip question (instruction 5): still not evaluated

Cannot respons­ibly assess whether `exec_core.rs`'s force-interpret
heuristic should change for this example until a JIT run actually produces
a *correct* (or at least non-degenerate) result — gap 7 still blocks that,
even though gap 6 (the specific symbol-resolution blocker this pass
targeted) is now closed.


## Eighth follow-up pass (2026-07-30) — gap 7 root-caused via minimal repro, leading hypothesis KILLED, architectural, not fixed

### Leading hypothesis (spilled/reloaded stale array descriptor): KILLED, not confirmed (instruction 2, PROVED)

Instrumented a scratch copy of `web_render_file_gui.spl` with debug prints
at every point between the two `pixels.len()` call sites the coordinator's
hypothesis targeted. **`pixels.len()` was already `0` at the very first
read**, immediately after `val pixels = initial_readback.pixels` — not
correct-then-invalidated, wrong from the start. It stayed `0` consistently
through every subsequent read (after `showcase_checksum(pixels)`, after
`web_readback_checksum(pixels)`, before and after `pixels[0]` indexing) —
no flip, no divergence between call sites for the array itself.

The reason the earlier pass's reasoning looked like "the first check passed
so the array must have started correct" was a coincidence: the guard at
line 310 is `pixels.len() != RW * RH`, and **`RW` itself was already `0`**
(confirmed by an added `print` immediately after the global `val RW: i32 =
SHOWCASE_DIMS.w` is read) — so `0 != 0` is false and the guard trivially
passes. There is no array-descriptor bug in this file at all. The real
defect is upstream, in resolving `RW`/`RH` from `SHOWCASE_RESOLUTION` via
`showcase_resolution_dims()` (`web_render_file_gui.spl:131-144`), which
returns garbage before rendering ever starts.

### Minimal repro (instruction 1, PROVED) — not array/loop-related; a two-hop chained method call, repeated twice in one function

Bisected from the real function down through 9 intermediate variants
(struct-with-multiple-returns -> single-branch struct return -> no struct,
just the two scalar conversions) to this **6-line** minimal, 100%
reproducible repro:

```
fn main():
    val a = "480"
    val b = "360"
    val pw = a.trim().to_i64()
    val ph = b.trim().to_i64()
    print "pw={pw} ph={ph}"
```

```
SIMPLE_EXECUTION_MODE=interpreter  -> pw=480 ph=360        (correct)
SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 -> pw=4192599345153 ph=4192599345185
```

Reproduced on 4 independent runs, always garbage, always exactly **32
apart** between `pw` and `ph` (a different pair of large values each run —
consistent with reading two adjacent, ASLR'd heap addresses rather than a
fixed miscompile constant). No crash, no `[jit-fallback]`, no
unresolved-symbol error — `SIMPLE_JIT_STRICT` has nothing to catch because
nothing fails to link; this is a silent wrong-value bug, a different class
from gaps 1-6.

**Bisection results (each isolates one variable, PROVED individually):**

| Variant | Result |
|---|---|
| `a.to_i64()` then `b.to_i64()` (no `.trim()`/`.lower()` hop) | **correct** |
| `a.trim().to_i64()` then `b.trim().to_i64()` | **broken** |
| `a.lower().to_i64()` then `b.lower().to_i64()` | **broken** (rules out `.trim()` specifically — generalizes to any text-returning hop before `.to_i64()`) |
| Same chain, but only ONE call in the function (no second chain) | not tested standalone, but `showcase_dims_min_repro.spl`'s single-branch, single-chain-per-branch struct version was also broken — see below |
| `parts[0].trim().to_i64()` / `parts[1].trim().to_i64()` after `raw.split("x")` (exact real-code shape) | **broken**, identical symptom |

**So: the trigger is a 2+-hop chained method call ending in `.to_i64()`
(any text-returning first hop), occurring twice in the same function.**
Both results are wrong, not just the second — ruling out a "later call
invalidates an earlier-cached-correct value" story; both are corrupted
essentially at their own computation. Struct-returning wrapper functions
with early-return branches (the real `showcase_resolution_dims()` shape)
are not required to reproduce it and were not the actual mechanism —
confirmed by this repro reproducing with zero structs, zero branches, zero
early returns.

Repro files (scratch, not committed):
`gap7_bisect_{a..j}.spl`, `gap7_minimal.spl`,
`showcase_dims_min_repro.spl`, `web_render_debug{,2,3}.spl` under
`/tmp/.../scratchpad/`.

### Not fixed — architectural, per instruction 5 (PROVED assessment, INFERRED mechanism)

This sits in MIR/codegen temp or stack-slot allocation for chained method
calls under cranelift — not a small, contained, single-call-site fix like
gap 6's `min`/`max`/`abs`. Root-causing it fully (why two 2-hop chains
collide, whether it's slot-reuse across statements failing to account for
extended liveness, or something in how `.trim()`'s intermediate `text` and
`.to_i64()`'s `i64?` result interact with the tagged-value boxing scheme)
would require reading MIR-lowering for method-chain expressions and likely
cranelift stack-slot assignment — out of scope for this pass per the
"don't force an architectural fix" instruction. Documented precisely
instead, with a reproducible minimal artifact for whoever picks this up.

Landed `test/01_unit/lib/language/chained_method_i64_conversion_spec.spl`
as a regression pin for the *intended* (interpreter-correct) behavior —
explicitly **not** a vacuity probe for the JIT bug. Verified directly (same
conclusion as gap 6, restated because it generalizes): the spec passes 4/4
identically whether run via plain `simple test` or `simple test` under
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` — `simple test` never
exercises the cranelift/JIT backend for spec files, full stop, regardless
of the env var. The only real evidence for this bug is the `simple run`
transcript above. Do not read the spec's presence or its passing as
coverage of gap 7.

### The prize: no timing captured, none was available to capture (instruction 4/5, PROVED)

Machine load at last capture: 37.62 (unchanged since the last pass; not
re-measured this pass, still flagged as partial contention). The
corruption happens in `showcase_resolution_dims()`, called before any HTML
parsing, rendering, or styling begins — `run_web_standards_showcase`
returns at line 341/342 (`reason=blank-or-uniform`, `return 3`) almost
immediately after start, well before the style loop
(`compute_styles_with_material` in
`simple_web_html_layout_renderer_core.spl`) is ever reached. There is no
partial per-node timing to extract from this run — the ~60 s wall time
observed is dominated by JIT compilation of the whole module graph (no
compile-artifact cache exists for this path, per the sibling lane's
finding), not by any styling work. Nothing to report here beyond "not
available," stated plainly rather than inferring a number.

### Heuristic-flip question (instruction 5, unchanged): still not evaluated

Blocked on gap 7, same as before — a correct-or-non-degenerate JIT result
still does not exist for this example.


## Ninth follow-up pass (2026-07-30) — gap 7 root-caused and FIXED; gap 8 found (module-level `val` via function call reads as 0 under JIT), still blocking the real repro

### Baseline check (deployed-binary swap mid-session, PROVED)

The deployed compiler at `bin/release/x86_64-unknown-linux-gnu/simple` was
swapped mid-session (57 MB / 0 `llvm::` strings -> 154 MB / 617 `llvm::`
strings, confirmed by direct `strings | grep -c` on the file). This
investigation's own binary was never that one: it is a locally
cargo-built `src/compiler_rust/target/release/simple` inside this
session's dedicated worktree (`git status` confirms only source files are
modified, no binary artifacts tracked), untouched by the swap or by the
ENOSPC cleanup (verified present, 57 MB, non-LLVM, correctly timestamped).
To rule out any doubt that the earlier gap-7 findings were an artifact of
this one build, re-ran the 6-line minimal repro directly against the new
deployed canonical (LLVM-having) binary before doing anything else — see
below: identical bug, identical 32-byte-stride signature. The bug is real,
present in the canonical toolchain, not specific to this worktree's build.

### Address hypothesis: CONFIRMED (instruction 2, PROVED)

```
SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 simple run <6-line repro>
```
on the freshly-confirmed deployed canonical binary, 3 independent runs:
```
pw=4134852167713 ph=4134852167745
pw=4716216256545 ph=4716216256577
pw=4206591543329 ph=4206591543361
```
always exactly 32 apart. A 3-occurrence version on the same binary:
```
pw=2340663725633 ph=2340663725665 pz=2340663725697
```
in hex: `0x220fa6e0e41`, `0x220fa6e0e61`, `0x220fa6e0e81` — each exactly
`0x20` (32) apart, landing at +32 and +64 from the first, precisely as
predicted: "a third occurrence landing 64 from the first would essentially
prove frame-slot addressing." Low, contiguous, fixed-stride hex deltas —
the signature of adjacent frame-slot (or spill-slot) addresses, not
decoded integers, confirming a missing load/deref rather than three
unrelated garbage reads.

### Root cause (instruction 3, PROVED by direct code reading — not the address arithmetic itself, but the trigger that produces it)

Traced `to_i64()` end to end:
- HIR (`hir/lower/expr/mod.rs`): `"trim" | "trim_start" | "trim_end" |
  "appended" | "prepended"` (and `"concat"|"slice"|"replace"`, see below)
  are typed `Some(TypeId::STRING)`, and `"to_i64"|"to_int"` are typed
  `Some(TypeId::I64)` — both correctly, confirmed directly by a temporary
  `eprintln!` showing `is_string=true` for the chained receiver
  (`"480".trim()` as the receiver of `.to_i64()`) — HIR is NOT where this
  breaks.
- MIR lowering (`mir/lower/lowering_expr_method.rs`): the generic
  (non-special-cased) method dispatch path lowers `to_i64` to
  `MirInst::MethodCallStatic { dest, receiver: receiver_reg, func_name:
  "text.to_i64", args }` via ordinary `self.lower_expr(receiver)` value
  lowering — also not where this breaks; nothing here distinguishes a
  chained vs. plain-Local receiver.
- **Codegen (`codegen/instr/body.rs`): found it.** A pre-pass builds a
  `types_map: HashMap<VReg, TypeId>` by walking every MIR instruction so
  later codegen knows each dest VReg's static type. This map has explicit
  arms for `MethodCallStatic` results of `to_text`/`to_string`/`str` and
  `to_u8`..`to_i32` (each typing the dest correctly) — but **no arm for
  `trim`/`trim_start`/`trim_end`/`appended`/`prepended`** (or `concat`/
  `slice`/`replace`), despite HIR typing all of these `STRING`. Without an
  entry, `.trim()`'s dest VReg falls through the catch-all `MirInst::
  MethodCallStatic { .. } => {}` and stays untyped in `types_map`.

This exactly matches the asymmetry (instruction 3's discriminator): a
plain `Local` receiver (`val a = "480"; a.to_i64()`) gets its type from
`MirInst::Load { dest, ty, .. } => types_map.insert(*dest, *ty)` — always
present for a declared local — so `to_i64()`'s receiver IS typed there,
correctly dispatching. A CHAINED receiver that is itself one of the
un-typed `MethodCallStatic` results has no such entry, so the outer call's
receiver type lookup misses, and (per an adjacent, already-fixed comment
in the same file documenting the identical `arr.len().to_i64()` case)
"falls through to name-based symbol resolution that mis-picks an unrelated
`Type.to_i64`" elsewhere in the link — explaining both the wrong VALUE
(reading whatever a mismatched-ABI callee left behind, consistent with the
address-shaped garbage) and why it costs nothing to `SIMPLE_JIT_STRICT`
(the wrong symbol still resolves and links; nothing is unresolved).

This is a **types_map coverage gap**, the same class of bug this very file
documents repeatedly having been fixed for `to_text`/`length`/`is_empty`/
`bytes`/etc. — never previously extended to the plain STRING-returning
transformation methods.

### Fix (instruction 4, contained — PROVED correct, not forced)

Added one new match arm to `codegen/instr/body.rs`'s `types_map` builder,
directly mirroring the existing `to_text`/`to_string`/`str` arm, for
`"trim" | "trim_start" | "trim_end" | "appended" | "prepended"` (both bare
and `Type.`-qualified `func_name` forms) -> `TypeId::STRING`.

**Deliberately excluded** `"concat"`/`"slice"`/`"replace"` even though
HIR's own table types them STRING too: `"slice"` collides with a real
ARRAY method of the same name (`"slice" | "filter" | "map" =>
Some(receiver.ty)` in the same HIR file's array-methods table), and this
`func_name`-only match has no receiver-type guard to disambiguate a
string call from an array call. Widening to those three risks a new
regression on chained array `.slice()`; correctly out of scope for a
contained fix, left as future work with the collision explicitly
documented in the code comment.

**Verified correct, PROVED, via `simple run` before/after transcripts:**

| Repro | Pre-fix (deployed canonical binary) | Post-fix (worktree binary) | Interpreter (oracle) |
|---|---|---|---|
| 6-line 2-occurrence | `pw=4134852167713 ph=4134852167745` (garbage, 32 apart) | `pw=480 ph=360` | `pw=480 ph=360` |
| 3-occurrence | `pw=2340663725633 ph=...665 pz=...697` (32/64 apart) | `pw=480 ph=360 pz=240` | `pw=480 ph=360 pz=240` |
| Exact `showcase_resolution_dims()` shape (struct, split+index+trim+to_i64, nil-guard) | `w=-796579551 h=-796579519` (garbage) | `w=480 h=360` | `w=480 h=360` |

No regression, PROVED: re-ran `trim()`/`trim_start()`/`trim_end()`/
`appended()`/`prepended()`/chained `.trim().to_string()` under JIT after
the fix — output identical to the interpreter in every case.
`.lower().to_i64()` (the earlier "generalizes beyond trim()" bisection
result) is **still** broken post-fix, as expected — `.lower()`/`.upper()`
aren't in HIR's STRING-typed table at all (a different, pre-existing,
separate gap; correctly left untouched by this contained fix).

Updated `test/01_unit/lib/language/chained_method_i64_conversion_spec.spl`
to record the fix and restate, per instruction 5, that it still cannot
detect the JIT bug either way — `simple test` does not route through
cranelift regardless of `SIMPLE_EXECUTION_MODE`. The `simple run`
transcripts above and in this doc are the only real evidence.

### Gap 8 (new, NOT fixed — architectural, out of scope for this pass): module-level `val` initialized via a function call reads as `0` under JIT

With the gap-7 fix landed, re-ran the assigned web-pipeline repro under
`SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1` expecting the "prize" (gap
7 was believed to be the last blocker for `RW`/`RH`). It still printed
`web_standards_showcase status=fail reason=blank-or-uniform pixels=0
nonzero=0 checksum=0` — **unchanged**. Instrumented the real file directly
(`print "DEBUG-RW RW={RW} RH={RH}"` at the top of
`run_web_standards_showcase`): still `RW=0 RH=0` even with the fix.

Bisected with fresh minimal repros (PROVED, not inferred):

```
struct Dims: w: i32 / h: i32
fn resolve_dims(raw: text) -> Dims: ...exact showcase_resolution_dims() body...
val DIMS: Dims = resolve_dims("480x360")
val RW: i32 = DIMS.w
fn main(): print "RW={RW}"
```
-> `RW=0` under JIT even post-fix, vs. the IDENTICAL logic called from
inside `main()` as a local `val` (previous table row) -> `RW=480`
correctly. The only difference is **module-level vs. local scope**.

Narrowed further:
- `val DIMS: Dims = make_dims()` where `make_dims()` just returns a
  hardcoded `Dims(w: 480, h: 360)` (**no** chained method call, **no**
  trim/to_i64 anywhere) -> **still `RW=0`**. Not gap 7's mechanism at all.
- `val RW: i32 = make_w()` where `make_w()` is `fn make_w() -> i32: 480`
  (trivial, scalar, one-liner) -> **still `RW=0`**.
- `val RW: i32 = 480` (literal, no function call) -> **`RW=480`, correct.**

**So gap 8, precisely stated: a module-level `val` initialized by calling
ANY function (regardless of what that function does) reads as `0` under
JIT; a module-level `val` initialized by a literal does not.** This is
unrelated to gap 7's chained-method/types_map mechanism — it reproduces
with zero method chaining, zero string parsing, a function that returns a
hardcoded literal. It is a different, and by symptom (clean `0`, not an
address-shaped garbage value) probably differently-mechanismed bug in
module/global initializer lowering under JIT — plausibly related to the
"module-global MIR lowering" area flagged as historically fragile in
project memory (array-typed globals were fixed there in an earlier pass;
this is a function-call-initialized scalar/struct global, seemingly not
covered by that fix). Not root-caused further and not fixed — this is a
different, likely larger area (global/module init sequencing) than the
"one contained fix" scope of this pass, per instruction 4's standing
guidance to stop and document rather than force it. This is now gap 8's
own open item, and it — not gap 7 — is what still blocks
`web_render_file_gui.spl` from producing a non-degenerate JIT result.
Minimal repro files (scratch, not committed):
`gap7_global_repro.spl`, `gap7_global_simple.spl`,
`gap7_global_scalar.spl`, `gap7_global_literal.spl` under
`/tmp/.../scratchpad/`.

### The prize: still not captured (instruction 5, PROVED)

Machine load at capture time: 5.71 (1-min avg) — materially lower than the
37.62 flagged in the prior two passes (host appears to have been
rebooted/reset during the session interruption: `uptime` now reports "up
55 min" versus many hours before), so this pass's timing conditions are
cleaner, for whatever future run gets far enough to use them. `simple run`
on the real web repro still exits in ~60 s with the same degenerate
`pixels=0 nonzero=0 checksum=0` status line as every prior pass — gap 8
(not gap 7, which is now fixed) is the reason. No partial per-node timing
exists to extract: the failure is still upstream of any HTML
parsing/rendering/styling, in resolving `RW`/`RH` before rendering starts.

### Heuristic-flip question (instruction 5, unchanged): still not evaluated

Blocked on gap 8, not gap 7 — a correct-or-non-degenerate JIT result for
this example still does not exist.


## Tenth follow-up pass (2026-07-30) — gap 8 root-caused, contained fix built and PROVED to segfault on `val`, reverted; gap 9 found on re-run (CastElse, reproducible across 2 runs)

### Bisection (instruction 1, PROVED) — the trigger is "any function call", not a type/arity/order/builtin-vs-user distinction

Extended the four repros from the ninth pass with targeted variants, each
changing exactly one variable:

| Repro | Result under JIT | Result under interpreter |
|---|---|---|
| `val RW: i32 = 480` (literal) | `480` (correct) | `480` |
| `val RW: i32 = make_w()` (trivial user fn, 0 args) | `0` | `480` |
| `val S: text = make_s()` (text return) | `""` (empty) | `"hello"` |
| `val B: bool = make_b()` (bool return) | `false` | `true` |
| `val A: [i64] = make_a()` (array return) | `A.len()==0` | `A.len()==3` |
| `val RW: i32 = make_w()`, `make_w` defined AFTER the global (order swapped) | `0` | `480` |
| `val RW: i32 = make_w(480)` (1-arg fn vs. 0-arg) | `0` | `480` |
| `val A: i64 = abs(-7)` (builtin, not user fn) | `0` | `7` |

**Every function-call initializer reads as its type's zero value
(`0`/`false`/`""`/empty array), regardless of return type, arg count,
declaration order, or builtin-vs-user-defined.** This rules out a
type-specific or arity-specific hole; the trigger is the mere presence of
a runtime call in a module-level initializer.

**Not the same machinery as the prior array-global fix.** Checked
`project_module_global_mir_lowering_2026-07-25` (memory): that fix
(`952d2ca34d7`) is in the **pure-Simple self-hosted compiler**
(`src/compiler/50.mir/_MirLowering*`, part of the from-Simple-sources
self-hosting bootstrap), an entirely different implementation from the
Rust seed compiler (`src/compiler_rust/compiler/src/mir/...`) that
`SIMPLE_EXECUTION_MODE=jit` actually runs. Different codebase, different
language the compiler itself is written in — not reachable from this
investigation, and its "array-typed OR cross-import" defect shape doesn't
match gap 8's "any function call, any type, same-module or not" shape
anyway.

### Root cause (PROVED by direct code reading)

`run_file_jit` (`driver/src/exec_core.rs`) compiles the MIR module and
calls `em.execute("main", &[])` directly — it never calls
`run_module_init`, the helper that the OTHER execution path
(`execute_and_gc`, used for SMF-loaded/AOT modules) calls before `main`
specifically to run a function named `__module_init` if present. The
JIT-side execution machinery is already fully wired for this: `codegen/
jit.rs`'s `call_i64_void` unconditionally calls `run_module_init_once()`
before invoking any OTHER named function, and would correctly find and run
`__module_init` if it existed in the compiled module's `func_ids` — the
gap is purely that nothing ever *produces* that function for `run_file_jit`
specifically.

Traced where it IS produced: `inject_freestanding_module_global_init`
(`pipeline/native_project/module_global_init.rs`) is an AST-rewrite pass
that turns each non-literal module-level initializer into a runtime
assignment inside a synthesized `__module_init_<prefix>_dynamic` (plus one
`__module_init_<prefix>_dynamic_optional_<index>` per Optional-typed
call-initialized global) function — but it is called from
`pipeline/native_project/compiler.rs` **only `if is_freestanding`**
(bare-metal/SimpleOS targets). `run_file_jit` always targets the host, so
this pass is simply never invoked for it, hosted or not. The whole-program
linker (`generate_init_caller` in `pipeline/native_project/linker.rs`)
resolves the resulting multi-function naming scheme by collecting every
`__module_init_*`-prefixed symbol across all linked objects, **sorting by
name**, deduping, and calling each with no args — that convention is
already shipping and tested, just never reused by the JIT path.

### Contained fix attempted, PROVED to work for `var`, PROVED to segfault for `val` — reverted (instruction 2/4)

Built the fix exactly as designed: widened `inject_freestanding_module_
global_init` from `pub(super)` to `pub` (and its module from private to
`pub`) so `run_file_jit` (a different crate) could call it; called it
unconditionally on the already-import-flattened AST right after
`load_module_with_imports` (freestanding was never the gate that mattered
for a host JIT call site); after `compile_module`, collected every MIR
function name starting with `__module_init_`, sorted (mirroring
`generate_init_caller`'s exact convention), deduped, and called each via
`em.execute(name, &[])` before `main`.

**Result, PROVED via a same-shape `var`-vs-`val` A/B pair (only the
declaration keyword differs):**

```
var B: bool = make_b()   ->  B=true   (correct, exit 0, no crash)
val B: bool = make_b()   ->  Segmentation fault (core dumped), exit 139
```

Root cause of the segfault (INFERRED from the code path, not traced
further): `inject_freestanding_module_global_init`'s non-Optional branch
leaves the original declaration's initializer expression untouched and
adds a **runtime assignment** to the same name in the synthesized init
function — freestanding global storage is apparently always
runtime-mutable regardless of `val`/`var`, so this is safe there, but
hosted (non-freestanding) HIR/MIR lowering evidently treats a `val`
module-level binding as a true immutable/read-only constant; writing to it
from a separate function is undefined behavior in that lowering and
crashes. This is a real semantic difference between freestanding and
hosted global representation in this compiler, not a bug in the reused
pass itself.

**This is worse than the pre-fix bug for `val`-declared globals** (a
silent wrong zero vs. a crash), and the real motivating case
(`showcase_resolution_dims()` assigned to `val SHOWCASE_DIMS`/`val RW`/
`val RH`) is exactly the `val` shape that crashes. Per instruction
4/the standing "an open bug with a six-line repro beats a rushed codegen
change" rule: **reverted all three files** (`exec_core.rs`,
`pipeline/native_project/mod.rs`, `pipeline/native_project/
module_global_init.rs`) back to HEAD, rebuilt, and confirmed the revert
restores the safe (silently-wrong-but-non-crashing) pre-fix baseline —
`val B: bool = make_b()` -> `B=false`, no crash, matching every prior
pass's behavior exactly. Nothing from this attempt is landed. Making this
safe for `val` requires either (a) making hosted module-level `val`
globals genuinely runtime-mutable (a change to immutability enforcement
in HIR/MIR global lowering, clearly out of "contained" scope) or (b) a
different synthesis strategy that doesn't require writing to a `val` at
all (not designed here) — flagged as the next concrete step for whoever
picks this up, not attempted.

### Gap 9 found on re-run (instruction 5: "do not report the web cell unblocked"; PROVED, reproducible)

Per instruction, re-ran the real repro after the revert (nothing fixed,
so no claim of unblocking is made). Two independent runs, both to
completion of the 280 s watchdog, produced the **same, different**
failure from every prior pass:

```
SIMPLE_EXECUTION_MODE=jit SIMPLE_JIT_STRICT=1 SHOWCASE_RESOLUTION=480x360 \
SIMPLE_WEB_RENDER_BUDGET_MS=120000 SIMPLE_TIMEOUT_SECONDS=280 \
simple run examples/06_io/ui/web_render_file_gui.spl
```
```
[INFO] JIT compilation failed, falling back to interpreter: HIR lowering error:
Unsupported feature: CastElse { expr: Identifier("top_left"), target_type: Simple("i32"), fallback_fn: Integer(0) }
...
error: example timed out after 280s: examples/06_io/ui/web_render_file_gui.spl
```

This is the same `CastElse` defect class fixed at 6 sites earlier in this
campaign (dedicated `<expr> as T else: fallback` postfix form, parser
precedence swallows an enclosing `if`'s `else`), now hit at a 7th,
previously-unseen site (`top_left`) — **not** gap 8's zero-value symptom;
compilation itself fails here, before any of gap 8's code would even run,
and `SIMPLE_JIT_STRICT` does not catch it because it's a HIR-lowering
"Unsupported feature" error, not the "unresolved external symbol" class
strict mode targets, so it silently falls back to the interpreter and then
times out (the interpreted lane's well-documented ~4s/node cost exceeding
the 280s budget for the module's overall script, not just the style loop).

**Flagged, not chased further:** the immediately-prior pass, on
byte-identical source and a functionally-equivalent binary (this pass's
revert restores the exact prior state), produced a clean ~60s
`pixels=0` compile-and-run with no CastElse error at all. Two consecutive
runs THIS pass both hit the CastElse error consistently. Whether the
difference between passes is genuine JIT non-determinism (a previously
catalogued class of issue in this codebase, see project memory
"flat_lane_nondeterminism_rootcause") or an artifact of this session's
rebuild/restart was not determined — noted as an open question rather
than asserted either way. Per instruction: **the web cell is NOT reported
unblocked.** No non-zero pixels have been produced by any run in this
entire chase.

### The standing question: independent defects, or one structural weakness? (instruction: "say so if you see a common shape")

**Not one weakness — two distinct, separately-evidenced shapes, plus one
non-pattern:**

1. **Shared MIR/codegen coverage gaps (gaps 6, 7).** Both are the SAME
   shape: a specific expression form (bare `min`/`max`/`abs` calls; a
   method call chained directly off certain STRING-returning methods)
   falls through an incomplete lookup table in codegen that ALL backends
   share (`mir/lower/lowering_expr_builtin.rs`'s `BuiltinCall` fallback;
   `codegen/instr/body.rs`'s `types_map` pre-pass). Both reproduced
   identically on the full canonical deployed binary (built via the
   complete native-build toolchain, not just `run_file_jit`), confirming
   these are backend-shared bugs, not pipeline-specific ones. Both fixed
   with a small, additive table entry.
2. **`run_file_jit` pipeline-completeness gaps (gap 4's W1006/lenient-mode
   fix from earlier in this campaign, and now gap 8).** Both are the SAME
   shape: `run_file_jit`'s simpler, single-file, no-whole-program-prescan
   pipeline is missing a STEP that the whole-program `native_project`
   pipeline already performs (there: `set_strict_mode(false)`/
   `set_lenient_types(true)`; here: running non-literal global
   initializers via a synthesized `__module_init`). Gap 8's fix direction
   is even more literally the same pattern as gap 4's: reuse the
   already-correct mechanism from the other pipeline, wire it into
   `run_file_jit`. The `val`-immutability segfault is a NEW wrinkle this
   pattern hadn't hit before (gap 4's fix was a pure flag flip with no
   representation mismatch).
3. **Gap 5 (`text.from_any`) is neither pattern** — a function that was
   never implemented anywhere in the codebase, an ordinary unimplemented-
   dead-code bug, not a systemic JIT weakness at all.

**The single most actionable finding from this shape analysis:** every
`run_file_jit`-only bug found in this campaign (gap 4, gap 8) has been
"the whole-program pipeline already has this, `run_file_jit` just never
calls it" — never a case where the correct mechanism didn't exist
anywhere. A systematic, one-time diff of `run_file_jit`'s pipeline steps
against `native_project::compiler.rs`'s pipeline steps would likely
surface any REMAINING gaps of this shape in one pass, rather than one
per bisection round. This is offered as the higher-value next step over
continuing to chase individual symptoms through the real web repro.

### The prize: still not captured

No non-zero-pixel run has occurred in this entire chase. Gap 8 is
root-caused and has a known-safe-for-`var`/known-unsafe-for-`val` partial
fix (not landed). Gap 9 (CastElse at `top_left`, possibly non-deterministic
in its appearance) is now the immediate next blocker, ahead of gap 8 in at
least 2 of the last 2 runs.

### Heuristic-flip question: still not evaluated

Unchanged — no correct-or-non-degenerate JIT result exists for this
example yet.
