# Interpreter: cross-module struct field-resolution collision with DIFFERENT struct names (Style vs CellStyle)

**Date:** 2026-07-04
**Severity:** high — blocks CARD 16 office GUI; broader instance of the
ledgered same-name struct collision
**Status:** WORKAROUND APPLIED — CARD 16 repro unblocked via source-level
rename (see "Workaround applied" section below); root-cause architectural
fix in the Rust seed interpreter's unqualified-call overload resolution
remains open and unlanded.

Prior status: PARTIAL — repro reconfirmed, root cause re-diagnosed (see
2026-07-04 iter section below); original field-name-set hypothesis
disproven, real mechanism is an unqualified zero-arg FUNCTION overload
collision. Fix is architecture-sized, not landed.

## Symptom

Once BOTH `src/app/office/sheets/cell.spl` (`CellStyle`: bold, italic, align,
format) and the browser engine's `Style` struct (bold, italic, …, display,
…) are loaded in one interpreter process, constructing/copying ANY `Style`
value fails:

```
error: semantic: class `CellStyle` has no field named `display`
```

~4s deterministic failure, unconditional on CSS content (reproduced with
every `display:` property removed). Not present when `Style` is exercised
without sheets code loaded (all browser-engine specs pass).

## Why it matters beyond the GUI

The previously ledgered bug required the SAME struct name in two modules.
Here the names DIFFER (`Style` vs `CellStyle`) — the interpreter's runtime
struct-literal/copy resolution appears to match by field-name-set overlap
(bold/italic shared), not declared type. Any two structs sharing a field
subset across modules are at risk when co-loaded.

## Repro

`office counter --gui` fallback path in `src/app/office/gui.spl`
(`office_gui_minimal_css()` knob) — bypasses render_frame, calls
`render_html_tree()` + `simple_web_engine2d_render_html_pixels()` directly
with ~1KB CSS; fails fast with the error above. Full analysis in
doc/08_tracking/bug/browser_engine_css_size_quadratic_pixel_render_2026-07-04.md
(Round 3 lane section).

## Related open item (same doc)

Separate unexplained gap: the identical render call is fast under
`bin/simple test <spec>` but hangs 60s+ under
`bin/simple run src/app/office/mod.spl` (full office module graph as entry) —
suspect symbol-count-scaled dispatch overhead or JIT-fallback difference.

## Next step

Find the interpreter's struct-literal/copy-update resolution (likely
matching by field-name set) in src/app/interpreter/ or
src/compiler/70.backend/backend/interpreter*.spl; resolution must key on the
declared/inferred TYPE, not field names. Cross-ref:
[[interp_dict_in_struct_copy_corruption_2026-07-03]],
[[interp_array_param_indexing_2026-07-03]].

## 2026-07-04 iter — root cause re-verified: disprove field-name-set theory, real cause is unqualified FUNCTION overload collision

### Repro confirmation

`timeout 120 bin/simple run src/app/office/mod.spl office counter --gui`
(note: `--` before `office` drops the args in `_get_office_cli_args()` in
`src/app/office/mod.spl` — pass `office counter --gui` directly, no `--`).
Fails deterministically, 3/3 runs, with:

```
error: semantic: class `CellStyle` has no field named `display`
```

The active binary is `bin/release/x86_64-unknown-linux-gnu/simple`
(built 2026-07-03 12:40, confirmed via `strings` to be the **Rust seed**
interpreter in `src/compiler_rust/compiler/src/interpreter*` — debug
path strings like `compiler/src/interpreter_eval.rs` are baked into the
binary). It predates today's #112 ObjectStore-model commits (which touch
`src/compiler_rust/compiler/src/interpreter/expr.rs` too), so it does not
yet reflect that in-flight migration.

### Field-name-set theory: disproven

Traced every `"class `X` has no field named `Y`"` emission site:
`src/compiler_rust/compiler/src/interpreter_call/core/class_instantiation.rs`
(construction, ~line 300), `src/compiler_rust/compiler/src/interpreter/expr.rs`
(~line 120, field access) + `.../interpreter/expr/calls.rs` (~line 377,
property access), and `src/compiler_rust/compiler/src/pipeline/lowering.rs`
(static "struct" wording, different message — ruled out). All three
runtime sites gate the field-name-set fallback
(`pick_fitting_class_def()` / `CLASS_OVERLOADS.with(...).get(class_name)`
in `class_instantiation.rs:28-51`) **by the exact class name being
constructed/accessed** — both `classes: HashMap<String, Arc<ClassDef>>`
and `CLASS_OVERLOADS: HashMap<String, Vec<Arc<ClassDef>>>` are keyed by
the literal's own type name (`s.name.clone()` / `c.name.clone()` at
registration in `interpreter_eval.rs:300-370`). A `Style(...)` call can
never structurally resolve to a `CellStyle` def through this path — the
`CellStyle` bucket is never consulted for a `Style` construction. This
rules out cross-*struct* field-set matching as the mechanism, contrary to
the "Why it matters" hypothesis above.

### Real root cause: unqualified zero-arg FUNCTION name collision

Three separate zero-parameter functions share the bare name
`default_style`, each with a **different return type**, all reachable
from one `office/mod.spl` load:

- `src/app/office/sheets/cell.spl:37` — `fn default_style() -> CellStyle:`
- `src/lib/nogc_sync_mut/tui/style.spl:137` — `fn default_style() -> Style:` (tui Style)
- `src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl:1593` — `fn default_style() -> Style:` (browser Style, has `display`)

The browser layout renderer calls its own `default_style()` unqualified at
line 5225/5229 (`var styles: [Style] = [default_style(); node_count]` /
`else: default_style()`). All 3 candidates land in the same
`FUNCTION_OVERLOADS: HashMap<String, Vec<Arc<FunctionDef>>>` bucket
(populated in the function-registration loop in
`src/compiler_rust/compiler/src/interpreter_eval.rs`, `Node::Function`
arm) because the registry has **no module qualification at all** — flat
bare-name key, the same gap as the struct/class registry but for
functions, and with no cross-module disambiguation cache analogous to
`MODULE_CLASSES_CACHE` / `MODULE_FUNCTIONS_CACHE`
(`src/compiler_rust/compiler/src/module_cache.rs`) consulted at this
call site — those caches only serve explicit qualified `module.symbol()`
access, not unqualified bare calls.

`select_overload()` (`src/compiler_rust/compiler/src/interpreter_call/mod.rs:116-127`)
scores each candidate via `overload_score()`, which only compares
parameter **count** and **argument value types**
(`func.params.len() != values.len()` short-circuit, then per-param
`value_matches_type`). With 0 params and 0 args, all three candidates tie
at score 0 with no argument shape to break the tie on. The tie-break rule
(`Some((best_score, _)) if *best_score >= score => {}`, i.e. keep the
existing best on a tie) means whichever candidate was pushed into
`FUNCTION_OVERLOADS["default_style"]` **first** wins — i.e. whichever
module's `default_style` registered during the **earliest** module load.

`src/app/office/mod.spl` imports `app.office.sheets.sheets_app.{SheetsApp}`
(line 8, pulls in `cell.spl`) **before** `app.office.gui.{office_gui_frame,
...}` (line 14, pulls in the browser engine transitively via
`render_html_tree` / `simple_web_engine2d_render_html_pixels`). So
`cell.spl`'s `default_style() -> CellStyle` registers first and wins the
tie for every unqualified `default_style()` call in the whole process —
including calls made from *inside* the browser engine's own rendering
code, which then treats the returned `CellStyle` object as a `Style` and
fails accessing/copying its `display` field. This reproduces the exact
observed error and explains why it only appears once BOTH modules are
loaded together (matches the original symptom description), but the
actual mechanism is function-overload resolution, not struct-literal
field-name matching.

### Why this isn't a minimal/lane-sized fix

A correct fix needs unqualified-call resolution to prefer (or restrict
to) the candidate defined in the **calling function's own module**. That
requires:

1. Module identity attached to each registered function. `FunctionDef`
   (`src/compiler_rust/parser/src/ast/nodes/definitions.rs`) has no
   `module_path` / `source_module` field — only a `Span` (line/col).
   Adding one means either extending the parser AST (touches parsing,
   every `FunctionDef` construction site, and the self-hosted `.smf`
   serialization format) or maintaining a parallel side-table in the
   interpreter's own registries (`FUNCTION_OVERLOADS`, `functions`) — a
   new field/companion map threaded through every registration and
   lookup site in `interpreter_eval.rs`, `interpreter_call/mod.rs`, and
   `module_cache.rs`.
2. Threading "which module is the currently-executing code's home
   module" into `select_overload`'s call site
   (`interpreter_call/mod.rs:315-334`, Priority 4) — there is currently
   no "current module" context plumbed into `evaluate_expr` / `eval_call`
   at all for this purpose.

Both changes ripple across the flat global function/class registries
underlying the *entire* interpreter's overload resolution (used for
every same-named function across the whole stdlib+app tree), not just
this one symptom. That is architecture-sized, not lane-sized, and risks
regressing unrelated overload resolution if rushed. Recommend a
follow-up task scoped specifically to "module-qualified unqualified-call
resolution", touching `interpreter_eval.rs` (registration),
`interpreter_call/mod.rs` (dispatch + `select_overload`), and
`module_cache.rs` (module-context plumbing), verified against a targeted
regression spec with 2+ same-name zero-arg functions of differing return
type across two modules.

### Smallest safe interim mitigation (not applied — flagging, not deciding)

Rename one of the two colliding `default_style()` functions (e.g. the
browser engine's to `default_computed_style()`) to remove the immediate
collision for CARD 16's repro. This is a workaround, not a root-cause fix
— any other pair of same-named, same-arity functions across modules with
differing return types remains latently broken. Left undone here per
"don't paper over the root cause without recording it" — next lane should
decide whether an interim rename is acceptable while the architectural
fix is scheduled.

### Status of this iteration: PARTIAL

Root cause identified, prior theory disproven with file:line evidence, no
code changed. The fix site is the Rust seed interpreter
(`src/compiler_rust/compiler/src/interpreter_call/mod.rs` +
`interpreter_eval.rs`); it would require a `cargo` rebuild of
`src/compiler_rust` to take effect, since the deployed
`bin/release/x86_64-unknown-linux-gnu/simple` predates any interpreter
change made here. No bootstrap/seed rebuild performed in this lane, per
lane scope ("don't rebuild — report what needs rebuilding and why"). A
pure-`.spl`-level fix is not available: the colliding resolution logic
lives entirely in the Rust seed interpreter, not in any self-hosted
`.spl` interpreter path (`src/app/interpreter/`,
`src/compiler/70.backend/backend/interpreter*.spl` do not implement
unqualified-call overload resolution for the code path this repro
exercises).

## 2026-07-04 — Workaround applied (pure-`.spl` rename, CARD 16 unblock)

Per the "smallest safe interim mitigation" noted above, renamed two of the
three tied `default_style()` zero-arg functions so the global
`FUNCTION_OVERLOADS["default_style"]` bucket no longer has a same-name tie.
`src/app/office/sheets/cell.spl:37`'s `default_style() -> CellStyle` is left
untouched (office code depends on the bare name; after the renames below it
is the sole `default_style` in the process, so no collision remains).

**Renames:**

- Browser engine (`src/lib/gc_async_mut/gpu/browser_engine/simple_web_html_layout_renderer.spl`):
  `default_style` → `renderer_default_style`. 3 call sites in this file
  (definition at line 1593, plus 2 internal call sites, formerly ~5225/5229).
  Swept the whole file and `src/`/`test/` tree for other importers — none
  found; nothing else references this file's `default_style` by name.
- TUI style (`src/lib/nogc_sync_mut/tui/style.spl`): `default_style` →
  `tui_default_style`. Definition (line 137) + 1 internal call site
  (line 301), plus every re-export/import chain that names it explicitly:
  `src/lib/nogc_sync_mut/tui/__init__.spl`,
  `src/lib/nogc_sync_mut/tui/widget.spl`,
  `src/lib/nogc_sync_mut/tui/widgets/{input,box_widget,text,list}.spl`,
  `src/lib/gc_async_mut/tui/__init__.spl`,
  `src/lib/gc_async_mut/tui/style.spl` (re-export),
  `src/lib/nogc_async_mut/tui/__init__.spl`,
  `src/lib/nogc_async_mut/tui/style.spl` (re-export), and the TUI widgets
  facade specs under
  `test/01_unit/lib/{gc_async_mut,nogc_async_mut}/tui/widgets/` (including
  the untracked `.spipe_matchers_*` mirrors) and the older duplicate copies
  under `test/unit/lib/{gc_async_mut,nogc_async_mut}/tui/widgets/`.
  18 files total touched across both renames.

**Classification sweep (ambiguous cases, left alone):**

- `be_default_style()` in `src/lib/gc_async_mut/gpu/browser_engine/css.spl`
  is a distinct, already-uniquely-named function — not part of the
  collision, untouched.
- `TextStyle.default_style(font: FontHandle)` (static method,
  `src/lib/nogc_sync_mut/engine/render/text.spl:32` and the
  `nogc_async_mut` mirror) is a qualified static-method call with 1 param —
  different resolution path and arity, not part of the 0-arg unqualified
  collision, untouched.
- `default_style_for(tag: text)` (`src/lib/common/render_scene/office_style_resolver.spl`)
  and `_default_style()` (`src/app/ui.tui_web/screen_to_html.spl`) are
  already distinctly named — untouched.
- **Pre-existing unrelated bug found, not fixed here:**
  `src/os/compositor/browser_backend.spl:20` and
  `src/os/apps/browser_sample/browser_sample.spl:24` both import a bare
  `default_style` from `std.gc_async_mut.gpu.browser_engine.css` — but
  `css.spl` only exports `be_default_style`, never a bare `default_style`.
  This import appears stale/broken independent of this bug and of the
  renames above (it doesn't reference either renamed symbol); flagging for
  a separate fix, out of scope for CARD 16.

**Verification:**

- Repro `timeout 120 bin/simple run src/app/office/mod.spl office counter --gui`
  (no `--` before `office`) no longer hits the CellStyle/display collision;
  it now runs to completion: `office-gui: counter frame 96x64, 2523
  non-background pixels`.
- Specs green after the rename:
  `test/01_unit/lib/gc_async_mut/gpu/browser_engine/simple_web_renderer_spec.spl`
  (79/79), `test/01_unit/lib/gc_async_mut/tui/widgets/tui_widgets_facade_spec.spl`
  (1/1), `test/01_unit/lib/nogc_async_mut/tui/widgets/tui_widgets_facade_spec.spl`
  (1/1), `test/01_unit/app/office/sheets/formula_financial_spec.spl` (15/15),
  `test/01_unit/app/office/md_wysiwyg_render_spec.spl` (7/7).

**Root cause still open:** this is a workaround, not the fix. Any other
pair of same-name, same-arity, differing-return-type functions across
modules remains latently broken by the same
`FUNCTION_OVERLOADS`/`select_overload()` tie-break-keeps-first-registered
mechanism described above. The architectural fix (module-qualified
unqualified-call resolution in the Rust seed interpreter,
`interpreter_eval.rs` + `interpreter_call/mod.rs` + `module_cache.rs`)
remains scheduled as a separate, architecture-sized follow-up.

**WC-sweep note:** all 18 files in this rename were reverted once by a
concurrent working-copy sweep mid-lane and had to be reapplied; verify the
rename (`grep -rn 'default_style' <files>`) is still present before
building on this workaround in a future session.

## 2026-07-04 — Root-cause CORRECTED + working fix built in isolated worktree (NOT landed on main)

An isolated-worktree agent built the seed (`cargo build -p simple-driver`),
reproduced the bug with a minimal 2-module repro, and implemented a verified
fix. Status: **fix works on the repro + overload-relevant specs; regression
coverage PARTIAL; deliberately NOT landed on shared main** pending a dedicated
hardening + full-regression pass (see caveats). Fix is preserved on git branch
`worktree-agent-aa278f276edfdc49d` (commit `b8672cfbce2`, 8 seed files,
+177/-11) and as `scratchpad/card16_fix_final.diff`.

### Correction to this doc's earlier analysis

The earlier "Next step" pointed at the interpreter's runtime `use`-loader
(`interpreter_module/module_loader.rs` → `module_evaluator.rs`). That path is
**NOT** what the actual `bin/simple run`/`-c` CLI exercises. The CLI uses
`pipeline::module_loader::load_module_with_imports`, which **flattens all
imported modules' AST items into one combined list** (`strip_flattened_import_
nodes`) BEFORE the interpreter's single registration pass runs — erasing
per-function module identity before `interpreter_eval.rs` ever sees it. A naive
"tag the function's module at registration" fix silently does nothing on this
path (every function's owner reads as `"<entry>"`). This is why the collision
persists into the CLI/GUI path specifically.

### The fix (scoped to the tie case only)

- `interpreter_state.rs`: 3 new thread-locals — `FUNCTION_MODULE_OWNER` (Arc
  ptr-identity → owning module), `FLATTEN_FUNCTION_MODULE_HINT` (bridges module
  identity across the flatten step, keyed by `(name, span.line, span.column)` —
  the only thing surviving the flatten value-clone), `CURRENT_EXEC_MODULE`.
- `pipeline/module_loader.rs`: `strip_flattened_import_nodes` records the hint.
- `interpreter_eval.rs`: registration reads the hint to set the owner.
- `interpreter_call/core/function_exec.rs`: save/restore `CURRENT_EXEC_MODULE`
  around each function body (the single choke point).
- `interpreter_call/mod.rs`: `select_overload` — ON AN EXACT SCORE TIE ONLY,
  prefer the candidate whose owner == `CURRENT_EXEC_MODULE`; replace the
  incumbent only if incumbent is not a same-module match and the new one is.
  Every non-tie case is byte-for-byte identical to the old keep-first rule
  (this is the key safety property: it cannot change a currently-correct
  resolution, only arbitrary ties).

### Verification (why it's promising but NOT yet landable)

- Repro: pre-fix mis-dispatches `call_from_b()`'s `thing()` to module A
  (`AResult has no field 'label'`); post-fix resolves correctly.
- Specs on the fixed binary: `static_method_overload_dispatch_spec` 4/4,
  `office_gui_pixel_spec` 5/5, `formula_financial_spec` 15/15; `counter --gui`
  completes.
- **Gaps:** `cargo test -p simple-compiler --lib` is PRE-broken (3× E0063
  `missing field is_value_type` in test-cfg code the fix did NOT touch) — blocks
  the full Rust unit regression. `simple_web_renderer_spec` (79 ex) hit the test
  daemon's 2-min timeout — inconclusive, not a confirmed regression.
- **KNOWN EDGE-CASE HOLE (must harden before landing):** the flatten hint is
  keyed by `(name, line, col)` because `Span` has no source-file field. Two
  different files with a same-named function at the same line/col would COLLIDE
  → wrong module hint. Landing requires either adding a file/module id to `Span`
  (or the hint key), or another disambiguator. Do not land until this is closed.

### Orthogonal bug discovered (separate, file if lifting this)

The DEFAULT JIT/native path (not the interpreter dispatch fixed here)
mis-handles the same same-name/different-struct pattern with a memory
corruption (`<invalid-heap:...>`), reproduced IDENTICALLY on pre- and post-fix
binaries. Separate JIT/native-codegen issue, out of scope for the interpreter
overload fix.

### Recommended landing path

Dedicated seed task: (1) harden the hint keying (close the line/col-collision
hole), (2) fix or route around the pre-broken `cargo test` E0063s so full Rust
regression runs, (3) full `.spl` spec sweep on the rebuilt binary, (4) land the
seed diff + a targeted 2-module-same-name regression spec, (5) rebuild + deploy
`bin/release` (the hazardous swap — coordinate with parallel sessions). Until
then the source-level `default_style` rename workaround above keeps CARD 16's
GUI repro unblocked.

## 2026-07-04 — Hardening pass DONE; source LANDED (inert until rebuild); only deploy remains

Steps (1)(2)(3)(4-source) above are now DONE (isolated worktree branch
`worktree-agent-aa278f276edfdc49d`, commits `b8672cfbce2` + `67259836cc7`), and
the seed source is LANDED on main (inert until the next seed rebuild). Only the
rebuild + `bin/release` DEPLOY (step 5, the hazardous shared-binary swap) and a
release-build re-confirm of the heavy renderer spec remain — deferred, same
hazard class as CARD 6.

- **(1) Edge case CLOSED — collision-proof by construction.** Approaches (a)/(b)
  were impossible (flatten holds `Node::Function` BY VALUE — no Arc — and mints a
  fresh `Arc::new(f.clone())` at registration; registration doesn't know its
  module). Solution (c'): the flattener pushes a SYNTHETIC ATTRIBUTE
  (`FLATTEN_MODULE_OWNER_ATTR_PREFIX` + module_path) onto each flattened
  `FunctionDef`; the attribute travels WITH the node value and survives the
  clone, so registration reads the exact per-node owner. The unsound
  `(name,line,col)` side-table is DELETED. Proof the old key was unsound: a trace
  showed two byte-identical-layout files yield IDENTICAL spans for `fn thing()`
  (`line=3 col=1 start=24 end=65`). Honest caveat: a parallel `register_
  definitions` path also assigns owners by Arc-identity and currently MASKS the
  collision in minimal repros, so a live minimal pre-hardening mis-resolution
  couldn't be exhibited — the real office/browser `default_style` collision is
  the live evidence; the attribute fix removes the unsound key as defense-in-depth
  regardless.
- **(2) Rust regression GREEN — 0 new failures.** E0063 fixed via
  `is_value_type: false` in the 3 test-cfg ClassDefs (context_pack.rs,
  interpreter_module/module_loader.rs, mcp.rs). `cargo test -p simple-compiler
  --lib` = 2860 pass / 234 fail; the 234 fail-set is BYTE-IDENTICAL to baseline
  (b8672 + only the E0063 fixes) → this fix introduces ZERO regressions. The 234
  are pre-existing env/WIP-seed failures (codegen/mir/pipeline/native/std-io,
  e.g. missing `examples/ui/web_wm.spl`).
- **(3) Specs.** Overload/dispatch/module-resolver green (static_method_overload
  4/4, module_resolver_1/2/3, cross_module_trait_default_dispatch,
  trait_static_dispatch); browser_engine green (html_renderer, selector_matcher,
  paint_image_scene, engine2d_backend_resolver). `simple_web_renderer_spec` (79
  ex) hits the test-runner daemon timeout on the DEBUG/unoptimized binary
  (never completed pre-change either — debug perf, not a regression); re-confirm
  on a release build during the deploy pass.
- **Orthogonal bug (file when deploying):** the DEFAULT JIT/native path
  memory-corrupts (`<invalid-heap:...>`) on the same same-name/different-struct
  pattern, identical pre/post-fix — separate JIT/native-codegen issue.

**BOTH residuals now converge on ONE deferred action.** CARD 16's fix and CARD 6's
raw-mode extern are both SEED changes that only take effect after a seed
bootstrap rebuild + `bin/release` deploy. That single, hazardous-in-a-shared-WC
step (it replaces the binary every parallel session uses) is the only thing left
for BOTH — do them together in a coordinated deploy window, with the release-build
renderer re-confirm. The CARD 16 source is already in-tree and regression-clean;
the CARD 6 externs are already declared (interactive.spl:333).
