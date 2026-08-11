# Design — Self-Hosted Frontend Parser Gaps + Lazy Module-Closure Startup

**Date:** 2026-07-07
**Status:** DESIGN — agent-executable
**Plan pair:** `doc/03_plan/compiler/self_hosted_frontend/full_cli_redeploy_and_browser_startup_plan.md`
**Related design:** `doc/05_design/compiler/parsing/parser_architecture_unified_2026-02-04.md`

Covers two compiler-frontend concerns that share the interpreted-parse root cause
(see the plan §0):
1. Three grammar-surface gaps the self-hosted `parse_full_frontend` rejects but the
   interpreter accepts (Task #21 correctness blocker).
2. The `use lazy` module-closure mechanism used to shrink the interpreted `--open`
   startup closure (Task #29 short-term fix).

All anchors below were verified against the working tree on 2026-07-07.

---

## 1. Context: why the two parsers diverge

The interpreter parser and the self-hosted `parse_full_frontend` are separate code
paths. Compiler sources were written/tested against the richer interpreter parser, so
constructs the interpreter accepts can still fail the self-hosted parse
(`doc/08_tracking/bug/bootstrap_stage4_graph_load_timeout_2026-07-05.md` §4). The design
principle for every gap: **make both accept the same grammar**, not make the
self-hosted parser reject less loudly.

Hot self-hosted parse path (for locating edits):
`src/compiler/80.driver/driver.spl:355` (parse loop) →
`src/compiler/10.frontend/frontend.spl:34 parse_full_frontend` →
`src/compiler/10.frontend/_FlatAstBridge/module_assembly.spl:455 parse_and_build_module`.

---

## 2. Parser feature designs

### 2.1 Array-repeat **expression** `[value; count]`  (gap A1)

**Symptom (verified):** `check` on `[0u8; 12]` →
`expected ], got ; ';'` then `unexpected token in expression: ] ']'`.

**Root cause:** the array-literal **expression** parser
(`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl:503-513`) handles only
the comma-separated form and the `for`-comprehension form (`:467-502`). After parsing
`first_elem` it expects either `,` (kind 160) or `]` (kind 145); a `;` derails it. Note
the sized-array **type** `[T; N]` is already handled separately at
`src/compiler/10.frontend/core/parser.spl:523-524` (accept-and-drop the size) — the
gap is only the **value** form.

**Design:** after `first_elem` is parsed (before the `:503` regular-array branch), add a
`;`-lookahead branch mirroring the type-side handling at `parser.spl:523`:
- On `;`: `parser_advance()`, parse a `count` expression, `parser_expect(145)` (`]`).
- Emit the repeat. Two lowering options — **pick per the AST's existing capability:**
  - **(a) Preferred if a repeat node/marker exists:** emit a dedicated repeat array-lit
    so the count stays symbolic (needed for `[desktop_batch; windows.len()+2]` where the
    count is runtime, not a literal).
  - **(b) Fallback if only `expr_array_lit(elements, _)` exists and count is a literal:**
    expand at parse to N copies. Rejected for A1 because
    `window_scene_draw_ir.spl:148,232` use **non-literal** counts (`z_span`,
    `windows.len()+2`) — parse-time expansion is impossible there. Therefore **option
    (a) is required**; if no repeat node exists in the AST, add one (a minimal
    `expr_array_repeat(value_expr, count_expr, span)`), with HIR lowering to the same
    fill the interpreter already uses for this construct.

**Files:** `_ParserPrimary/primary_expr.spl` (parser branch); AST + HIR lowering module
for the repeat node if (a) requires one; a `parser_*_spec.spl` regression.

**Acceptance:** `check` clean on `backend_metal.spl:257,265` and
`window_scene_draw_ir.spl:148,232`; interpreter (`run`) and self-hosted (`check`) both
accept a literal-count and a runtime-count repeat.

### 2.2 `mut` parameters  (gap A2)

**Symptom (verified):** `check` on `fn rewrite_block(..., mut stats: PatternIdiomStats)`
(`src/compiler/mir_opt/mir_opt/pattern_dispatch.spl:193`) → `expected ), got Ident`.
74 repo files use `mut` params.

**Root cause:** `struct Param` (`src/compiler/10.frontend/parser_types.spl:139`) has
fields `name / has_type_ / type_ / default` — **no `is_mut`**, and no parser code
consumes a leading `mut` in param position.

**Design:**
1. Add `is_mut: bool` to `struct Param` (after `name`, keep the desugar-comment field
   ordering intact so the flat-AST bridge offsets stay consistent — verify against
   `_FlatAstBridge` field encoding before reordering).
2. In the parameter parser, before reading the param name, snapshot-and-check for a
   leading `mut` keyword token; if present, consume it and set `is_mut = true`. Use the
   same keyword-token handling the parser already uses elsewhere (grep the param-parse
   function that builds `Param(...)`; it is the single construction site to update).
3. **Semantics:** `mut` on a parameter marks the binding mutable inside the body. At
   stage4 the self-hosted path may treat it as a no-op annotation (parse-and-accept)
   IF the interpreter already permits reassignment of the param name — verify: the
   interpreter parses `mut` params fine (bug record §4), so accept-and-record is
   sufficient for parse parity. Do **not** add borrow/alias checking here (out of scope).

**Files:** `parser_types.spl` (struct), the param-parse function under
`src/compiler/10.frontend/core/` (grep for the `Param(` construction), flat-AST bridge if
the new field needs encoding, a `parser_*_spec.spl` asserting `is_mut` round-trips.

**Acceptance:** `check` clean on `pattern_dispatch.spl`; spec asserts a `mut`-param fn
parses and the flag is set.

### 2.3 Irrefutable destructuring `val PATTERN = EXPR`  (gap A3)

**Symptom (verified):** `val Some(dollar_idx) = dollar_pos`
(`src/std/nogc_sync_mut/env/variables.spl:358`). The interpreter **parses** it but its
HIR let-lowering rejects (`complex patterns not yet supported in let bindings`); the
self-hosted `parse_full_frontend` rejects at parse (`expected =, got (`). 226 repo files
use `val Some(...) =`.

**Root cause:** two layers — (i) self-hosted parser only accepts a bare ident LHS in a
`val`/`var` let; (ii) HIR let-lowering only handles ident LHS. This is the **largest**
change of the three (touches lowering, not just parse).

**Design:**
1. **Parse:** in the `val`/`var` statement parser, when the LHS is not a bare ident,
   parse it as a **pattern** (reuse the existing pattern parser used by `match`/`case`
   arms — do not fork a second pattern grammar). Produce a let node carrying a pattern
   LHS instead of an ident.
2. **HIR lowering:** lower `val PAT = EXPR` to: bind `EXPR` to a fresh temp, then emit
   the pattern's binding extractions against that temp (positional/field reads), exactly
   as the interpreter's `match` single-arm lowering does. For an **irrefutable** pattern
   (`Some(x)`, tuple, struct) this is a straight extraction; a **refutable** pattern in a
   `val` is a semantic error (mirror the interpreter's behavior — do not silently drop).
3. **Scope guard:** only enable the extraction path for the irrefutable-single-constructor
   and tuple/struct cases the 226 files actually use; do not attempt exhaustive
   refutable-let semantics.

**Files:** the `val`/`var` statement parser under `src/compiler/10.frontend/core/`; the
HIR let-lowering module (grep `complex patterns not yet supported in let bindings` for
the exact site); a `parser_*_spec.spl` + a lowering spec.

**Acceptance:** `check` clean on `variables.spl`; **parity spec**: `run` and `check`
both accept `val Some(x) = e` and `val (a, b) = pair`. Land last (highest regression
risk on nested patterns), behind its own spec.

---

## 3. Lazy module-closure design (Task #29 startup)

### 3.1 Mechanism (verified)

Simple has a first-class `use lazy` import modifier:
- **Parse:** `src/compiler/10.frontend/core/parser_decls_use.spl:163 decl_set_lazy(use_result)`
  sets a lazy flag on the use decl.
- **Interpret:** `src/compiler/10.frontend/core/interpreter/eval_decls.spl:81-105` — for a
  `DECL_USE` with `decl_get_is_lazy == 1`, calls `register_deferred_module(...)` and
  **returns without loading the module**. The module (and its transitive closure) loads
  only on first symbol use.
- **Smoke test (2026-07-07):** a `use lazy` import whose symbol is never referenced does
  not load the module (prints the no-use path); referencing the symbol resolves it
  correctly (`heavy_thing()` → 42). Confirms defer + on-use resolution both work in
  `SIMPLE_EXECUTION_MODE=interpret`.

### 3.2 Why it fixes the `--open` regression

The `--open` lane is interpreted, so its wall time scales with the **transitively parsed
module closure** (bug record: ~0.8 ms/char × reachable modules). `app.spl` gained
`use os.compositor.host_compositor_entry.{...}` (+ `window_protocol.geometry`) whose
closure is large (see `host_compositor_entry.spl` header: ~15 compositor/WM/web-render
imports). But those symbols are used **only** inside `run_shared_wm_browser` /
`browser_shared_wm_config` (`app.spl:310-330`), reached only when `shared_wm == true`
(`app.spl:333`). The default `--open` (`main.spl:88`, `shared_wm=false`) never touches
them. Marking those imports `use lazy` defers the entire compositor closure off the
`--open` parse, while `--shared-wm` still resolves it on first `init_host_wm` call.

### 3.3 Design decision: lazy import vs structural split

- **Primary — `use lazy` (plan D1):** minimal, no code movement, no new module. Change
  `app.spl:17-18` to `use lazy`. `std.diag.{dbg_stage}` stays **eager** (hot-path use).
- **Fallback — structural (plan D1-alt):** only if a symbol forces eager resolution
  (e.g. a top-level `val`/type that the interpreter resolves at module init). Then move
  `run_shared_wm_browser` + `browser_shared_wm_config` into the existing
  `os.compositor.host_compositor_entry` module behind one exported entrypoint, and
  dispatch from `main.spl`'s `shared_wm` branch so `app.spl` drops the import entirely.
  **Constraint:** merge into the existing compositor module — **no `X2`/`_v2`/numbered
  split** (MEMORY.md `feedback_no_numbered_module_splits`).

### 3.4 Risk / verification

- **Type-annotation references:** `main.spl:203 shared_wm_backend_kind_browser() ->
  HostBackendKind` names the enum only as a return type. Interpret-mode erases type
  annotations at runtime, so a `use lazy` on `HostBackendKind` in `main.spl` is expected
  safe — but VERIFY with the D2 protocol (a `--open` run must not load the compositor
  closure; check via `dbg_stage` phase timing and absence of compositor load).
- **On-use resolution must still work:** a `--shared-wm --open` run must reach
  `shared_wm_init_done` (`app.spl:328`) — proves the deferred module resolves on first
  `init_host_wm` use.
- **Measurement (plan D2):** gate `SIMPLE_DIAG=stage`; compare `launch_start`→`parse_start`
  (module-load closure) before/after. Expect the closure phase to collapse post-lazy.

### 3.5 Removability

`use lazy` here is a latency mitigation on the **interpreted** path. Once the frontend
runs compiled (plan Track B) and is redeployed (Track C), the per-char multiplier is
gone and closure size stops being latency-critical; the `use lazy` markers can revert to
plain `use` in the same change that measures flat compiled-startup latency.
