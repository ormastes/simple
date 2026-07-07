# Interpreter Array Mutating-Method Fast-Path Plan - 2026-07-08

## Purpose

Fix the O(N²) list-building landmine documented in
`doc/08_tracking/bug/interp_array_mutating_methods_clone_whole_array_2026-07-08.md`: the Rust
seed interpreter's array mutating methods (`push`/`append`/`pop`/`insert`/`remove`/`extend`/
`clear`) clone the entire backing array on every call — 84× slower than the equivalent
`a[i]=`-into-preallocated-local pattern at N=16000, and diverging (clean O(N²) vs. O(N)). Two
tracks: a durable interpreter (seed) fix, and immediate unblocked per-site refactors of the
worst-ranked call sites while the seed fix waits for a full-bootstrap window.

## Source

- Sweep: `/private/tmp/claude-501/-Users-ormastes-simple/7597a415-f0b0-4c3f-822d-107292b34bec/scratchpad/bare_array_param_sweep.md`
- Bug record: `doc/08_tracking/bug/interp_array_mutating_methods_clone_whole_array_2026-07-08.md`

## Scope

**In scope:** the interpreter's handling of the 7 array mutating methods for the common case of a
locally-bound, uniquely-owned (`Arc::strong_count == 1`) array identifier receiver; per-site
replacement of `push`-in-loop with `[default; n]` + index-assign at ranked hot-path victims.

**Out of scope (do not fix here):** the nested-struct-field `push` non-persist bug (different
failure mode, different fix — reassign-whole-parent-struct workaround already in place) and the
`(expr) as u8` push-marshals-empty bug (different code path — extern marshal element tagging).
Both are explicitly disambiguated, not folded into this plan, in the bug record's "adjacent bugs"
section — do not conflate fixes across them.

## TRACK A — durable fix: extend the `case1_unique` fast path to mutating methods (seed change)

**What:** add an ownership-gated in-place fast path to the array-mutating-method dispatch,
mirroring the index-store fast path that already exists and is proven safe in
`src/compiler_rust/compiler/src/interpreter/node_exec.rs:906-937`.

**Where (current, no-fast-path state, per the bug record's source citations):**
- `src/compiler_rust/compiler/src/interpreter_method/mod.rs:149` — `evaluate_method_call` clones
  the receiver via `evaluate_expr(receiver, ...)` before dispatch, unconditionally, for every
  method call including mutating ones.
- `src/compiler_rust/compiler/src/interpreter_method/collections.rs:50-66` — `handle_array_methods`
  "push"/"append"/"pop": unconditional `arr.to_vec()`, no ownership check.
- `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs:121,451-490` — the lvalue
  self-update write-back branch (`ARRAY_MUTATING_METHODS`) that recognizes `name.push(...)` on a
  bound identifier: re-invokes the above, then writes the whole new `Arc` back into the binding.
  This is also gate-free.

**Proposed shape (~40 lines, in `patterns.rs`'s array-mutating branch, before it falls through to
`evaluate_expr`):**
1. Require the receiver to be a bare `Expr::Identifier(name)` (matches the existing self-update
   branch's own precondition — it already restricts to this shape).
2. Look up `env.get(name)`; if `Value::Array(arc)` with `Arc::strong_count(arc) == 1 &&
   Arc::weak_count(arc) == 0`, take `env.get_mut(name)` → `Arc::get_mut(arc)` → mutate the `Vec`
   **in place** for `push`/`append` (`vec.push(item)`), `pop` (`vec.pop()`, return the popped
   element — also fixes the separate "pop returns whole array" defect in this path), `insert`,
   `remove`, `extend`, `clear` — no `.to_vec()`, no new `Arc` allocation, no env write-back needed
   (the binding's `Arc` is mutated through the existing pointer).
3. If the identifier is const (existing `CONST_NAMES` check already present) still reject before
   attempting the fast path — behavior unchanged there.
4. If not unique (`strong_count > 1` — aliased: `mut` param while caller retains it, module
   global, captured closure var) or receiver isn't a bare identifier (field access, index
   expression, method-chain result, etc.), fall through to the existing clone path unchanged —
   **value semantics preserved exactly**, identical safety argument to the shipped index-store fix.

**Why this is low-risk:** gated purely on `strong_count == 1`, so every case that currently
depends on aliased-array mutation being visible/invisible to other bindings keeps its current
(clone-based) behavior byte-for-byte. It mirrors an already-landed, already-proven pattern
(index-store) rather than inventing a new safety argument. Care points: `Vec::push` may reallocate
— fine under `Arc::get_mut(&mut Vec)`, no different from any other in-place `Vec` mutation;
`pop`'s in-place path must return the removed element, not the array (this actually *fixes*
a pre-existing minor defect, not introduce one — see bug record).

**Blast radius:** every `push`/`pop`/etc. call site in the whole codebase that mutates a uniquely
owned local array becomes O(1) amortized instead of O(N) per call — converts a pervasive O(N²)
list-building pattern to O(N) with zero source changes required elsewhere. Likely the single
largest available interpreter perf win given how idiomatic `push`-based list-building is.

**Gating — this IS a seed change, requires full-bootstrap:** `src/compiler_rust/` is the Rust
seed/runtime (per `.claude/rules/bootstrap.md` and the "default tooling = self-hosted binary, seed
is bootstrap-only" rule). There is no pure-Simple implementation of this interpreter to patch
instead — `95.interp/mir_interpreter.spl` is a different, flat-i64-slot MIR simulator with no `Arc`
arrays, not this code path. This is the legitimate exception the bootstrap rule anticipates for
something that structurally cannot be fixed in pure Simple: file it, implement in the seed,
land via an explicit `--full-bootstrap --deploy`, not as an incidental side effect of unrelated
work.

### Verification protocol for Track A (all must pass before landing)

1. **Aliasing spec (correctness gate, most important):** construct an array, bind it to two
   names (`val a = [...]; mut b = a` or pass as a `mut` param while the caller retains its own
   binding), mutate through one binding (`push`/`pop`/`a[i]=`), assert the **other** binding does
   **not** observe the mutation (value semantics preserved). Must hold both before and after the
   fast path lands — this is the same guarantee the index-store fast path already provides; the
   spec should mirror whatever spec currently protects that fast path if one exists, or be added
   alongside it if not.
2. **Perf gate:** re-run the sweep's `fill_push` harness (`mut a = []; for i in 0..n { a.push(i) }`)
   for n in {2000, 4000, 8000, 16000} post-fix; expect ~2×/doubling (O(N) total, matching
   `fill_idx`'s current numbers), not the pre-fix ~3.6–3.9×/doubling. The 84× gap at n=16000
   should close to roughly parity with `a[i]=`.
3. **Full test suite green:** `bin/simple test` (or the bootstrap-appropriate equivalent) with no
   new failures — mutating-method semantics (return values, especially `pop`'s element-vs-array
   return) must be unchanged for all existing callers.
4. **Representative render victim re-measured:** re-run one of the Track B victims below (e.g.
   `browser_renderer.spl`'s scene-op builder or `html_tokenizer.spl`'s token list build) at a
   realistic N and confirm wall time drops consistent with the O(N²)→O(N) prediction, not just the
   synthetic microbenchmark.

## TRACK B — immediate, unblocked: per-site `push`-in-loop → `[default; n]` + index-assign

No seed rebuild needed; ships today. Pattern already proven twice in the browser engine
(`style_rule_candidates` at `:4983` builds `[[i32]]` via `[[]; n]` + index-assign;
`SimpleWebHeuristicSurface.create` in `simple_web_engine2d_renderer.spl:11-17` replaced a
`pixels = pixels.push(x)` W×H loop with `[0u32; w*h]`, with an in-source comment naming this exact
bug). Apply the same two-shapes-of-fix to the ranked victims from the sweep, in order:

| Rank | Site | Pattern today | Fix shape |
|---|---|---|---|
| 1 | `browser_renderer.spl:87` `out = out.push(SceneCommand.stroke_rect(...))` | functional-reassign push, per-render scene-command list | two-pass: count ops first, then `[default; count]` + index-assign; or count is already known from node/rect counts |
| 2 | `html_tokenizer.spl` (17 push sites) | token list built per char/token, grows with document length | two-pass (pre-count tokens) or `Vec`-like growth amortization if a two-pass count isn't cheap; compounds with the separate `text.substring()` O(offset) bug — do not conflate fixes |
| 3 | `html_tree_builder.spl` (16 push sites) | node/stack lists per token | same shape, size ~ # nodes |
| 4 | `style_block_parse.spl` (12), `style_block.spl` (14) | decl/rule lists per token, size ~ CSS size | same shape; feeds `compute_styles` |
| 5 | `layout_paint.spl` (13), `layout_core.spl` (11) | draw-op/box lists per node, per frame | same shape |
| 6 | `webgl_context.spl` (124 sites), `webgpu_commands.spl` (26) | GL/GPU command buffers | same shape; only matters under `SIMPLE_EXECUTION_MODE=interpret` |
| 7 | engine2d executors (`gc_sync_mut`/`gc_async_mut/render_scene/engine2d_executor.spl`) | scene-op decode/build per op | same shape |
| 8 | `widget_to_dom.spl` (7), `dom_visual_effects.spl` (7) | DOM/effect lists per widget | same shape |
| — | **`simple_web_html_layout_renderer.spl` (ALL push sites, incl. `:8766` `ops = ops.push(scene_fill_rect(...))`)** | — | **NOT for now, the whole file** — this file is contended by concurrent work; do not touch ANY push site in it, ranked or not, without coordinating first |

For sites where the final size isn't known up front, use a two-pass count-then-fill (cheap count
loop, then `[default; count]` + index-assign) rather than growing a `Vec`-equivalent by hand —
that reintroduces the same problem one level down. Where genuinely unbounded/streaming, defer to
Track A rather than hand-rolling a growth strategy in Simple.

## Sequencing

1. **Now, unblocked:** apply Track B to ranked victims #1–#4 (scene-op builder + parsers) —
   these are the highest render-visible impact among the sites NOT excluded below and need no
   seed rebuild. Re-measure the 700/1500/3000-rule `compute_styles`/`parse_html` timing points
   used in the adjacent `text_substring_o_offset_parse_html_quadratic_2026-07-07.md` and
   `web_compute_styles_residual_quadratic_2026-07-06.md` records to confirm improvement without
   regressing those already-tracked numbers. **Explicitly excluded from "now":**
   `simple_web_html_layout_renderer.spl` in its entirety (every push site in that file, including
   the would-be-rank-1 `:8766` site) — it is contended by concurrent work; do not touch it until
   that work has landed and this plan is revisited.
2. **Land Track A as a deliberate, scheduled full-bootstrap** when the tree is quiet (per
   `.claude/rules/bootstrap.md` — not bundled incidentally into unrelated work). Run the full
   verification protocol above before deploy.
3. **After Track A lands,** the remaining Track B victims (#5–#8, and any repo-wide `push`-in-loop
   sites outside this ranked list — including `simple_web_html_layout_renderer.spl` once
   unblocked) become optional micro-opts, not required fixes — Track A retires the whole O(N²)
   class in one change. Do not invest further per-site refactor effort once Track A is verified
   and deployed.

## Verification Gates (rollup)

- Track B: each per-site refactor is a pure-Simple change — verify via the file's existing specs
  (byte-identical output pre/post refactor) plus a direct before/after timing note in the commit,
  no new seed/bootstrap step required.
- Track A: full protocol above (aliasing spec, perf gate, full test suite, representative victim
  re-measure) — no partial landing (e.g. shipping the fast path without the aliasing spec is not
  acceptable; that spec is what makes this safe).
- No claim of "fixed" for either track without a before/after measurement in the same commit or a
  linked follow-up commit — this plan exists precisely because an earlier unmeasured/fabricated
  perf claim (`compute_styles_nodes_arg_copy_quadratic_2026-07-07.md`, never landed) had to be
  caught and retracted before it shipped.
