# Interpreter: font-load blows up from ~8s to 2+ min merely by having an unrelated Engine2D alive on the stack

- **Date:** 2026-07-25
- **Lane:** 2D headless showcase (`examples/06_io/ui/graphics_2d_showcase.spl`), interpreted (seed `bin/simple run`, Linux x86_64)
- Status: **FIXED (interpreter side) 2026-08-20** — see "Actual root cause" below.
- **Verification 2026-08-21 (bug-status-consistency audit): PARTIAL, not fully fixed.** `try_field_array_mutation_in_place` + guard landed, but the doc's own "Still open" items (font-load lane not re-timed; pure-Simple `src/compiler/95.interp` uninspected) are unaddressed. `bug_db.sdn` row is `fix-implemented-verification-pending`.
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Actual root cause (2026-08-20) — it is NOT a GC root scan

**There is no GC root scan in the Rust seed's AST interpreter.** A census of
`src/compiler_rust/compiler/src/interpreter*` and `runtime/src/value` finds no
`mark_roots` / `root_set` / `collect` path at all, so the "root-scan cost scales
with live object graph" hypothesis in the section below is wrong. The title is
kept for traceability; the mechanism is different.

The real defect is an **aliasing-induced O(N^2)** in mutator dispatch:

- `arr.push(x)` on a **bare identifier** receiver is already O(N) amortized.
  `interpreter_helpers/patterns.rs` re-reads the binding via `env.get_mut` and
  calls `Arc::make_mut`; the binding is uniquely owned, so the backing `Vec` is
  mutated in place.
- `obj.field.push(x)` (i.e. every accumulation into an object field, which is
  what `FontRenderer` / `FontRasterizer` construction does) went through
  `interpreter/expr/calls.rs`, which copied the field value into a
  `__nested_field_<name>__` **temp binding**. That second strong reference made
  the array Arc aliased, so `Arc::make_mut` took its clone branch and copied the
  **entire backing Vec on every single push**. Accumulating N elements into a
  field cost O(N^2).

Measured on the seed (`SIMPLE_EXECUTION_MODE=interpret`), building an N-element
array into a class field — exactly 4x per doubling, the signature of a quadratic:

| N | before | after |
|---|--------|-------|
| 5,000  | 0.46s | 0.06s |
| 10,000 | 0.55s | 0.07s |
| 20,000 | 2.07s | 0.09s |
| 40,000 | 8.02s | 0.12s |

The same probe with a **local** array (`var a = a.push(i)`) was linear both
before and after, which is what isolates the field receiver as the culprit.

This also explains the original "unused `Engine2D` makes it 15x slower"
observation without any GC: an `Engine2D` in scope changes which receiver shapes
the font-load call chain takes and how many strong refs the accumulating arrays
carry, flipping the in-place branch to the clone branch.

## Fix

- `src/compiler_rust/compiler/src/interpreter_helpers/patterns.rs` — new
  `try_field_array_mutation_in_place()`: evaluates the mutator's arguments FIRST
  (so a self-referential argument still bumps the refcount and correctly forces
  the clone branch), then re-reads the object through `env.get_mut` and mutates
  the field array via `Arc::make_mut`. Uniquely owned mutates in place; aliased
  clones-then-mutates, so **value semantics are byte-for-byte unchanged**. Uses
  the existing `apply_array_mutation_in_place` kernel, so the field lane and the
  identifier lane are provably identical in behaviour.
- `src/compiler_rust/compiler/src/interpreter/expr/calls.rs` — calls that helper
  before the `__nested_field_*__` temp-binding path; returns `Ok(None)` and falls
  through unchanged for every shape it does not cover.

## Evidence

- Semantics: `test/01_unit/compiler/interpreter/field_array_mutation_in_place_spec.spl`
  — push/pop/insert/remove/extend/clear plus alias-non-observation. Output is
  identical on the pre-fix and post-fix binaries.
- Cost (fails pre-fix): `sh scripts/check/check-interp-field-array-push-linear.shs`
  — `FAIL — ... doubling N cost 364x100 ...` on the deployed seed,
  `PASS — ... ratio 127x100 ...` on the fixed binary. `--selftest` is fatal and
  runs first.
- No regression: `cargo test --release -p simple-compiler --lib` reports
  **3672 passed / 66 failed** both with and without the change — an identical
  pre-existing baseline in this working tree.

## Still open

The font-load lane itself was not re-timed end to end (the 17.8MB
`NotoSansSC[wght].ttf` repro is expensive and the showcase lane has other
blockers). The pure-Simple self-hosted interpreter (`src/compiler/95.interp`)
was not inspected; if it has the same temp-binding shape it needs the same fix.

## Symptom

This is the dominant remaining cause of the "2D x headless" regression in
`doc/09_report/showcase_matrix_fresh_evidence_2026-07-25.md` (no evidence line after
40+ min, independent of canvas resolution). The `sha256_bytes` O(N^2) `.push()` bug
(`doc/08_tracking/bug/sha256_bytes_push_quadratic_font_hash_2026-07-25.md`) was fixed
first and is real, but fixing it alone does **not** resolve the hang: with the fix
applied, `graphics_2d_showcase.spl` at 32x24 still times out (60s+) at the exact same
call, `Engine2D.load_font(...)`.

## Isolation (gdb backtrace + bisection)

1. `gdb`-interrupt sampling of the hung process (`handle SIGINT stop`, `thread apply
   all bt`) showed thread `simple-main` continuously on-CPU (utime climbing linearly,
   ~1 CPU-second consumed per wall-clock second — genuinely busy, not I/O-blocked),
   with a stable ~111-117 frame deep interpreter call stack
   (`evaluate_module_impl` -> ... -> `handle_method_call_with_self_update` ->
   `exec_block_fn` -> `exec_function_with_self_return`, repeating) — not growing
   unboundedly, so not naive infinite recursion either.
2. Primitive-by-primitive bisection (isolated `.spl` probes: basic shapes, curves,
   gradients/images/mask/engine-composition all completed in well under a second)
   narrowed the hang to font loading specifically.
3. Calling `FontRenderer.new().try_load_runtime_ttf(path)` **standalone** (no
   `Engine2D` anywhere in the program) on the real 17.8MB default font
   (`NotoSansSC[wght].ttf`) completes in **~8 seconds**, reliably, repeatedly.
4. Adding a single **unused, untouched** `var e = Engine2D.create_offscreen(32, 24)`
   earlier in the *same function* — never read again until after the font-load call —
   makes the identical `try_load_runtime_ttf(path)` call take **2+ minutes and still
   rising** (killed at the 120s bound, still had not printed its completion line).
5. Moving the font-load call into a **separate function**, called from a caller that
   still holds a live `Engine2D`, reproduces the same blowup — so this is not about
   lexical scope; it is about `Engine2D` being reachable anywhere on the live call
   stack / heap root set while the font blob is being loaded and incrementally
   processed.

## Working hypothesis

This looks like a GC (or interpreter value-copy) root-scanning cost that scales with
the size/complexity of the live object graph, triggered repeatedly during font
loading (each of the many small field writes / array touches involved in
`FontRasterizer` construction, `FontRenderer._try_install_ttf`, cache invalidation,
etc.). With no other large live object around, the per-touch root-scan is cheap; with
an `Engine2D` (or its nested Option-typed backend fields) also live, each touch
apparently re-walks a much larger/more expensive root set, and this cost compounds
over the many small mutations that happen while loading and validating a 17.8MB font
blob — consistent with the observed >15x slowdown (8s -> 120s+) from adding one
inert, unrelated local variable.

## Why this is filed, not fixed here

This does not look like an application-level `.spl` antipattern (no missing
pre-sizing, no wrong loop bound, no `arr = arr.push(v)` reassignment pattern found in
the font-load call chain beyond the already-fixed `sha256_bytes`). The reproduction
step in item 4 above — an **unused** local of an unrelated type changing the cost of
a completely separate call by an order of magnitude — points at the interpreter's
GC/value-semantics implementation itself (`src/compiler_rust/interpreter` on this
seed binary; the original regression report ran the self-hosted binary, so the same
or an analogous defect likely lives in the self-hosted interpreter as well, though
this could not be independently confirmed on this Linux dev box, which has no
deployed self-hosted `bin/simple` — only the Rust seed). Per
`.claude/rules/bootstrap.md` / `feedback_fix_spl_not_rust`, this needs the interpreter
implementation's owner rather than a library-level patch, and per `feedback_no_coverups`
should be filed rather than worked around with a fragile, unexplained reordering of
`.spl` call sites.

## Suggested next step

Profile the interpreter's GC/root-scan path (or its per-array-mutation bookkeeping)
under a workload that (a) keeps one large, mostly-idle live object graph around and
(b) incrementally builds/mutates a large array elsewhere, to find whether root-scan
cost is accidentally proportional to total live heap size per mutation rather than
being amortized. A synthetic repro (no font/TTF dependency) would help: allocate a
large dummy class instance, keep it alive, then time an unrelated large-array build
loop with and without that instance in scope.

## Repro artifacts (this session, scratchpad — not checked in)

- `probe_fontrenderer.spl` — standalone font load, ~8s.
- `probe_engine_loadfont_direct3.spl` — same load with an unused `Engine2D` alive in
  the same function, 120s+ and still not done.
- `probe_engine_loadfont_separate_fn.spl` — same load moved to a separate function,
  caller still holds `Engine2D`; same blowup.
