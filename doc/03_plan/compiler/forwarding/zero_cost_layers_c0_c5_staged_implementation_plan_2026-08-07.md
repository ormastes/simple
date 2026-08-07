# Zero-cost layers (C0–C5) — staged implementation plan (2026-08-07)

Source sketch: `doc/03_plan/ui/perf/render_perf_redesign_plan_2026-08-06.md`
§3 (lines 131-217). Design detail already landed for a slice of this:
`doc/05_design/language/forwarding/layer_forwarding_and_layer_eq_types.md`.
This doc turns both into milestones a future session can execute one at a
time without half-finishing anything.

## 0. Reachability verdict — read this before scheduling any of it

**Source is pure Simple; the currently-deployed compiler is not.** Two facts,
checked this session, resolve what would otherwise be a hedge:

- `src/compiler/` is **100% `.spl`, 0 `.rs`** (`find src/compiler -name
  '*.rs' | wc -l` → 0, across all 17 numbered layers). The frontend
  (`10.frontend`), HIR (`20.hir`), semantics (`35.semantics`), MIR
  (`50.mir`/`60.mir_opt`), and driver (`80.driver`) are all self-hosted
  source today.
- `src/compiler_rust/` (the seed) has its **own complete, independent** Rust
  frontend/parser/HIR — `parser/`, `hir-core/`, `compiler/src/hir/`, ~30,277
  `.rs` files total. `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple`
  is, per the design doc's own landed-slice note, **the seed binary** ("the
  only binary in tree"). This is the load-bearing fact: **editing
  `src/compiler/10.frontend/*.spl` today does not change what `bin/simple`
  parses.** The two frontends are separate codebases, not one codebase with
  a self-hosted "view" — the seed does not read `src/compiler/` at all.

**Verdict:** C0-C5 is fully **source**-reachable in pure Simple — every file
this plan touches is `.spl`, no Rust-frontend blocker exists at the
source-location level. But it is **not runtime-reachable** through the
binary currently deployed as `bin/simple` until a pure-Simple self-hosted
build is produced (`bin/simple build bootstrap`) and that build is what gets
tested. Per standing rule `reference_simple_test_silently_delegates_to_seed_child.md`,
this is not a one-time caveat — every milestone below must state which
binary (seed `src/compiler_rust` vs. self-hosted `src/compiler/`) actually
ran its spec, because `bin/simple test ...` will silently run the seed and
report green while `src/compiler/*.spl` changes sit inert.

Consequence for sequencing: M0-M3 (checkers/validators over declared or
locally-computed facts, see below) can be authored and spec-tested today
under the seed for syntax/logic correctness, but their pass only proves
anything about the *language feature* once run against a self-hosted build
that actually parses through `src/compiler/10.frontend`. M2 in particular
(wiring to the compiler's *own* computed layout) is meaningless under the
seed, since the seed's layout computation lives in a different codebase
(`src/compiler_rust/compiler/src/hir` or wherever its layout pass is) — that
milestone's acceptance check is explicit about this.

## 1. What already exists (do not re-build)

| Artifact | State |
|---|---|
| `src/compiler/35.semantics/layer_eq_checker.spl` (98 lines) | Landed. Structural proof engine over **declared** `LayerEqType`/`LayerEqField` facts — obligations 1-4 of the design doc (field count, name mapping, per-field type+offset+size, whole-type size+align). Self-contained; not fed by real compiler layout computation yet. |
| `test/01_unit/compiler/semantics/layer_eq_checker_spec.spl` | 7 specs, seed-green, sabotage-tested (type check skipped → rejection specs went red, reverted). |
| `src/compiler/35.semantics/effect_verifier.spl` (385 lines) | Landed, 16/16 green this session. `@copy_budget(N)`/`@bounded_loop` verdict engine over **extracted facts** (`CopySite`, loop descriptors) — explicitly documents it is not yet fed by real MIR extraction ("driver/MIR work that cannot be verified in this tree"). |
| `src/app/desugar/forwarding.spl` (504 lines) | The CURRENT forwarding mechanism — text-level source generation, four phases. This is what C2 replaces. Not a stub; it is the thing being obsoleted, so C2 must keep it as fallback until collapse is proven (design doc §6 item 4). |
| `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md` | Facet/dynSMF design C3 should extend, not duplicate. |
| `layer` keyword / `@layer_eq` / `@layer_field` / `HirForwardDecl` in the parser or HIR | **Absent** — confirmed by grep this session (only hit is the checker file name itself). No `"layer"` token in `10.frontend` parsing at all. |

The design doc's own §6 "Honestly deferred" list (6 items) is the TODO queue
this plan schedules into milestones. Re-reading it before starting any
milestone below is cheaper than re-deriving it.

## 2. Milestone breakdown

Numbering matches the sketch's C0-C5 lanes; each is split further where a
single lane is still too large to be "smallest independently shippable."
Fidelity intentionally drops after M3 — see §3.

### M0 — `layer` declaration parsing + DAG validation (zero runtime effect)

**Scope:** parse `layer NAME` and `layer NAME uses A, B`; build the layer
DAG; reject cycles and reject declared-upward `uses` edges. No `@layer(...)`
module tagging yet, no type/forwarding semantics. This is deliberately the
"decisive first milestone" — same shape as the perf plan's own §0: a small,
provable, all-or-nothing check with zero behavioral coupling to anything
else.

- Files:
  - `src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl` and
    `src/compiler/10.frontend/core/tokens.spl` — top-level decl-kind keywords
    (`"trait"`, `"struct"`, `"module"`) and their token entries live here;
    add `layer` alongside them (grep this session:
    `grep -rln '"trait"\|"struct"\|"module"' src/compiler/10.frontend` hits
    exactly these plus `frontend.spl`, `core/hir_types.spl`,
    `core/interpreter/value.spl`, `core/types.spl`,
    `_FlatAstBridge/module_assembly.spl` — confirm the precise decl-dispatch
    site while implementing, this is the entry list to start from, not a
    single-file guess).
  - New: `src/compiler/35.semantics/layer_dag_checker.spl` — registry of
    declared layers + `uses` edges, cycle detection (reuse or mirror the
    style of `noalloc_checker.spl`'s registry pattern), one diagnostic per
    cycle/upward-edge violation.
  - New spec: `test/01_unit/compiler/semantics/layer_dag_checker_spec.spl` —
    accepted acyclic DAG (draw ← gui ← web/wm from the sketch verbatim),
    rejected 2-cycle, rejected 3-cycle, rejected self-edge, rejected
    declared-upward `uses`.
- Precedent to apply: **sabotage test** the cycle detector itself (skip the
  visited-set check → cycle specs must go red) before calling it done, same
  as the layer_eq_checker's landed slice. State which binary (seed vs
  self-hosted) ran the spec, per §0.
- Done / not-half-finished check: `bin/simple test test/01_unit/compiler/semantics/layer_dag_checker_spec.spl`
  green, sabotage reverted, AND a `layer` decl with no `@layer_eq`/forwarding
  usage anywhere else compiles through the full pipeline unchanged (proves
  "zero runtime effect" isn't just asserted in prose — nothing downstream
  breaks when a codebase adds layer decls and does nothing else with them).

### M1 — `@layer(gui)` module tagging + same-layer/downward call rule

**Scope:** parse `@layer(NAME)` on `module` decls; resolve a symbol's owning
layer; add the semantic check "a call target's layer must equal the caller's
layer or be reachable via a downward `uses` edge from M0's DAG." Still zero
runtime effect — this is a static rejection pass, no codegen change.

- Files: extends `layer_dag_checker.spl` (or a sibling
  `layer_call_direction_checker.spl` if the registry gets unwieldy — decide
  at implementation time, don't pre-commit to a file split that turns out
  wrong).
- Spec: same-layer call accepted, downward call accepted, upward call
  rejected, cross-branch call (draw→wm with no edge) rejected.
- Acceptance: same shape as M0 — spec green + sabotage + binary-provenance
  statement. Additionally: run against one real existing module pair to
  confirm the check doesn't false-positive on real code before it's turned
  on repo-wide — this is the "both-engine"-style proportionality check
  translated to this domain (real code, not just fixtures). Concrete target:
  `src/lib/gui/` (GUI-layer candidate) against `src/lib/common/ui/draw_ir_v3_*.spl`
  / `src/lib/nogc_sync_mut/ui/draw_ir_v3_*.spl` (draw-layer candidate) —
  located this session via `find src/lib -iname '*gui*' -maxdepth 3 -type d`
  and `find src/lib -path '*ui*draw*'`. Neither directory is tagged with
  `@layer(...)` yet; run the check in dry-run/report mode against them, not
  enforced — tagging real modules is out of scope for this milestone.

### M2 — production-wire `layer_eq_checker.spl` to real layout, not fixtures

**Scope:** design doc §6 item 3, verbatim. Replace `LayerEqType`/
`LayerEqField` fixture construction with values read from the compiler's
actual field-layout computation (wherever `30.types` or `50.mir` computes
struct offsets today — locate it first, don't assume a location). Parse
`@layer_eq(...)`/`@layer_field(...)` into that registry (§6 item 1, the part
of item 1 not already covered by M0/M1).

- Files: `src/compiler/10.frontend` (attribute parsing, same decl-kw sites as
  M0), `src/compiler/30.types/type_layout.spl` + its `_TypeLayout/` split
  modules (`layout_core.spl` for `compute_struct_layout`/`FieldLayout`/
  `TypeLayout`, `arch_and_verify.spl` for `compute_field_offset`/
  `compute_layout`) — this is the compiler's real layout computation,
  located this session via
  `grep -rln 'field_offset\|struct_layout\|compute_layout\|layout_of' src/compiler/30.types` —
  and `src/compiler/35.semantics/layer_eq_checker.spl` (consumes real layout
  instead of fixture structs — likely an adapter function from `TypeLayout`/
  `FieldLayout` to `LayerEqType`/`LayerEqField`, not a rewrite of the proof
  logic itself, since obligations 1-4 are already correct against declared
  facts).
- Spec: extend `layer_eq_checker_spec.spl` with real-struct cases (two
  structs with genuinely identical compiler-computed layout vs. one with
  compiler-inserted padding difference the fixture-only version couldn't
  have caught).
- Acceptance: the padding-difference case is the load-bearing one — it must
  be a case where fixture-declared "same size" would have wrongly passed but
  real layout correctly fails. If no such case exists, the milestone hasn't
  actually proven anything beyond M1.
- Flag per §0: this milestone's spec result is only meaningful if it's
  confirmed against the compiler's own layout computation as it exists in a
  live build (seed or self-hosted) — state which.

### M3 — obligations 5-8 (enum discriminants, ownership, address space, unit/color/alpha tags)

**Scope:** design doc §6 item 6. Parse `@unit`/`@space`/`@color`/`@alpha`
tags; extend `check_layer_eq` with obligations 5-8 (currently only 1-4 are
implemented — confirmed by reading the 98-line file in full this session).
"Absent tag ≠ any tag" is the one rule most likely to be gotten backwards —
make that its own explicit spec case.

- Files: `layer_eq_checker.spl` (extend `LayerEqField`/`LayerEqType` with
  discriminant/ownership/address-space/tag fields), frontend tag parsing.
- Spec: extend `layer_eq_checker_spec.spl`; explicit negative case for
  `CssLogicalRect → DevicePixelRect` (must stay rejected — this is the
  design doc's own worked "never equivalent" example, so it's a regression
  guard, not a new scenario to invent).
- Acceptance: same pattern as M2.

**Below this line, fidelity drops deliberately** — C2-C5 are multi-week
compiler-pass work (a transitive forwarding graph, MIR-level chain collapse,
AOP weaving, devirtualization) that this planning pass will not pretend to
design in full. What follows is scope + sequencing + acceptance shape only.

### M4 (= C2) — `HirForwardDecl` emission, phase-by-phase retirement of text-desugar

Emit `HirForwardDecl` metadata for the *simplest* of `src/app/desugar/forwarding.spl`'s
four phases first (`fn name = target` — no field-path projection, no trait
alias, no blanket alias) while leaving the other three phases on the current
text-generator. Keep both paths live simultaneously, selected per forwarding
site, until each phase's collapse is independently proven — this is the
design doc's own §6 item 4 instruction ("retire... phase-by-phase... keep as
fallback until collapse works, gated by the §4 zero-hop counters"), not a new
idea introduced here. Do not attempt the field-path/trait/blanket phases in
the same milestone as the plain-symbol phase — each is its own shippable
slice with its own before/after physical-hop-count proof.

### M5 (= C3) — logical AOP join points

Scope only after M4's join-point IDs exist and are stable, since C3 targets
`logical_join_point_id` from `HirForwardDecl`. Extend the existing
facet/dynSMF design rather than building a parallel interception path (design
doc §4, "extends the facet/dynSMF design above" — explicit instruction
already on record). Static-weave mode only for the first slice; dynload and
live-reload modes are separate follow-on milestones, not bundled in.

### M6 — production-wire `effect_verifier.spl` to real MIR extraction

Effect verifier (C4) already exists and passes 16/16 against **extracted
facts**; its own file states the extraction from real code is undone driver/
MIR work. This milestone is that wiring — feed it real `CopySite`/loop
descriptors from the post-M4/M5 MIR instead of hand-built fixtures. Sequenced
after M4/M5 because "post-weave, post-collapse MIR" (the verifier's stated
target per the sketch) doesn't exist as a concept until collapse (M4) and
weaving (M5) land.

### M7 (= C5) — `@zero_forward_path` mechanical gate

Last, because it's a compile-fail gate over the counters (`physical_forward_calls=0`,
`layer_view_copy_bytes=0`, etc.) that only M4-M6 produce. Scope: wire the gate
to already-existing counters; do not invent new measurement machinery here if
M4-M6 already emit what's needed — re-check before adding anything.

## 3. Sequencing dependency chain

```
M0 (layer DAG) → M1 (call direction) → M2 (real layout) → M3 (tags/obligations 5-8)
                                                                    ↓
                                              M4 (HirForwardDecl, phase-by-phase)
                                                                    ↓
                                              M5 (AOP join points, static weave)
                                                                    ↓
                                              M6 (effect verifier real wiring)
                                                                    ↓
                                              M7 (@zero_forward_path gate)
```

M0-M3 are genuinely independent-shippable in the sense the task asked for:
each has its own file list, its own spec target, its own sabotage-tested
acceptance check, and does nothing to running code if left there
unfinished by a future session (all are static-analysis-only additions with
no codegen change). M4 onward is where "shippable" starts meaning "shippable
within its own phase-scoped sub-slice," not "shippable as one PR" — flagged
here rather than sketched to false precision.

## 4. Standing-rule anchors to reapply per milestone (not restated per-item above)

- Binary provenance: state seed vs. self-hosted per spec run
  (`reference_simple_test_silently_delegates_to_seed_child.md`).
- Sabotage-then-revert on every new checker/verifier before calling it done
  (established precedent: both `layer_eq_checker.spl` and this session's
  `effect_verifier.spl` work).
- No half-finished implementation: a milestone that can't clear its own
  acceptance check by the "done" bar stated above is not landed — it's filed
  as a TODO/bug per this repo's "implement or delete" rule, not shipped as a
  partial stub.
- Push each landed milestone to GH immediately, not batched
  (`feedback_push_gh_immediately_after_each_bug_fix.md`).
