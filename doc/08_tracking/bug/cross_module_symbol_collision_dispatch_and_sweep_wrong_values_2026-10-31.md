# Cross-module symbol collision: wrong dispatch is real, and the caret sweep wrong values are three separate defects

Status: OPEN
Date: 2026-10-31
Seed under test: `build/sweep-seed-simple-v2` (branch `release/1.0.0`)
Logs: `build/sweep/logs/main_spec.log`, `types_spec.log`,
`distributed_host_registry_sdn_v2_spec.log`, `build/sweep/results/caret-unit.tsv`

## Symptom

The caret unit sweep emits
`[compiler_cross_module_private_symbol_collision]` warnings (for
`env_get`, `skip`, `atomic_bool_new`, `atomic_i64_new`, `unwrap_str`,
`parse_query_string`, `register_tool`, ...) and several specs then produce
wrong values:

- `test/01_unit/app/llm_caret/main_spec.spl`:
  `expected dummy to equal claude_cli` (resume example) and
  `expected 200 to equal 413` (guard_request size cap).
- `test/01_unit/app/llm_caret/types_spec.spl`:
  `creates generic event: expected  to equal payload`.
- `test/01_unit/app/llm_caret/distributed_host_registry_sdn_v2_spec.spl`:
  3 failures `expected HOST_CONFIG_TYPE to equal ...`.

All specs ran on the **interpreter** (seed emits no MC/DC probes).

## Finding 1 — the collision warning's fallback CAN dispatch to the wrong body (compiler bug, confirmed)

The warning is emitted from
`src/compiler_rust/compiler/src/pipeline/module_loader.rs:1806-1817`
(differing-signature arm; same-signature arm at 1780-1794 is default-off via
`SIMPLE_DIAG_SAME_SIGNATURE_COLLISION`; class arm at 1846-1857). The JIT side
mitigates direct calls with mangled `$dupN` variants
(`src/compiler_rust/compiler/src/mir/lower/lowering_core.rs:1901-1957`) and
exact arg-type match with arity fallback and a **last-definition fallback**
(`src/compiler_rust/compiler/src/mir/lower/lowering_expr_call.rs:848-869`).
The interpreter has no such machinery: module merging is a flat bare-name
map, last write wins
(`src/compiler_rust/compiler/src/interpreter_module/module_merger.rs:31`,
dispatch at `src/compiler_rust/compiler/src/interpreter_call/mod.rs:849`).
Whatever module merges last wins every call to the bare name, regardless of
what the caller imported. The pure-Simple side has the same flat
last-write-wins table with only a warning
(`src/compiler/10.frontend/core/interpreter/eval_tables.spl:279-293`,
warning at `:277`; owner-aware resolution exists at `:408-430` but the
comment at `:429` admits the call evaluator still applies the legacy flat
fallback).

Minimal repro (wrong dispatch observed):

```
$ timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/symbol_collision_repro.spl --no-session-daemon
warning: public function `probe_whoami` has 2 co-compiled definitions with 2 differing signatures ((text)->i64 vs (text)->text); JIT call sites resolve by exact arg-type match (mangled `$dupN` variants), falling back to the last definition when types are ambiguous — a fallback hit may still dispatch to the wrong one. Rename the conflicting helper(s) to a unique name. [compiler_cross_module_private_symbol_collision]
markers: a=a b=b
probe_whoami("caller-arg") returned: 424242
DISPATCH WRONG: imported sc_dup_a.probe_whoami is (text)->text, but the call produced '424242' — sc_dup_b's (text)->i64 body executed instead
```

Files: `build/sweep/probes/sc_dup_a.spl`, `sc_dup_b.spl`,
`symbol_collision_repro.spl` (the caller imports only `sc_dup_a.probe_whoami`;
`sc_dup_b` is co-compiled for an unrelated marker and merges last).

## Finding 2 — `expected dummy to equal claude_cli`: if/match EXPRESSIONS revert pending module-global writes (seed interpreter bug, confirmed; the actual cause of this failure)

`expected dummy to equal claude_cli` is **not** caused by the collision
warning's fallback. Bisection with an instrumented copy of
`src/app/llm_caret/main.spl` (`build/sweep/probes/patched/llm_caret/main.spl`,
runner `build/sweep/probes/patched_apply_probe.spl`) shows:

```
DBG apply enter: RT_PROVIDER='dummy' sess.provider='claude_cli'
DBG after RT_PROVIDER assign: RT_PROVIDER='claude_cli'
DBG after literal-if: m_computed='y' RT_PROVIDER='dummy'   <- val x = if true: "y" else: "z" REVERTED the write
```

In `apply_resumed_session` (`src/app/llm_caret/main.spl:1187-1203`), the
write `RT_PROVIDER = sess.provider` lands, and the very next statement
`RT_MODEL = if sess.model == "": ... else: ...` — an **if-expression** —
reverts `RT_PROVIDER` to the pre-call value; the result is then built with
the stale provider. Characterization:

- Plain assignments, nested function calls, and if/match **statements** do
  not revert (verified).
- **if-expressions and match-expressions** revert module-global writes made
  earlier in the same function (`val m = if true: "y" else: "z"` suffices;
  literal branches, field-access branches both trigger).
- A standalone single-file probe (`build/sweep/probes/if_assign_global_probe.spl`)
  does **not** reproduce; the defect needs the large llm_caret co-compiled
  unit (CowEnv overlay / scope re-point path engaged).

The relevant machinery is the module-global write-back/refresh channel:
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
(`publish_live_bound_globals` :230, `refresh_live_bound_globals` :288,
`sync_owned_captured_globals` :335, `publish_and_repoint` :206) and the
if/match expression evaluator
`src/compiler_rust/compiler/src/interpreter/expr/control.rs:79-201`. Recent
commits touching this exact area: `8e9fd4efeb2` ("fix(seed-interp):
module-global write-back"), `da5b603d0ff` ("share imported module tables by
reference, not by copy"), `e0d455e6183` ("fix(coverage): real condition
probes"). Suspected regression window; needs `git bisect` against a spec
that exercises it (`test/01_unit/app/llm_caret/main_spec.spl` resume
example, or `patched_apply_probe.spl` reduced).

Attribution probes: `build/sweep/probes/resume_dummy_probe.spl`,
`resume_dummy_probe2.spl` (file on disk and direct `load_session` both show
`claude_cli`; only the value returned through `apply_resumed_session` is
`dummy`), `rt_provider_probe.spl` (a sibling function's write to the same
global *does* stick — only the write followed by an if/match expression
reverts), `global_write_probe.spl` (standalone pattern correct).

Whether the pure-Simple interpreter (`src/compiler/10.frontend/core/interpreter/`)
inherits this specific defect is UNVERIFIED — no `bin/simple` was available
to run the same probe.

## Finding 3 — vendored stale stdlib snapshot co-compiles and corrupts `SdnValue`-typed code (seed loader bug, confirmed mechanism, load-order dependent)

`distributed_host_registry_decode_v2` returns `HOST_CONFIG_TYPE` for a valid
document (repro: `build/sweep/probes/registry_decode_probe.spl`; instrumented
copy `build/sweep/probes/patched_wb/`). Root cause chain:

- `src/compiler_rust/lib/std/src/` is a stale, un-tiered stdlib snapshot
  whose `sdn/value.spl` defines `enum SdnValue` with variants
  `Null/bool/i32/f32/text/Array/Dict/Table` — **disjoint** from the project
  enum at `src/lib/common/sdn/value.spl:28`
  (`Null/Bool/Int/Float/String/Array/Dict/Table`).
- The project `src/lib/common/sdn/` has **no `__init__.spl`**; the seed's
  stdlib path resolution probes the vendored tree as a fallback
  (`src/compiler_rust/compiler/src/interpreter_module/path_resolution.rs:848-858`,
  vendored subpath at `:851`), so the vendored `sdn/__init__.spl` (which
  re-exports the vendored `SdnValue`) can be co-compiled into the same unit.
- Enum registration is a flat bare-name last-write-wins map with **no
  collision warning** (`src/compiler_rust/compiler/src/interpreter_module/module_merger.rs:55`;
  the census in `pipeline/module_loader.rs:1690-1858` warns functions and
  classes only — enums are not covered).
- Observed corruption in the failing unit: `credential_reference:
  secret://roles/...` parses as a nested mapping `{secret: ...}` instead of a
  String (parser behavior differs — vendored parser wins), and a
  `Dict<text, SdnValue>` mis-indexes (`fields["identity"]` returns the
  `credential_reference` entry; `build/sweep/probes/dict_index_probe.spl`
  prints empty lines for exactly the two `SdnValue`-valued lookups, while the
  same four keys in `Dict<text, i64>` are correct —
  `build/sweep/probes/dict_collision_probe.spl`). The same source parses and
  matches correctly in a differently-ordered unit
  (`build/sweep/probes/registry_shape_probe.spl`) — classic
  registration-order-dependent silent wrongness.

Suggested directions: (a) delete or exclude the stale vendored snapshot from
stdlib fallback search; (b) add the missing project
`src/lib/common/sdn/__init__.spl`; (c) extend the collision census to enums
(and to generic-type-identity collisions).

## Finding 4 — two of the sweep failures are NOT compiler bugs

- `expected 200 to equal 413`: stale spec. `MAX_BODY_BYTES` was legitimately
  raised from 1,000,000 to 30,000,000 in `src/app/llm_caret/main.spl:716`
  (commit `88aac2ffe28`, image-proxy hardening); the spec
  (`test/01_unit/app/llm_caret/main_spec.spl:768-778`) still builds only a
  1,280,000-byte body, so `guard_request` correctly allows it. Fix the spec.
- `creates generic event: expected  to equal payload`: spec/source drift.
  The spec calls `new_stream_event("content_block_start", "")` and expects
  `content == "payload"` (a default-fill the current
  `src/app/llm_caret/types.spl:149-158` never had on this branch); the
  struct copies `content` verbatim. Either the spec or the source lost a
  default during the main→release/1.0 transplant — reconcile intent.

## Repro

```
timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/symbol_collision_repro.spl --no-session-daemon
timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/resume_dummy_probe2.spl --no-session-daemon
timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/patched_apply_probe.spl --no-session-daemon
timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/registry_decode_probe.spl --no-session-daemon
timeout 240 build/sweep-seed-simple-v2 run build/sweep/probes/dict_index_probe.spl --no-session-daemon
SIMPLE_DIAG_SAME_SIGNATURE_COLLISION=1 build/sweep-seed-simple-v2 test test/01_unit/app/llm_caret/main_spec.spl --no-session-daemon   # 359 silent same-sig collisions in one spec
```

## Status: OPEN
