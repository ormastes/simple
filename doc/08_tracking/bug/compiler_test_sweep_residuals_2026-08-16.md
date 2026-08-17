# Compiler test sweep residuals — 2026-08-16

Triage of unfixed failures from the 2026-08-16 compiler test sweep. Engine:
`bin/simple test` (tree-walk interpreter path). One item was a stale spec and is
FIXED in this change; everything else is filed here with root-cause notes.

## Fixed in this change

- **lexer_intensive_spec: `#[` no longer emits TOK_HASH_LBRACKET** — intentional
  migration: commit `b2fbb38fc6f7` "refactor: unify tag system — merge #[]
  attributes into @ syntax". The lexer (`src/compiler/10.frontend/core/lexer_struct.spl:1384`)
  now treats every `#` as a comment start. Spec updated to assert `@test` emits
  `TOK_AT` and that `#[test]` emits no `TOK_HASH_LBRACKET`. `TOK_HASH_LBRACKET`
  still exists in `tokens.spl:211` (exported) but is dead — candidate for removal.

## Filed: interpreter gaps (unit, `test/01_unit/compiler_core/`)

All fail as `expected false to equal true` — the interpreter feature under test
is absent or returns the wrong shape, not a flaky harness.

1. **while finite-iteration guard** (`lang_basics_spec.spl`, 2 examples: while
   statements and while expressions). Interpreter does not enforce/report the
   finite-iteration guard the spec asserts.
2. **receive/after-timeout parsing** (`receive_spec.spl` "should parse receive
   arms and after timeout arms"). Parser/interpreter path for `receive ... after
   <timeout>:` arms does not produce the expected arm structure.
3. **match-exhaustiveness warning** (`exhaustiveness_spec.spl` "should keep
   interpreter match warnings on no matched arm"). Interpreter no longer emits
   (or the harness no longer surfaces) the no-matched-arm warning.
4. **nested-optional nil** (`branch_coverage_30_spec.spl` "optional - all nil
   levels"; `branch_coverage_35_spec.spl` "optional of optional - nil inner").
   `Option<Option<T>>` with nil inner/outer levels evaluates incorrectly.
5. **pipe to placeholder-lambda in parens** (`parser_pipe_operator_spec.spl`):
   `expected <lambda> to equal 15` — the parenthesized placeholder lambda is not
   applied by `|>`; the lambda value itself leaks through unevaluated.
6. **string-interpolation segment count** (`parser_intensive_spec.spl` "parses
   strings with and without interpolation"): `expected 3 to equal 34` — segment
   splitting returns a wrong count/shape.
7. **Option with unknown inner type tag** (`parser_spec.spl` "parses Option with
   unknown inner type"): `expected 300 to equal 14` — type node gets an
   error/unknown tag (300) instead of the Option tag (14).
8. **module-level pseudo-decl arena OOB** (`parser_spec.spl` "parses
   module-level expression as pseudo-decl", plus "parses a mixed module"
   `expected 7 to equal 6`): module-level expression is not wrapped as a
   pseudo-decl; downstream arena index read goes out of bounds.

## Filed: integration backend failures (`test/02_integration/compiler/`)

From `B_compiler_02_integration.log` (457 total, 55 failed). Toolchain presence
checked on this host: ghdl, llc, clang ARE installed — none of these is a
missing-toolchain environment failure; all are real defects, in two families.

- **vhdl_backend_e2e_spec.spl (20 passed / 21 failed)** — two causes:
  (a) real VHDL backend defect: `CompileError(phase: backend (vhdl), message:
  VHDL combinational local 'arr_sig' must be a fixed scalar or record)` — array
  locals in combinational context are rejected; (b) `semantic: unknown extern
  function: rt_process_run_capture` — the interpreter running the spec lacks the
  process-capture extern, so simulation-run assertions cannot execute
  (environment/runtime-binding gap, not a VHDL defect).
- **advanced_types_spec.spl (2 passed / 10 failed)** — diagnosed; see
  "advanced_types_spec.spl — per-example diagnosis (2026-08-16 follow-up)"
  below: compile-delegation-loop guard in the lightweight external driver
  facade blocks all in-process check/compile calls under the test runner.
- **llvm_backend_e2e_spec.spl (20 passed / 6 failed)** and
  **llvm_parity_spec.spl (3 passed / 4 failed)** — same root cause family:
  `semantic: method 'with_cpu_override' / 'with_llvm_ir' / 'with_assembly' /
  'with_compile_time' not found on value of type object in nested call context`.
  This is the known erased-receiver method-chain limitation (builder chains on
  values whose static type was erased) hitting the specs' CompileOptions-style
  builder — an interpreter method-resolution defect, not an LLVM codegen one.
  **FIXED (verified 2026-08-16):** root cause is the Rust seed interpreter's
  nested-call dispatcher `call_method_on_value`
  (`src/compiler_rust/compiler/src/interpreter_helpers/method_dispatch.rs`)
  having no arm for `Value::ClassInstance` receivers (`type_name()` reports
  them as "object"), so any chain link whose receiver was a ClassInstance —
  e.g. `LlvmBackend.create(...).with_llvm_ir()` — fell through to the error.
  A `Value::ClassInstance` arm mirroring the primary evaluator (class-body
  methods → local impl map → GLOBAL_IMPL_METHODS → TRAIT_IMPLS, `self` bound
  via the single-entry "self" fields convention) fixes it. Verified with a
  seed rebuilt from that source: llvm_backend_e2e_spec 20/26 → 24/26 (the 2
  residual failures are unrelated env/oracle issues: llc path resolves to
  `/usr/bin/llc-20`, and cpu compat expects `x86-64` but gets `x86-64-v1`);
  llvm_parity_spec 3/7 → 7/7. Deployed `bin/simple` (seed, 2026-08-15) still
  predates the fix — needs a seed rebuild + redeploy to go green in CI.
- **wasm_e2e_spec.spl (0 passed / 4 failed)** — `semantic: function
  'CompileOptions' not found` (x3): the spec's constructor-call form for
  CompileOptions no longer resolves under the interpreter; all four examples die
  in setup before any wasm is emitted. **NOT the erased-receiver bug** (verified
  2026-08-16): identical 0/4 failure on both the pre-fix and post-fix seed —
  this is a separate defect in resolving the imported `CompileOptions`
  constructor-call form (`use compiler.backend.backend.backend_types.{...,
  CompileOptions, ...}` then `CompileOptions(field: ...)`), still open.

## Unblock conditions

- Interpreter items 1–8: implement the missing behaviour in
  `src/compiler/10.frontend/core/interpreter/` (each spec names the exact
  assertion); specs stay RED per testing.md — do not weaken.
- Backend: fix erased-receiver builder-chain resolution (unblocks llvm_e2e,
  llvm_parity, likely wasm_e2e's `CompileOptions`); add
  `rt_process_run_capture` extern binding for the test interpreter; VHDL array
  combinational-local support is a genuine backend feature gap.

## advanced_types_spec.spl — per-example diagnosis (2026-08-16 follow-up)

Individual rerun (`SIMPLE_TIMEOUT_SECONDS=600 bin/simple test
test/02_integration/compiler/advanced_types_spec.spl`) gives
`Results: 12 total, 2 passed, 10 failed`. The earlier sweep note said "child
exits 1, no detail"; the real per-example evidence is now captured. All 10
failures share ONE root cause, and none are stale specs — no spec edits made.

Root cause: the spec imports `compiler.driver.driver_api_compile_single`
(`check_file` / `compile_files` / `compile_to_smf`), which under the test
interpreter resolves to the **lightweight external facade**
(`src/compiler/80.driver/driver_public_compile_process.spl`). That facade does
no in-process type check — it delegates every op to an external `simple` CLI
via `find_simple_binary()` + `rt_process_run`. Inside `bin/simple test` the
delegation guard (`driver_public_shared.spl:597-613`,
`check_compile_delegation_guard`) fires — either the
`SIMPLE_COMPILE_DELEGATED` marker inherited from the runner chain or the
same-binary-path check (child binary IS `bin/release/.../simple`) — so every
call returns `CompileResult.RuntimeError("compile delegation loop detected:
external fallback resolves to this same CLI; ... not supported in-process")`.

Per-example outcomes:

- `rejects recursive value layouts ...` — FAIL: `check_file` returns the guard
  RuntimeError, so `direct.is_success()` is false but the error text is the
  guard message, and the `reference`/`array` accept-cases assert
  `is_success()==true` → `expected false to equal true`.
- `rejects a recursive value layout split across imported modules` — FAIL:
  `compile_files([left, right], Check)` hits the facade's hard limit at
  `driver_public_compile_process.spl:42`: `lightweight external compile_files
  only supports a single input path`. Structurally impossible on this facade
  regardless of the guard.
- 6 accept/compile examples (union check+smf, try-operator check+smf, SIMD
  check+smf) — FAIL `expected false to equal true`: guard RuntimeError.
- `rejects intersection/refinement ... with a concrete parser error` (x2) —
  FAIL: rejection happens, but error text is the guard message, not
  `Ampersand`/`Where`.
- The 2 PASSING examples (`does not emit an artifact ...` x2) are **vacuously
  green**: they only assert failure + no artifact, which the guard error also
  satisfies.

Unblock condition: give the facade a real in-process Check/Aot path when
running under the test interpreter (or route `driver_api_compile_single` to the
full in-process driver instead of the external delegator), or run this spec in
an environment where `SIMPLE_BINARY` points at a genuinely different compiler
binary and the delegation marker is not inherited. Specs stay RED per
testing.md — assertions are correct and must not be weakened.

### ROOT CAUSE FOUND (2026-08-17) — a public-symbol collision, not a facade choice

The diagnosis above asked why the spec's `check_file` "resolves to" the
external facade even though it explicitly imports
`compiler.driver.driver_api_compile_single` — which is the genuine **in-process**
driver (`compiler_driver_create` / `compiler_driver_run_compile`, no subprocess
anywhere). It is not a resolution *preference*; it is a **duplicate-definition
collision**.

Six names were defined twice, with byte-identical signatures:

| name | in-process definition | external delegator definition |
|---|---|---|
| `compile_file`, `compile_files`, `compile_to_smf`, `jit_file`, `check_file`, `parse_sdn_file` | `driver_api_compile_single.spl` | `driver_public_compile_process.spl` |

Both were also publicly re-exported by two parallel aggregators —
`driver_api_core.spl` (in-process) and `driver_api.spl` -> `driver_public_compile.spl`
(external). Under co-compilation each name therefore had **two definitions**, and
the cross-module collision resolver dispatches an ambiguous call to the **last**
definition (the same mechanism behind the
`compiler_cross_module_private_symbol_collision` warnings, and the family
tracked in `cross_module_public_symbol_collisions_2026-08-16.md`). So the
explicit Tier-2 import silently landed on the delegator, which spawns the
resolved `simple` CLI — which under `bin/simple test` is the CLI already
running. Every call then re-entered `check_compile_delegation_guard`.

Two distinct symptoms came from this one cause:
1. **Deterministic guard errors** when the guard recognised the re-entry (the 10
   failures diagnosed above).
2. **A silent non-terminating run** when it did not: `find_simple_binary()`
   prefers `bin/release/simple`, which is a *shell wrapper* (`file` reports
   "Bourne-Again shell script") that execs `bin/release/<triple>/simple`. The
   guard's textual same-path test did not equate wrapper with target, so the
   facade spawned it and re-entered at a full CLI startup per hop, producing no
   error and no `Results:` line at all.

**Fix (landed):**
- `driver_public_compile_process.spl` now defines its entry points as
  `external_*`; `driver_public_compile.spl` aliases them back to the short
  public names, so the compatibility surface is unchanged and no name has two
  definitions. Dispatch is deterministic and Tier-2 importers reach the real
  in-process driver.
- `driver_public_shared.is_release_wrapper_self_delegation` teaches the guard
  the wrapper/target shape, so the un-guarded variant fails deterministically
  instead of spinning.

Regression + generalization coverage:
`test/01_unit/compiler/driver/compile_delegation_wrapper_loop_spec.spl`
(mirror-synced to `test/unit/...`) pins the wrapper shape, the
no-facade-shadows-the-driver invariant, and the alias surface —
`declared>=9 executed=9 passed=9 failed=0`, exit 0.

**Measured before/after** on `advanced_types_spec.spl`. Both runs use the same
worker the daemon spawns (`bin/simple run
src/app/test_runner_new/test_runner_single.spl <spec> --no-session-daemon
--sequential --timeout 1500`), same tree, same binary:

| | pre-fix | post-fix |
|---|---|---|
| verdict line | **none emitted** | `12 total, 4 passed, 8 failed` |
| examples executed | 0 (`executed=1 timeout=1`) | 12 |
| exit | 143 (SIGTERM at the 1500s outer timeout) | 1 |
| `compile delegation loop detected` occurrences | every check/compile call | **0** |

So the loop is gone and all 12 examples now execute against the real
in-process compiler. Vacuous greens are gone too: the two examples that used to
"pass" only because the guard error also satisfied "fails and emits no
artifact" now assert against real behaviour.

**Residual 8 failures are a different, genuine defect set** — real compiler
diagnostics, no guard text — and stay RED per testing.md:
- mutual recursive value layout reports only one side (`expected  to contain
  Right`), both for the single-file and the cross-module case;
- the in-process `check` REJECTS programs the spec expects to accept: union
  with payloads + pattern matching, and `vec[4, f32]` SIMD signatures (check
  and smf variants, 4 examples);
- parser rejects intersection `&` / refinement `where` correctly but spells the
  token differently than the asserted `Ampersand` / `Where`.

Note the daemon path still caps a worker at a hard **120s** budget regardless of
`SIMPLE_TIMEOUT_SECONDS` / `--timeout` (observed `budget_ms=119955`), so plain
`bin/simple test <this spec>` reports `daemon-worker-timeout` rather than the
verdict above — a separate harness limitation, not a delegation problem.

---

## mdsoc cluster (`test/01_unit/compiler/mdsoc/`) — 2026-08-16

Sweep baseline: 285/324 passing; three failing spec files. Two were stale specs
(now ported and GREEN), one is a genuine RED pin against a never-implemented
module. Two substantive compiler/language defects surfaced and are filed below.

### DEFECT 1 (compiler, filed) — a `use pkg.Mod.{Sym}` import where the module basename equals the imported symbol resolves to the MODULE NAMESPACE, not the symbol

`transform_adapters_spec.spl` failed 32/67 with, e.g.:

```
semantic: method `empty` not found on type `dict`
  (receiver value: {MirProgram: <constructor:MirProgram>, MirProgram__empty: <fn:MirProgram__empty>})
```

The receiver is the module's namespace dict. The struct's *constructor* call
`MirProgram(...)` still works (the dict carries the constructor), so only
`static fn` calls fail — which is why 35 examples passed and every static
factory (`MirProgram.empty`, `TokenStreamView.from_lexer_output`, …) failed.

Affected import shape: `use <pkg>.<Name>.{<Name>}` where the file
`<Name>.spl` defines struct `<Name>`. In this spec that is MirProgram,
MirDebugInfo, TokenStreamView, MirOptView, ObjectFileView, LoadedModuleView.
Imports where the module basename differs from the symbol
(`TypedAstView.{TypedAstContext}`, `HirView.{CfgContext}`) were unaffected.

Not reproducible with a single such import in a one-example spec (verified
GREEN in isolation) — it needs the module co-compiled alongside its siblings /
package `__init__`, so the shadowing comes from namespace merging, not from the
single import alone.

Workaround applied to the spec (intent preserved, no assertion weakened):
import through the package re-export instead —
`use compiler.mdsoc.transform.feature.mir_to_backend.entity_view.{MirProgram}`.
Every `entity_view/__init__.spl` already `export`s the symbol.

Note also `.../mir_to_backend/entity_view/MirView.spl` still imports via the
pre-rename path `compiler.transform.feature....` (missing the `mdsoc` segment)
and its `__init__.spl` exports `MirProgram`/`MirDebugInfo` twice.

### DEFECT 2 (language, filed) — binding `.?` to a `val` yields the PAYLOAD, not a bool

`layer_checker_spec.spl` failed 6/43, all with the same shape:

```
val is_denied = violation.?          # violation: LayerViolation?
expect(is_denied).to_equal(true)
# expected LayerViolation(message: layer 'infra' (level 3) cannot depend on ...) to equal true
```

The `LayerChecker` implementation is correct — it *did* produce the violation.
Only the assertion is wrong-typed: `.?` in a `val` binding evaluates to the
unwrapped payload, while the same `.?` in a condition (`if violation.?`) and in
a comparison (`if grant_opt.? == false`, `layer_checker.spl:169`) behaves as a
bool. That inconsistency is the defect; it silently converts a presence check
into a payload binding.

Spec ported to the type-correct form of the same intent:
`expect(violation).to_not_be_nil()` (6 sites, incl. one on `v2`).

### GENUINE RED (left in place) — `compiler.mdsoc.feature.cache.cache_port` does not exist

`pipeline_integration_spec.spl` (13 passed, 1 failed):
`error: semantic: Cannot resolve module: compiler.mdsoc.feature.cache.cache_port`.

`grep -rl "cache_port\|CachePort" src/ doc/` finds **zero** source hits — no
`src/compiler/85.mdsoc/feature/cache/` directory exists at all, and no such
module was ever deleted. The sibling ports it is modelled on do exist
(`feature/metrics/metrics_port.spl`, `feature/events/ports.spl`), so the spec's
Phase-5 `CachePort` block is a contract for an unimplemented port, not a stale
path. Already tracked as row 3 of
`doc/08_tracking/bug/spec_imports_declared_nowhere_2026-08-04.md`.

Left RED per `.claude/rules/testing.md` — the assertions are correct and must
not be weakened. Unblock condition: implement
`src/compiler/85.mdsoc/feature/cache/cache_port.spl` exposing `CachePort`
(fields `name`, `check_fn`, `store_fn`, `invalidate_fn`, `get_stats_fn`),
`CacheCheckStatus` (`is_fresh`), `CacheStats`
(`hits`/`misses`/`stores`/`invalidations`) and `create_noop_cache_port()`,
mirroring `metrics_port.spl`.

### Progress note 2026-08-17

- `transform_adapters_spec.spl` was found back at 32/67 red in this worktree —
  the DEFECT-1 workaround described above was NOT present in the file (direct
  `entity_view.<Name>.{<Name>}` imports still in place; likely clobbered or
  never landed here). Re-applied the package re-export import form (with an
  explanatory NOTE comment): now **67/67 GREEN**. Mirror
  `test/unit/compiler/mdsoc/transform_adapters_spec.spl` synced.
- Fixed the adjacent stale-path defect: `entity_view/MirView.spl` imported via
  the pre-rename `compiler.transform.feature....` path (missing `mdsoc`
  segment) — corrected to `compiler.mdsoc.transform.feature....`; and removed
  the duplicate `export MirProgram, MirDebugInfo` line from
  `entity_view/__init__.spl`.
- Interpreter items 1-8 and the seed-side fixes (erased-receiver dispatch,
  `rt_process_run_capture`, wasm `CompileOptions`) remain blocked on a seed
  rebuild/redeploy, which is prohibited while the current bootstrap runs —
  unchanged, still RED as filed.

### Adjacent observation (not fixed)

`BypassGrant` / `BypassUsage` are defined **twice, identically**, in
`src/compiler/85.mdsoc/types/bypass_grant.spl` (+`bypass_usage.spl`) and in
`src/compiler/85.mdsoc/mdsoc/types.spl:425+`. Not the cause of the failures
above (verified — the impl behaves correctly), but it is exactly the co-compiled
class-collision shape the compiler warns about elsewhere.
