# Stage4 Self-Host Redeploy (#79) — Corrected Plan (2026-07-09)

Supersedes `redeploy_stage4_plan_2026-07-08.md` (that doc's "string-literal
drop" wall is **fixed** — see #128 below). This one records the *actual*
redeploy pipeline (the prior plan chased a proxy path) and the two remaining
concrete blockers, with IR evidence.

## What the real pipeline is (was mis-identified before)

`scripts/bootstrap/bootstrap-from-scratch.sh` (reuse-seed default, no cargo)
runs the **manual staged** bootstrap (`can_full_bootstrap=0`), exporting
`SIMPLE_BOOTSTRAP=1` globally, then:

- **Stage 2**: `seed native-build --backend cranelift --entry-closure --mode
  <mode> --entry src/app/cli/bootstrap_main.spl`. **Key gotcha:**
  `SIMPLE_BOOTSTRAP=1` forces the driver's real-LLVM bootstrap emit path
  (`driver_bootstrap.spl` `bootstrap_emit_real_llvm_object`, `[llvm-direct]` +
  external `llc`), **overriding `--backend cranelift`**. And the
  `bootstrap_lower_hir_globals_to_mir_module` path lowers **only the 6 entry
  functions** of `bootstrap_main.spl` (`bootstrap_version`, `native_build_help`,
  `bootstrap_output_from_args`, `run_native_build_bootstrap`, `get_cli_args`,
  `main`), not the whole closure.
- **Stage 3**: stage2 recompiles bootstrap_main via `${backend}`. Both stages
  **tolerate failure** and fall back to the seed for stage 4.

**Proxy traps to avoid** (cost several build cycles): building `tiny_str.spl`
or bootstrap_main with `SIMPLE_BOOTSTRAP_REAL_LLVM=1` and *no* `--entry-closure`
exercises a different shape than stage 2. The **deployed-binary routes are
closed**: the deployed `bin/simple` bakes in its own (buggy) backend — fixing
source can't fix it (circular); deployed+cranelift-AOT errors
`unknown extern rt_cranelift_new_aot_module` (AOT runtime unlinked, JIT-only).
So the **seed is the only from-source redeploy route.**

## Fixed this session (on origin/main)

- **#128** `fbd2fd7941a` — `lower_hir_block` had a stale `SIMPLE_BOOTSTRAP`
  branch returning `HirBlock(stmts:, value:, span:)` — omitting the desugared
  `has` field, which read `nil`, so MIR `lower_block` dropped every tail/
  implicit-return value (`bootstrap_version()` → `ret ptr null`, inert binary).
  Deleted the stub → hardened path sets `has`.
- **#130** `bfd98b0327f` — `lower_hir_expr` Call/MethodCall arms had a
  `SIMPLE_BOOTSTRAP` branch wiping the arg list to `[]` (from `050209d9b`
  "speed up bootstrap"). Every call lost all args. Restored the safe
  all-four-field `HirCallArg` loop.

Both are `SIMPLE_BOOTSTRAP`-gated (no normal-build impact) and are inherited by
the real stage-2 path.

## Remaining stage-2 blockers (IR evidence: `/tmp/simple_llvm_1765712.ll`)

`llc` fails; the two defects, in llc-report order:

1. **#131 — duplicate SSA name `%l2`** (`error: multiple definition of local
   value named 'l2'`). `bootstrap_output_from_args` is a 5-arm elif-ladder
   returning `text`; all arms merge at one join block → an **N-ary phi**. The
   SSA phi *detector* (`var_reassign_ssa.spl:506/535`) only matches a single-hop
   **2-way** diamond and `SsaPhiPlan` is **binary**, so it rejects → non-SSA MIR
   → backend emits the same `LocalId` twice. Phi *machinery* works
   (`aggregate_intrinsics.spl:179` emits real `phi`); only detection+plan-arity
   are incomplete. Shared with the general LLVM-AOT path
   (`core_codegen.spl:107/115`) — any 3+-arm elif returning a value miscompiles.
   **Miscompilation risk** — implement N-ary (or alloca-per-reassigned-local,
   mirroring cranelift's slot approach) + adversarially verify across CFG shapes.
2. **#133 — `nil` call-arg types** (`call ptr @bootstrap_output_from_args(nil
   %l0, nil %l40)` vs correct `define ptr @…(ptr %l1, i64 %l2)`).
   `translate_call` (`core_codegen.spl:811`) `lookup_function_param_type`
   returns `""` because the registry stored **empty** params: under
   `SIMPLE_BOOTSTRAP`, `declaration_lowering.spl:144` **skips param lowering**,
   so the MIR signature has no params. The *define* gets its `(ptr,i64)` from a
   different source (`translate_function:188-204`). Fix: derive call arg types
   from the callee's define param types (or align the registry with that
   source), or lower params under `SIMPLE_BOOTSTRAP` too (check why they were
   skipped — likely seed-safety).

`#132` (callee → `inttoptr undef`) was **tiny_str-proxy-only** — the stage-2 IR
calls `@bootstrap_output_from_args` directly. Closed.

## Next steps

1. Fix **#131** and **#133** (both general LLVM-text-backend codegen bugs; both
   must clear `llc`). Verify by re-running the real stage 2 and inspecting the
   emitted IR / that `llc` advances.
2. Re-run `scripts/bootstrap/bootstrap-from-scratch.sh` (reuse-seed); let the
   next failure define the next item. Note stage 4 seed-fallback is **slow**
   (30-min timeout compiling full `main.spl`) — a perf concern, not correctness.
3. Only after stage 2/3 self-host: full 3-stage + extended smoke matrix before
   any redeploy to `bin/release`.

## Infra facts banked

- **`eprint` is dropped** by the native-build worker (stderr not forwarded to
  the captured log) — trace bootstrap/HIR/MIR with `print`, never `eprint`.
  (When the *script* captures a stage log directly via `2>&1`, eprints do show.)
- Reproduce via `native-build` (not `simple run` — the session kill-monitor
  SIGKILLs exec-mode processes).

## Session update 2026-07-10 — #131 built, value-wall found (type tracking)

- **#131 dup-SSA: FIXED at IR/llc level.** With the N-ary phi + Call/Copy/Move
  SSA-rewrite change (git object `a487bb71bcdf`, SIMPLE_BOOTSTRAP-gated), stage 2
  now **builds** (exit 0, 122MB binary) where it previously failed at `llc`.
  opus review: "correct for its literal target". NOT pushed (see below).
- **But the stage-2 binary is value-INCORRECT** (verified by running it): every
  `argc==2` arm collapses to the version arm. Two defects, both **pre-existing
  properties of the partial 6-fn SIMPLE_BOOTSTRAP real-LLVM path**, not #131
  regressions:
  1. **#135 guard-collapse** — guards mixing a method-call (`.len()`/
     `.starts_with`) with `and` all evaluate always-true. IR shows the branch
     cond is `add i64 %X, undef` → the second operand (a value defined in a
     later-emitted block, i.e. a short-circuit-`and` / nested if-EXPRESSION arm)
     is emitted as `undef` because the backend only names a local after its
     defining block is seen. Plain int compares (`argc < 2`) work.
  2. **#136 interpolation** — `{bootstrap_version()}` emitted verbatim.
- **ROOT CAUSE (confirmed 3×): the SIMPLE_BOOTSTRAP LLVM backend does not track
  local types.** Copies lower to `add i64 X, 0 ; copy` (always i64); guards/
  forward-refs fall back to `undef`; call args fall back to `nil`/`native_int`.
  #134, #135, #136 are all symptoms of this one gap.
- **Piecemeal undef-patching REGRESSES the build.** A "defined-anywhere" pre-pass
  that emits the real `%lN` for forward-refs (instead of `undef`) made `llc`
  reject: `instruction forward referenced with type 'ptr'` — `%l54 = add i64
  %l58, 0 ; copy` defines i64 but is consumed as `ptr`. The type-lossy copy
  lowering surfaces the moment undef stops masking it. Attempt saved:
  `scratchpad/attempt_135_undef_forwardref.patch`.
- **Correct next step = architectural, not piecemeal:** give this backend real
  per-local type tracking (derive each local's type from its defining
  instruction, thread it through copy/phi/call/guard emission) — OR route the 6
  bootstrap_main fns through the normal typed MIR→LLVM lowering instead of the
  "fast" untyped path. Then #134/#135/#136 fall together. Verify by RUNNING the
  arms (3 distinct correct outputs), never llc-accept alone.

### DIAGNOSIS CONFIRMED — the fast path can't hand-build SSA (pivot to alloca)

Type-tracking attempt (`scratchpad/attempt_135b_typetrack.patch`) built but llc
still rejected: `use of undefined value '%l21'` + residual `inttoptr i64 undef to
ptr` phi arms + copies still `add i64 X,0`. Three attempts each just RELOCATED the
invalid SSA (dup-name → undef operand → dangling `%l21`). **Root mechanism: the
fast path builds SSA phis BY HAND** (`var_reassign_ssa` detects joins →
`__simple_ssa_phi` → `aggregate_intrinsics` emits `phi`), and hand-construction
cannot resolve incoming-value-per-predecessor for real control flow (short-circuit
`and`, nested if-EXPRESSIONS). Type-tracking was necessary but can't fix a
value-flow/dominance defect.

**PIVOT (advisor-endorsed): alloca-per-reassigned-local** — the cranelift-slot
approach. For every reassigned local: one `alloca` in the ENTRY block (dominates
all uses → the undef/dangling class is structurally impossible), `store` on each
reassignment, `load` before each use. No phi, no dominance reasoning; correct at
`llc -O0` (exactly what `clang -O0` emits). Keeps the fast path; reuses the
type-tracking (for slot element types); the N-ary phi code becomes dead. The
"why does the fast path exist" question is moot — `050209d9b` was a SPEED hack,
and speed is irrelevant for 6 functions; correctness wins outright.

**Ops rule learned:** the 3 subagent deaths were all the API stalling at the
build transition. **Delegate EDITS to subagents; run BUILDS yourself** via
detached Bash (`SIMPLE_BOOTSTRAP=1 seed native-build … -o …stage2/…/simple`),
then grep IR + RUN the binary's arms.

### Method-resolution is a project-wide DEAD STUB (not a cheap re-enable)

Investigated whether the bootstrap method-drop class could be killed by
re-enabling a skipped resolution pass. NO: `resolve_methods()`
(`src/compiler/35.semantics/resolve.spl:731`) is stubbed project-wide — it builds
an EMPTY `SymbolTable` (`resolve.spl:743`, deliberate "Phase 9 follow-up" stub),
so `try_instance_method`/`try_trait_method`/`try_ufcs` always return nil. Every
`HirExprKind.MethodCall` starts `MethodResolution.Unresolved` in BOTH normal
(`expressions.spl:379`) and bootstrap (`module_lowering.spl:578`
`lower_bootstrap_flat_expr`) lowering, and the default driver branch
(`driver.spl:601-723`) never calls `resolve_methods` at all. Un-stubbing =
pipeline-wide, multi-step, unverified-at-scale (build populated SymbolTable + wire
into default driver + bootstrap `module_lowering.spl:578` sets receiver
`type_: HirType.Infer(0,0)` so has no type to resolve against). NOT bootstrap-
scoped. So the method-drop tail must be handled in the MIR-lowering
`Unresolved` arm (`method_calls_literals.spl` `lower_method_call`), either via
per-method special-cases (done: `len`, `substring`/`slice`, `starts_with`) if the
remaining set is small, or ONE generic UFCS-style emission
(`method_name(receiver, args…)` → linkable rt_/free-fn) to cover all at once.
Decide via the 6-fn construct enumeration.

### ALLOCA IMPLEMENTED & WORKING (reassigned-local class fixed)

`ssa_alloca_transform_blocks` in `var_reassign_ssa.spl` (gated in
`core_codegen.spl` `llvm_bootstrap_ssa_function` + `driver_bootstrap.spl`):
every reassigned local → one entry `alloca` + `store` per def + `load` per use.
**`bootstrap_output_from_args` IR is now fully correct: 5 alloca / 5 load / 10
store, ZERO undef / phi / inttoptr.** The whole dup-SSA (#131) + undef-phi
(#135 in that fn) class is structurally eliminated. Working patch:
`scratchpad/alloca_working.patch` (807 lines).

Bugs fixed en route (all seed-interpreter quirks, positive-form rule):
- `val new_src = match X.kind:` mis-lowered by the seed → converted 4 sites to
  `if val Copy(local) = …:` form.
- `ssa_alloca_apply_def_store` used `if not written.?:` — **negated `.?` on a
  struct-boxed optional mis-evaluates in the seed interpreter**, so it
  early-returned on EVERY def (5 alloca, 5 load, 0 store). Positive-form fix.

### REMAINING BLOCKER: short-circuit `and` drops its 2nd operand

`__simple_main` still fails llc: `use of undefined value '%l24'` at
`%l25 = add nsw i64 %0, %l24`. The `and`-guards `first.len()==N and
first.starts_with(S)` lower as `(a_i64 + b_i64) != 0`, where the SECOND operand
(`.starts_with` result: l24/l34/l54/l62) is **NEVER DEFINED** — a phantom
reference. This is NOT an alloca/SSA issue (nothing to slot — the def is
missing); it's a HIR→MIR/backend `and`-lowering bug: `b`'s computation
(the `.starts_with` icmp) isn't emitted, or is emitted in a later/conditional
block while the fused `add %0,%b` references it earlier. ALSO note `(a+b)!=0` is
OR-semantics, not AND — the boolean-`and` lowering itself is wrong. Correct fix:
lower `a and b` as proper short-circuit control flow (or `and i1`), ensuring `b`
is materialized and dominance holds. Distinct next task; the alloca work stands.
- **VCS note:** parallel sessions force-push `main` continuously; my local #131
  commit got squash/rebase-conflicted. Left the 3 backend files at origin
  content (WC buildable); #131 stays recoverable from git `a487bb71bcdf`. A clean
  reland should use an isolated worktree on origin tip (per the file-level-reland
  rule), rebuild+value-check, and only push once value-correct.

## Current status 2026-07-10 — WIP committed, redeploy blocked

- Core-C environment/process ABI fixes and the Stage 3 duplicate-LLVM-
  constructor fix are implemented. A prior cached Stage 2/3/4 run completed and
  the Stage 3 binary passed `--version`.
- The required clean-cache rerun does **not** pass Stage 2. Preserved IR
  `/tmp/simple_llvm_3014324.ll:215` defines `%l54` as `i64`, while a predecessor
  phi consumes `%l54` as `ptr`; LLVM rejects it with `instruction forward
  referenced with type 'ptr'`. This is the local-type/value-flow blocker
  described above, now reproduced on the real bootstrap path.
- Concurrent worktrees exposed fixed `/tmp/simple_rt_<name>.o` runtime object
  names. Runtime object paths now include the compiler PID so one bootstrap
  cannot delete another bootstrap's link inputs.
- The extended redeploy gate did not pass and **no release binary was
  deployed**. The next session must fix typed Copy/Move/phi emission, rerun the
  clean-cache Stage 2/3 pipeline once, then run the extended smoke matrix before
  deployment.
