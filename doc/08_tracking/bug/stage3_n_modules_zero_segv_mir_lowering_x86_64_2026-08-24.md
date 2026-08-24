# Stage 3 self-host: parse yields `n_modules=0` after 692 modules, SEGV at MIR lowering (x86_64-linux, 2026-08-24)

Cross-platform companion to the arm64 report
`stage3_monomorphize_segv_at_origin_main_arm64_2026-08-24.md` (present at
`origin/main`; not in this working tree at time of writing).
## CONFIRMED on x86_64-unknown-linux-gnu, at a HEAD that already carries the "reject Stage2 MIR loss" fix (2026-08-24)

Independent reproduction on a different platform and a newer commit. Same root
condition — the module set is emptied between parse and lowering — but the crash
lands one phase LATER than the arm64 report, which is consistent with an empty
program flowing further down the pipeline rather than with two separate bugs.

### Lane

Private, uncontended `git worktree --detach` at `e0bbc91a8f53c77e888a872aaba416303b97df9d`,
created solely for this run. `git status --porcelain` was **0 entries** before the
run, after Stage 2, after receipt validation, and after the crash — so nothing
mutated the tree mid-build. (This matters: an earlier attempt in a shared
worktree was invalidated by concurrent edits and its evidence deleted; see
`goal_r8_stage3_runtime_authority_snapshot_deleted_midrun_2026-08-24.md`.)

`git merge-base --is-ancestor 7a60b69c014 HEAD` returns **0** — the tree already
contains `fix(bootstrap): reject Stage2 MIR loss`. That fix does not prevent this.

### Commands

```
bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 \
    --backend=cranelift --mode=dynload --jobs=full --output=build/bootstrap/solo1
  -> "Stage 2 admitted; stopping before Stage 3 as requested."

bootstrap-from-scratch.sh planner-admission-v2 --target=//bootstrap:stage4 \
    --reason=self-host-convergence-check --parent-compiler=<solo1 stage2> \
    --bootstrap-output=<abs>/build/bootstrap/solo1 --out=<abs>/solo1/stage4-admission.env
  -> bootstrap-admission: produced .../solo1/stage4-admission.env   (MINT_RC=0)
  -> bootstrap-policy: receipt-valid target=//bootstrap:stage4 \
       reason=self-host-convergence-check execution=not-attempted   (VALIDATE_RC=0)

# full run, no --stop-after, no --resume
bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --backend=cranelift \
    --mode=dynload --jobs=full --output=build/bootstrap/solo1 --bootstrap-receipt=<receipt>
```

### Outcome

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
Segmentation fault (core dumped)
  warning: stage3 self-host was KILLED by signal 11 (SEGV), not a compile failure; Stage 4 unavailable
  Stage 2 native-build capability passed
Stage 3 unavailable — no provenance-verified compiler for Stage 4
```

### The module set is emptied, exactly as in the arm64 report

`stage3-native-build.log` (367,053 bytes, survived this time) shows **692**
`phase2:surface:file:released` lines — every module parsed, surfaced, promoted,
committed and released — and then:

```
[BOOTSTRAP-PHASE] +353509ms phase2:parse:done n_modules=0
[build] parse 0/0 step 2/6 +353509ms dt=350009ms complete
[BOOTSTRAP-PHASE] +353510ms phase3:hir_typecheck:start
[BOOTSTRAP-PHASE] +353510ms phase3:hir_typecheck:done
[build] hir unknown/unknown step 3/6 +353510ms dt=1ms complete
[mono] generic_fns=0 call_sites=0 specializations=0 unresolved=0
[BOOTSTRAP-PHASE] +353510ms phase5:mode_dispatch:start
[build] mir 0/0 step 4/6 +353510ms dt=0ms lower_to_mir
[BOOTSTRAP-PHASE] +353510ms aot:lower_to_mir:start
[mir-lower-free] start        <-- last line written; SEGV here
```

692 files released, `n_modules=0`. Type-check then "completes" in **1 ms** and
monomorphize reports `0/0` — both vacuous on an empty module set. The process
dies at `[mir-lower-free] start`, i.e. MIR lowering is the first phase that
actually dereferences the (empty/freed) module state instead of no-op'ing over it.

Difference from the arm64 report: there the SEGV was at `phase4:monomorphize`;
here monomorphize survives with `0/0` and the SEGV is at `aot:lower_to_mir`.
The shared, load-bearing fact on both platforms is `n_modules=0` after a parse
phase that demonstrably processed every file.

### Consequence

Stage 4 is unreachable on x86_64-linux at this commit, so there is no
self-hosted artifact to deploy. The 350 s spent in parse is real work whose
entire result is discarded.

### Note on the phase timing

`dt=350009ms` for parse vs `dt=1ms` for the whole of HIR type-check is itself a
signal: the work happened, the result did not survive the phase boundary.
Whatever releases/frees the per-file surface state (`phase2:surface:file:released`)
is the place to look — the crash marker is literally `[mir-lower-free]`.

## Second finding: re-invocation fails at Stage 3 with NO diagnostic

The run above was repeated verbatim (same receipt, same flags, same lane) to
capture the wrapper's true exit status, which the first attempt had not recorded.
The repeat did NOT reproduce the SEGV. It produced a different, worse outcome:

```
Stage 2: seed -> bootstrap_main.spl
  Stage 2: running bootstrap compiler sanity
  Stage 2: proving struct receiver/runtime capability
preserved: .../phase_snapshots/phase1_1787579614_phase2_1787579768/simple
Stage 3: stage2 -> bootstrap_main.spl (self-host)
REAL_BOOTSTRAP_RC=1
```

That is the entire tail of the log (1,216 bytes total, stdout+stderr merged).
Stage 3 announces itself and the wrapper exits 1 with **no typed error, no
warning, and no evidence path** — the operator is told only that something
failed. File mtimes prove Stage 3 never got as far as its own log:

```
stage3-native-build.log  367053  13:50:47   <- still run 1's; NOT rewritten
stage2-native-build.log     845  13:55:21   <- rerun did rebuild Stage 2
```

So the second invocation aborts between "Stage 3: ..." being printed and the
native build starting. This is the same defect class already tracked in
`simpleos_stage2_bootstrap_sanity_exit2_without_diagnostic_2026-08-20.md`
(non-zero exit with no diagnostic => UNDIAGNOSABLE), one stage later. A guard
that refuses without naming what it refused is not diagnosable, and here it
masks the far more interesting `n_modules=0` crash underneath.

Plausible but UNVERIFIED cause: the receipt pins `parent_compiler_sha256`, and
the rerun rebuilt Stage 2 first, so the pinned parent no longer exists byte-wise.
If that is the refusal, it needs to say so.

## Exit statuses — what is and is not established

* Repeat run: `REAL_BOOTSTRAP_RC=1`, captured directly into a variable on the
  line after the command. Established.
* First run (the one that SEGV'd, printed `Stage 3 unavailable ...` and then
  `Pure-Simple dynload build complete; full CLI relink skipped.`): **exit status
  UNKNOWN.** It was launched with `nohup ... &` and only waited on by PID, so the
  `[exited with code 0]` seen in the harness was the *watcher's* status (a
  `tail`), never the bootstrap's. It is NOT evidence that the wrapper fails open
  on the SEGV path, and must not be cited as such. Establishing it requires a
  fresh run of that same path with `RC=$?` captured directly.

## Net effect

Stage 4 was not produced on either attempt, so there is no self-hosted artifact
to deploy, and the MCP `tools/call simple_info` probe still executes the Rust
seed and still returns `exit: 1` with "this Rust-built Simple binary is a
bootstrap seed only". That probe cannot turn green until Stage 3 self-host does.

---

## ROOT CAUSE FOUND — fix `af74374c355` (2026-08-24)

### `n_modules=0` was never the defect

It is **correct by design** on this path. Phase 2's streaming-surface path ends
with (`driver_source_pipeline_parsing.spl`):

```
self.ctx.module_surfaces = Some(retained_surfaces)
self.ctx.modules = {}
```

On the streaming path the **surfaces ARE the module set**; `ctx.modules` is
deliberately emptied. `phase2:parse:done` read `ctx.modules` unconditionally and
so printed a bare `n_modules=0` after a fully successful 692-module parse. That
line reads as catastrophic loss and misdirected this investigation to the wrong
field. It now names its carrier.

Streaming was confirmed active: `bootstrap-from-scratch.sh` exports
`SIMPLE_STAGE3_STREAMING_SURFACES=1` for Stage 3, and the 692
`phase2:surface:file:released` lines are emitted only by the streaming path
(`log_module_surface_released`, `driver_log_helpers.spl:177`).

### The actual defect: phase 3 dispatched on a lost readiness flag

`driver_hir_pipeline_lowering.spl`, `lower_and_check_impl`:

```
if self.streaming_surface_owner_ready:          # <-- the mutable scalar, ALONE
    return self.lower_and_check_streaming_surfaces_impl()
```

Phase 2 sets `streaming_surface_owner_ready = true`. Under native value
semantics that boolean was **lost across the phase boundary**, so this test read
false and fell into the **legacy** path — which iterates `ctx.modules`, the
collection phase 2 had just deliberately emptied. Result: zero iterations, phase
3 "completes" in 1 ms, returns SUCCESS with zero HIR modules.

The empty program then flows on: monomorphize reports `0/0` (vacuous), and MIR
lowering is simply the first phase that DEREFERENCES rather than iterating —
`_bootstrap_entry_hir_module` is nil, `.?` enters the Some arm anyway (the
predicate-misread class of `c018ee15926`, where `is_empty()` returns false on an
empty list in Stage-2-compiled code), and `hir_module.symbols` SEGVs.
**The crash site was three phases downstream of the defect site.**

### Proven from the existing log — no new run required

From the 367 KB `stage3-native-build.log` of the original failing run:

- `grep -c 'phase=hir'` → **0**. The streaming impl's pre-loop
  `log_build_progress("hir", "modules", 0, surfaces.surfaces.len(), "pending", …)`
  **never printed**.
- `grep -c FAILED` → **0**, and phase 3 returned true in 1 ms.
- The streaming impl has **no success path before that log line** — every exit
  above it is `return (self.ctx, false)` with a recorded error.

Therefore the streaming impl was **never entered**, while the 692
`surface:file:released` lines prove phase 2 *did* take the streaming path. The
two halves of the pipeline disagreed about the mode. That is the seam.

Corroboration: `phase1:load_sources:done n_sources=968` — the sources were all
there; `phase2:source_reclaim` and `[parse-shard]` are both absent, excluding
eviction and shard-exit as alternative mechanisms.

### Fix (minimal, semantics-preserving)

`driver_orchestration` already derived *its* phase-3 routing from stable
configuration for exactly this reason — *"not the adjacent mutable readiness
boolean that native value semantics can lose between phase methods"*. This
dispatch was the one place still trusting the boolean.

1. **Route on both** — `streaming_ready_flag or streaming_config_gate`.
   Configuration rescues a lost flag; the flag serves compat callers that stage
   surfaces without the env gates.
2. **Legacy path fails closed** — `E-DRV-PHASE3-EMPTY`: 0 modules from >0
   sources aborts.
3. **Streaming path fails closed** — `E-DRV-PHASE3-EMPTY-SURFACES`.
4. **MIR entry fails closed** — `E-MIR-BOOTSTRAP-ENTRY-NIL` explicitly
   nil-checks the payload instead of trusting `.?`, turning the SEGV into a
   named error.
5. `phase2:parse:done` now reports `carrier=surfaces|modules`.

A zero-module parse result can no longer flow into a later phase on any path.

### Regression gate

`scripts/check/check-phase3-empty-module-abort.shs` — `--selftest` first and
fatal (4 fixtures: clean, incident-replay, partial-regression, empty-tree);
verdict last on stdout. Validated against reality:

```
# at origin/main (the broken tree)
FAIL — 4 invariant(s) checked in <tree>, violated: phase3-dispatch-routes-on-mutable-flag-alone \
  legacy-phase3-missing-zero-module-abort streaming-phase3-missing-zero-surface-abort \
  mir-bootstrap-entry-missing-nil-check

# at af74374c355 (fixed)
PASS — 4 invariant(s) checked, phase-3 zero-module abort intact (dispatch routes on config+flag; \
  legacy, streaming and MIR-entry paths all fail closed)
```

### Relationship to the arm64 report

One defect, not two. `stage3_monomorphize_segv_at_origin_main_arm64_2026-08-24.md`
describes the same empty-program condition ("clears HIR entirely"); after its own
monomorphize fault was fixed, that lane also proceeds to `aot:lower_to_mir` —
converging on exactly this x86_64 crash site.

### Status

**Root cause identified, fixed and landed at `af74374c355`; regression gate green.**
End-to-end Stage 3 / Stage 4 artifact verification is a separate long bootstrap
run and is recorded below when complete. Note that even absent that run, the
change is a strict improvement: the silent SEGV is now a named, fail-closed
error on every path.
