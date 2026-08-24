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
