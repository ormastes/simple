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

## INVESTIGATION 2026-08-24 — defect localized to ~30 lines; two theories REFUTED by measurement

Still OPEN. Stage 3 still SEGVs. What follows is measured, not reasoned, and it
retires two wrong explanations (including one this record previously asserted).

### REFUTED #1 — `n_modules=0` is not the defect

It is **correct by design**. Phase 2's streaming path ends with
`self.ctx.module_surfaces = Some(retained_surfaces)` / `self.ctx.modules = {}`
(`driver_source_pipeline_parsing.spl`): on that path the **surfaces ARE the
module set**. `phase2:parse:done` read `ctx.modules` unconditionally, so a fully
successful 692-module parse printed a bare `n_modules=0`. The line now names its
carrier (`carrier=surfaces`). Anyone chasing "the 692 modules are lost between
release and parse:done" is chasing a logging artifact.

### REFUTED #2 — the readiness flag is NOT lost, and phase 3 routes correctly

A previous revision of this record claimed the phase-3 dispatch fell into the
legacy path because `streaming_surface_owner_ready` was lost across the phase
boundary. **That is false.** Instrumented Stage 3 prints:

```
[BOOTSTRAP-PHASE] +348192ms phase3:route ready=true config=true n_modules=0 n_sources=968
[BOOTSTRAP-PHASE] +348192ms phase3:streaming:entry
```

`ready=true` — the flag survives, and the streaming impl **is** entered.

That claim rested on "the streaming impl's pre-loop `log_build_progress("hir",…)`
never appears in the stage3 log". **That reasoning was invalid**:
`log_build_progress` ends in `file_append`, so it never goes to that log at all.
A guard against repeating this: `log_phase` → stderr, `log_build_progress` →
`bootstrap-build-progress.events`. Do not use the absence of one to reason about
the other.

### MEASURED — where it actually goes wrong

`lower_and_check_streaming_surfaces_impl` is entered and then **returns success
from the middle of the method without executing any return statement**:

| probe (all UNCONDITIONAL `log_phase`, so they cannot be mis-branched) | result |
|---|---|
| `phase3:streaming:entry` (first line of the impl)                    | **printed** |
| `phase3:streaming:visit` (after `hir_visit_order` is computed)        | **never printed** |
| `phase3:legacy:entry`                                                 | never printed |
| any recorded error                                                    | **zero** |
| phase 3 verdict                                                       | **true**, in ~0 ms over 692 surfaces |

Execution then continues normally — `phase3:hir_typecheck:done`, `[mono]
generic_fns=0 call_sites=0`, `aot:lower_to_mir:start`, SEGV at
`[mir-lower-free] start`.

**Every `return` between those two probes is `return (self.ctx, false)` and every
one is immediately preceded by `add_error`.** Zero errors were recorded and the
verdict was `true`, so none of them ran. The method's only `(self.ctx, true)` is
at the very end, after a teardown that emits
`phase3:streaming_source_reclaim:done` and `hir_reclaim` events — **both absent
from this run**.

So the defect is bracketed to roughly 30 lines, between the entry probe and the
visit-order computation: owner unwrap, `rt_heap_ref_wellformed` inside an
`unsafe(capabilities: [ffi])` block, `hirlowering_for_module`,
`bootstrap_hir_modules_reset`, `hir_cache_enabled`/`hir_cache_closure_digest`,
`hir_shard_active`/`hir_shard_levels`.

### Assessment

This is **not a driver-logic defect** — no driver logic can return `true` from
the middle of that method. It is a **control-flow miscompilation in
Stage-2-compiled code**, the same family as `c018ee15926` ("`is_empty()` returns
FALSE on an empty list in Stage-2-compiled code"), where a predicate/branch in
the self-compiled compiler is lowered incorrectly. MIR lowering is merely the
first phase that DEREFERENCES the resulting empty program instead of iterating
zero times over it — **the crash site is three phases downstream of the defect
site**, which is why this was repeatedly misfiled as a MIR bug.

Fixing that codegen defect is out of scope for this record; it needs a
narrowed-down miscompilation reproducer, and `c018ee15926` is the existing
thread.

### Landed here (defensive; does not fix the SEGV)

- `af74374c355` — phase-3 dispatch routes on stable configuration as well as the
  readiness flag (defensive; measured to be a no-op for this bug), plus
  fail-closed aborts: `E-DRV-PHASE3-EMPTY` (legacy, 0 modules from >0 sources),
  `E-DRV-PHASE3-EMPTY-SURFACES` (streaming), `E-MIR-BOOTSTRAP-ENTRY-NIL`
  (explicit nil check instead of trusting `.?`).
- `0db03fbe7ac` — the `parse:done` carrier diagnostic must not dereference the
  retained surface owner. The first version did, and **SEGV'd in the diagnostic
  itself**: the log ended at `surface:file:released seq=692` with no
  `parse:done` line at all. A diagnostic must never be able to crash the compile
  it describes.
- `759ad1fd1c5` — the unconditional path receipts above, plus
  `E-DRV-PHASE3-EMPTY-VISIT`, which fails closed when the visit order is empty
  while surfaces are present. Deliberately conditioned on the **surfaces** (the
  carrier proven present), never on the owner arrays — a guard conditioned on
  the carrier it suspects is vacuous exactly when the bug fires.
- `scripts/check/check-phase3-empty-module-abort.shs` — 5-invariant ratchet,
  `--selftest` first and fatal, verdict last. Validated against reality: FAILs
  on the pre-fix tree naming all violations, PASSes after.

Note none of the new aborts fired in the failing run — consistent with the
assessment above, since a miscompiled branch skips guards too. They remain
correct and will catch the same *shape* of failure on any correctly-compiled
path.

### Verified evidence trail

Stage 2 admitted and a valid `//bootstrap:stage4` receipt were obtained (exit
codes read directly into variables, never through a pipe):

```
Stage 2 admitted; stopping before Stage 3 as requested.          STEP1_RC=0
bootstrap-admission: produced .../lane3/stage4-admission.env     STEP2_MINT_RC=0
bootstrap-policy: receipt-valid target=//bootstrap:stage4 reason=self-host-convergence-check execution=not-attempted   STEP3_VALIDATE_RC=0
```

The full run then reported, verbatim:

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
Segmentation fault (core dumped)
  warning: stage3 self-host was KILLED by signal 11 (SEGV), not a compile failure; Stage 4 unavailable
Stage 3 unavailable — no provenance-verified compiler for Stage 4
STEP4_FULLRUN_RC=2
```

**No Stage 4 artifact exists. Status: OPEN.**

### Next step for whoever picks this up

Do not re-diagnose from the MIR crash, and do not re-open the two refuted
theories. Bisect the ~30-line region with more unconditional `log_phase` receipts
(one between each call) to find the exact statement after which control escapes,
then reduce that statement to a standalone miscompilation fixture against
`c018ee15926`.

---

## MEASURED 2026-08-24 (second lane) — the ~30-line bracket narrows to SIX lines

Reproduced the failure end to end in a private worktree at `73331690322`
(`git status --porcelain` = 0 at creation; seed built in-lane), then re-ran
Stage 3 with **twelve additional unconditional `log_phase` receipts**, all
literal-string-only — no receipt dereferences a suspect owner, so the
2026-08-24 "diagnostic SEGV'd and moved the crash" failure is avoided by
construction.

### Harness defect that must be recorded, because it silently voids this experiment

`log_phase` is **gated**: `driver_phase_trace_enabled()`
(`src/compiler/80.driver/driver_log_helpers.spl:25-26`) requires
`SIMPLE_COMPILER_PHASE_PROFILE=1` or `SIMPLE_COMPILER_TRACE=1`. A run launched
without it emits **no receipts at all**, including the pre-existing ones — and
"no receipts" reads exactly like "control never got there". The first attempt
here was launched without it and was discarded. Also: the stage-3 log lives at
`build/bootstrap/<out>/logs/<triple>/stage3-native-build.log`, not at
`<out>/stage3-native-build.log`.

### Result — faithful reproduction, and the escape point

```
[BOOTSTRAP-PHASE] phase3:route
[BOOTSTRAP-PHASE] phase3:streaming:entry
[BOOTSTRAP-PHASE] phase3:streaming:r01-unwrapped     <-- LAST receipt emitted
                  (r02 .. r12 and the pre-existing `visit` line: NONE)
[BOOTSTRAP-PHASE] phase3:hir_typecheck:done
[BOOTSTRAP-PHASE] phase4:monomorphize:start / :done
[BOOTSTRAP-PHASE] aot:lower_to_mir:start
[mir-lower-free] start
Segmentation fault (core dumped)
```

Verbatim wrapper verdict, exit status captured directly into a variable on the
line after the command (`STEP3_RC=2`; the receipt mint before it was
`STEP2_RC=0`):

```
Stage 3: stage2 → bootstrap_main.spl (self-host)
Segmentation fault (core dumped)
  warning: stage3 self-host was KILLED by signal 11 (SEGV), not a compile failure; Stage 4 unavailable
  Stage 2 native-build capability passed
Stage 3 unavailable — no provenance-verified compiler for Stage 4
```

**`r01-unwrapped` prints and `r02-wellformed` does not.** Those two receipts
bracket exactly six lines of
`driver_hir_pipeline_lowering.spl::lower_and_check_streaming_surfaces_impl`:

```
val surfaces = self.streaming_module_surfaces_owner.unwrap()
log_phase("phase3:streaming:r01-unwrapped")          # PRINTS
if surfaces == nil:
    self.ctx.add_error("Streaming module surface owner payload missing after phase 2")
    return (self.ctx, false)
unsafe(capabilities: [ffi]):
    if not rt_heap_ref_wellformed(surfaces):
        self.ctx.add_error("E-DRIVER-HIR-OWNER-MALFORMED: ...")
        return (self.ctx, false)
log_phase("phase3:streaming:r02-wellformed")         # NEVER PRINTS
```

So the record's ~30-line bracket is now **six lines**, and the two candidate
statements are named: the `if surfaces == nil:` guard and the
`unsafe(capabilities: [ffi])` / `rt_heap_ref_wellformed(surfaces)` guard.
Everything downstream — `hirlowering_for_module`, the `hir_cache_enabled`
if-expression, the shard block, `hir_shard_visit_order` — is **excluded**, since
none of their receipts fire.

Still consistent with the original evidence: zero errors recorded, phase-3
verdict `true`, and the empty program flowing on to SEGV at `[mir-lower-free]`.

### Reduced fixtures — five shapes, ALL CLEAN, so they retire several theories

Built with the in-lane seed, `--backend=cranelift`, native output compared
against `bin/simple run`. Only difference in every case: native `print` omits
newlines (cosmetic).

| fixture | construct | verdict |
|---|---|---|
| `ifexpr` | `val x: T = if f(): g() else: ...` for text/i64/bool | values identical |
| `tupret` | `return (self.ctx, false)` after `add_error`, incl. inside `unsafe(capabilities: [ffi])` | values identical |
| `nestret` | the SAME nesting as the guard above: outer `if` -> `unsafe` -> inner `if` -> `return`, plus two controls | values identical |
| `interp5` | one message with five interpolated `.len()` slots | values identical |
| `chainfield` | interpolation over chained field-of-field owners inside a method | values identical |

**Retired by measurement, do not re-open:**
- The tuple `(heap-class, bool)` early return is NOT misread — `false` reads
  back as `false` and the `add_error` mutation lands. The composite hypothesis
  "a guard fired, `add_error` silently no-oped, and `false` was read as `true`"
  does not reproduce.
- A `return` nested three levels deep (`if` / `unsafe` / `if`) fires correctly.
- The `visit` line's five-slot interpolation is not itself droppable.
- An if-expression bound to a `val` is not lowered as a function return —
  refuted from source: `lower_hir_block` keeps a `Return` tail as a STATEMENT,
  and arms join through a real CFG merge block with a result temp
  (`50.mir/mir_lowering_stmts.spl:2194-2281`).

That every fixture is clean while the 692-module input fails is itself the
finding: this defect is **scale- or state-dependent**, which is why
`c018ee15926`'s standalone fixture did not reproduce either.

### Live secondary signal, same family

`E-HIR-BLOCK-VALUE-TYPE-DECAYED`
(`20.hir/hir_lowering/_Expressions/block_and_asm_lowering.spl:161`) fires
**6-10 times on a ~50-line fixture**. Its own comment says a fires-at-B split
means the value "decayed in this function (transient scope end), which is the
streaming-HIR-owner class" — i.e. heap-word decay across reclamation points is
demonstrably live at tiny scale and merely CONTAINED there by a placeholder
substitution. The phase-3 owner has containment only at the guards.

### A separate, fully reproduced defect found on the way

A Stage-2 binary SEGVs on a **two-line hello world**, and gdb puts the fault in
`CompileContext.error_message_at` — i.e. the compiler crashes while REPORTING
an error it correctly detected. Root cause is an element-type loss on `a[i]`
for `[text]`/`[bool]`/`[f64]`, with a 7-line reproducer and named lowering
sites. Filed separately as
`native_typed_array_element_read_loses_element_type_2026-08-24.md`, with gate
`scripts/check/check-native-array-element-type.shs`. Whether fixing it also
unblocks Stage 3 is **NOT established** — the escape point above is a distinct
measurement.

### Next step

Two more receipts inside the six-line window (after the `if surfaces == nil:`
block, as the first statement inside the `unsafe` block, and after the inner
`if` while still inside it) reduce this to a single statement. They are already
written in this lane; the confirming run was blocked by
`bootstrap-admission-error: parent-stage2-sanity-admission-mismatch`
(`STEP2_RC=64`) — re-minting a receipt fails once Stage 2 has been rebuilt,
which is the re-invocation defect already recorded above in this file.
