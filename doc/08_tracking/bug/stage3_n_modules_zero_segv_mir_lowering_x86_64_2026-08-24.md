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

---

## CORRECTION (2026-08-24, later the same day) — READ THIS FIRST

**The section below overstated its conclusion and is CORRECTED here. Do not
cite it standalone.** A real defect in the probe was found and fixed, but it is
**NOT** the root cause of this bug, and Stage 2 still SEGVs.

**What is proven:** `rt_heap_ref_wellformed` required the heap tag, and on the
native codegen lane a class reference is a raw UNTAGGED pointer, so the probe
answered 0 for every live class instance. Measured red→green on a native
fixture: `class-instance wellformed = false` → `true`. That was a genuine
latent defect — the guard could never have passed even on GOOD data — and the
fix is correct and necessary. **A second half was missed on the first pass and
is now also fixed:** the Stage-2 binary resolves this symbol to the **Rust**
runtime (`src/compiler_rust/runtime/src/value/objects.rs`), *not* to
`runtime_native.c`. Verified by disassembling the shipped binary.

**What is DISPROVEN:** that fixing the probe repairs Stage 2. With the tag test
confirmed **gone from the shipped Stage-2 binary** —

```
000000000112bd8e <rt_heap_ref_wellformed>:
 112bd8e:  48 81 ff 00 10 00 00   cmp    $0x1000,%rdi
 112bd95:  0f 93 c0               setae  %al
 112bd98:  c3                     ret
```

— the guard **still fires**:

```
NATIVE_BUILD_RC=139
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module
surface payload malformed at HIR entry
```

Since the probe now answers 0 **only** when `(value & ~7) < 4096`, the retained
surfaces owner payload is **genuinely a small word (0 or near-0), not a
pointer**. The guard is therefore **doing its job and correctly reporting a real
upstream defect**.

**So the answer to deliverable 1 is: BOTH, in sequence.** The check WAS wrong
(now fixed), AND the surfaces owner IS genuinely malformed (still open, and it
is the actual self-hosting blocker).

**Ruled out as the cause of the malformed value** — the driver's exact shape
reproduces CLEAN in a small native program, so this is not an `Any`-marshalling
or Option-unwrap artifact:

```
A fresh-local = true
B option-field-unwrap = true n=42     <-- Option<class> FIELD stored, read back, unwrapped
```

**Where to look next:** whatever populates `self.ctx.module_surfaces` between
phase 2 and HIR entry loses it — the payload word is zeroed while the Option
stays `Some`. That is the 2026-08-22 zeroed-payload class, now confirmed to be
occurring for real on this path rather than hypothetically. The narrowed
receipts (`r01-unwrapped` prints, `r02-wellformed` does not) are consistent with
this and remain the best entry point.

---

## Original section (SUPERSEDED IN PART by the correction above)

## Probe defect found and fixed (2026-08-24, lane `lane-retained-surfaces`)

`E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` fired on a **valid** hello world
because the formation probe backing it, `rt_heap_ref_wellformed`, **required the
heap tag** — and on the native codegen lane a **class reference is a raw
UNTAGGED pointer**, not a `|1`-tagged runtime value. The probe therefore
answered 0 for **every live class instance** on that lane.

Both driver HIR-entry guards pass a class reference
(`ModuleSurfacesByName`), so on the native lane they could **never** pass:

- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:149` → `E-DRIVER-HIR-OWNER-MALFORMED`
- `src/compiler/80.driver/driver_hir_pipeline_lowering.spl:585` → `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED`

**The surfaces were never malformed. The CHECK was wrong.** This resolves the
question deliverable 1 posed: the two branches needed opposite fixes, and the
evidence picks the second.

### Measured evidence — the discriminating differential

The same live class instance, the same probe, the two lanes. Fixture:
`extern fn rt_heap_ref_wellformed(value: Any) -> bool`, a two-field class, one
`print`. Exit codes read directly into a variable on the line after each
command, never through a pipe.

```
INTERP_RC=0
  class-instance wellformed = true      <-- interpreter (Rust runtime): heap-tagged
  text-value wellformed = true

NATIVEBUILD_RC=0
NATIVE_RUN_RC=0
  class-instance wellformed = false     <-- NATIVE lane: THE DEFECT
  text-value wellformed = true          <-- runtime value types ARE tagged
```

`text` reporting `true` on both lanes is what isolates the cause to the **class
representation**, not to the probe being unreachable or unlinked.

### The fix (minimal, semantics-preserving)

Drop the **tag requirement** only; keep zero-page rejection, which is what
actually catches the 2026-08-22 incident value `0`. One line removed in each of
the two lanes that had it:

- `src/runtime/runtime_native.c` — probe body is now a single masked comparison
- `src/runtime/simple_core/core_enum.spl` — same, pure-Simple mirror
- `src/compiler_rust/runtime/src/value/objects.rs` — **behaviour unchanged**;
  on the Rust lane every live object is a heap value, so `is_heap()`
  false-rejects nothing. Contract prose updated only.

**The protection the guard was added for survives**: all five previously pinned
rejections (`0`, nil `3`, tagged scalar `24`, heap-tagged zero-page `2049`,
heap-tagged real address) mask below/above 4096 exactly as before and still
return the same answers. Verified by running the C self-check — 5/5 unchanged,
plus a new sixth case pinning the untagged pointer.

Call sites were deliberately **not** touched: deleting them would lose the
zeroed-payload protection and orphan the probe plus its four mirrors, a far
larger diff. Realigning the probe with its own stated prime directive — *"must
never false-reject a live object"* — is the smaller and more honest change.

### Why this shipped green

Every test the probe had was **source-text matching**
(`expect(driver).to_contain(...)`) or a C self-check fed **only synthetic
heap-TAGGED words**. Nothing ever asked the probe about an untagged pointer, and
nothing ever ran either driver guard on a real class instance on the native
lane. The new gate closes exactly that gap by compiling and RUNNING the probe.

### Retired loose thread: the "missing archive symbol"

`rt_heap_ref_wellformed` was reported as **0 occurrences** in
`build/simple-core/libsimple_runtime.a`, and several lanes hit `unknown extern
function: rt_heap_ref_wellformed`. **This was stale build directories, not a
missing archive member.** Measured across five worktrees: every archive is dated
**2026-08-18**, five days before the probe landed (`57271d9ba49`, 2026-08-23).
`runtime_native.o` *is* a member, and the probe's immediate source neighbours
(`rt_enum_payload`, `rt_enum_check_discriminant`) *are* present. A fresh
`native-build` in this lane linked and ran the symbol with `NATIVEBUILD_RC=0`.
The precedent-based theory (add a missing archive member, per the 2026-08-21
three-member fix) was therefore **wrong**, and is recorded here so it is not
resurrected.

### Still open — a SECOND, separate defect (not fixed here)

The driver symptom "streaming method returns SUCCESS from its middle, zero
recorded errors, verdict `true`" is **error-propagation loss**, distinct from
this one: the guard *did* `add_error` and `return (self.ctx, false)`, yet the
caller saw success and MIR lowering then dereferenced an empty program and
SEGV'd. Fixing the probe stops the guard from firing spuriously, which makes
this defect **latent rather than resolved** — a future genuine fail-closed
return on the native lane may still be swallowed the same way. It needs its own
investigation and its own reproducer.

### Regression fence

`scripts/check/check-heap-ref-wellformed-accepts-class-refs.shs` — fail-closed,
`--selftest` first and fatal, verdict last.
`PASS — 6 case(s) checked, ...` exit 0 / `FAIL` exit 1 / `ERROR` exit 2; a
compiler-less machine or an unextractable probe is ERROR, never a pass. Unlike
the existing `.spl` spec it **compiles and runs** the shipped probe.
Mutation-tested three ways against the real tree:

| mutation | verdict | rc |
|---|---|---|
| restore tag test in C probe | `FAIL — 6 case(s) checked, ... C:untagged(want 1, got untagged=0)` | 1 |
| restore tag test in pure-Simple mirror | `FAIL — 6 case(s) checked, ... simple-mirror:requires-heap-tag` | 1 |
| delete the probe entirely | `ERROR — nothing was checked (could not extract ...)` | 2 |
| tree restored | `PASS — 6 case(s) checked, ...` | 0 |

## 2026-08-24 (lane-surfaces-payload): reproduced on Stage 2, plus a SECOND defect — phase 3's failing verdict is lost

### Reproduction (preserved Stage-2 binary, fresh seed, exit code read directly into a variable)

Binary: `/mnt/data/worktrees/lane-retained-surfaces/build/bootstrap/lanefix3/stage2/x86_64-unknown-linux-gnu/simple`
Input: a two-line `hello.spl` in a fresh output dir, `SIMPLE_COMPILER_PHASE_PROFILE=1`.

```
NATIVE_BUILD_RC=139
```

Log tail, verbatim:

```
[BOOTSTRAP-PHASE] +137ms phase2:parse:done n_modules=1 carrier=modules
[BOOTSTRAP-PHASE] +137ms phase3:route ready=false config=false n_modules=1 n_sources=1
[BOOTSTRAP-PHASE] +137ms phase3:legacy:entry n_modules=1 n_sources=1
[BOOTSTRAP-PHASE] +137ms phase3:hir_typecheck:done
[mono] generic_fns=0 call_sites=0 specializations=0 unresolved=0
[BOOTSTRAP-PHASE] +320ms aot:lower_to_mir:module:done idx=0 module=hello functions=0
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module surface payload malformed at HIR entry (heap-typed payload word is 0 or in the zero page)
```

### Three facts this pins that were previously mis-stated

1. **The failing route is LEGACY, not streaming.** `phase3:route ready=false config=false`.
   The earlier "measured `ready=true config=true`" note in this record does not
   describe this failure and must not be used to reason about it. The two guards
   emit DIFFERENT codes — `E-DRIVER-HIR-OWNER-MALFORMED` (streaming,
   `driver_hir_pipeline_lowering.spl:150`) vs
   `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` (legacy, `:585`) — and it is the
   legacy code that fires. Phase 2 therefore ran `parse_all_impl`'s
   native-entry-closure branch (`driver_source_pipeline_parsing.spl:737-861`,
   confirmed by the `[build] surface_freeze` receipts, which exist only there),
   which commits `self.ctx.module_surfaces = Some(entry_surfaces)` at `:854`
   and — unlike the streaming path — never calls `module_surfaces_promote`.

2. **It is native-codegen-specific.** The same source, same input, run by the
   Rust seed's interpreter (`native-build` under a freshly built
   `cargo build --release --bin simple`) gives `SEED_NATIVE_BUILD_RC=0` with the
   same `ready=false config=false` legacy route. Only the natively compiled
   Stage-2 binary reproduces.

3. **The shape alone does not reproduce.** Three standalone native-built
   fixtures — (a) `Option<class>` field unwrapped into an `Any` extern arg,
   (b) the same through two levels of class field (`self.ctx.module_surfaces`)
   inside a `me` method with the guard's exact `if != nil` / `unsafe` / inline
   `.unwrap()` form, and (c) the whole-context `self.ctx = parsed_ctx`
   reassignment after a tuple return — all report `wf=true` at every point and
   exit 0. So this is not a marshalling, unwrap, or context-copy *shape* defect;
   something in the real run changes the payload.

### LOCALIZED (instrumented Stage 2, probes on both carriers at every transition)

A Stage 2 was rebuilt from `origin/main` with `rt_heap_ref_wellformed` formation
probes (no dereference, no new extern -- the same disassembly-verified probe the
guard uses) at each transition between phase 2's commit and HIR entry. Verbatim:

```
[ZP] A pre-store  ...
[ZP] P1 parse:entry-closure:committed local=true readback=false isnil=false
[ZP] P2 orchestration:after-parse wf=false
[ZP] P3 orchestration:pre-phase3 wf=false
[ZP] P4 hir:legacy-entry inline=false hoisted=false
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED
```

**The payload dies inside a single statement.**
`driver_source_pipeline_parsing.spl:854`, `self.ctx.module_surfaces = Some(entry_surfaces)`:
the local `entry_surfaces` is a well-formed heap reference (`local=true`) and the
value read straight back out of the field on the very next line is a small word
(`readback=false`) while the Option still compares non-nil (`isnil=false`). This is
exactly the 2026-08-22 zeroed-payload class, and it is NOT an accumulation across
the phase boundary -- P2/P3/P4 merely carry forward a value that was already dead
at the point of commit. Everything downstream (the orchestration window, the
source-reclaim block, the phase-3 route, the guard's inline-vs-hoisted unwrap) is
therefore ruled out as the cause; `hoisted=false` at P4 additionally rules out the
guard's own expression shape.

Not reproducible standalone: four native-built fixtures of increasing fidelity --
up to a six-field class with `[T]`/`Dict<text,i64>`/`i64`/`bool` fields stored into
an `Option` field of a class held by another class, written and read back inside a
`me` method -- all report `local=true optUnwrap=true ctxReadback=true`. The defect
needs the real function's context, which points at codegen (field displacement,
spill, or the `Some` construction) rather than at the source shape.

### ROOT CAUSE (proven by disassembly of the failing Stage-2 binary): `.unwrap()` on an Option bound to `Poll.unwrap`

A second instrumented Stage 2 split the store from the read-back:

```
[ZP] A pre-store  local=true  optUnwrap=false
[ZP] B post-store readback=false localAfter=true optAfter=false isnil=false
```

`local=true` / `localAfter=true`: the class reference is intact throughout.
`optUnwrap=false` BEFORE the field store: **the field store is innocent.** What
returns a small word is `.unwrap()` itself, on a freshly constructed
`Some(entry_surfaces)` sitting in a local.

Disassembling the failing Stage-2 binary at the probe's `.rodata` anchor
(`parse_all_impl`, vaddr 0xe3c070) shows why:

```
e3e7a0: mov $0x1,%edi ; mov $0xf1987159,%esi ; mov %r14,%rdx
e3e7b4: call *%r10                 <- rt_enum_new(1, 0xf1987159, entry_surfaces)
e3e7be: mov %rax,0x78(%r10)        <- STORE module_surfaces, disp 0x78
e3e7d9: mov 0x78(%r11),%rdi        <- LOAD  module_surfaces, disp 0x78
e3e7e4: call ...Poll_dot_unwrap    <- lib__nogc_async_mut__async__poll__Poll_dot_unwrap
```

Store and load use the SAME displacement (0x78), so there is no field-offset
bug -- the layout hypothesis is disproven. The `Some` is constructed correctly
with tag `0xf1987159`. The defect is the CALLEE: `.unwrap()` on a
`ModuleSurfacesByName?` was emitted as a direct call to **`Poll.unwrap`**, the
unrelated async `Poll<T>` helper from `src/lib/nogc_async_mut/async/poll.spl`:

```
e85d42: mov $0x91301d4e,%esi ; call rt_enum_check_discriminant   # Poll::Ready
e85d58: mov $0xabfb25a5,%esi ; call rt_enum_check_discriminant   # Poll::Pending
e85d72: xor %rax,%rax                                            # neither -> RETURN 0
```

The stored tag matches neither Poll case, so the callee falls through and
returns **0**. Zero masked of its low three bits is 0, which is `< 4096`, which
is exactly the "heap-typed payload word is 0 or in the zero page" the guard
reports -- while the field itself still holds a real enum object, which is why
the Option keeps comparing non-nil. Every later probe (P2/P3/P4) reads `false`
because every one of them goes through the same miscompiled `.unwrap()`.

### Why: an erased receiver binds a bare method name by SUFFIX ALONE

`compiler/src/codegen/instr/closures_structs.rs` resolves a bare (dot-less)
method name by scanning `ctx.func_ids` for any key ending in `.unwrap` or
`_dot_unwrap`, with **no receiver-type test in the filter**. When the receiver
type is erased -- as it is for a class field read -- `Poll.unwrap` is simply the
`*.unwrap` symbol that happens to be linked in, and it wins.

A guard against exactly this already existed in that file, and
`pipeline/native_project/mangle.rs` carries two more of the same shape (added
for an identical `FailSafeResult.unwrap` leak). **The guard was dead**: it was
gated on `candidates.len() > 1`, so it only fired on multi-candidate ambiguity,
never on the single-candidate bind. The file's own tail comment says so --
"EXACTLY the single-candidate erased-receiver bind that produced the known
thefts, and it is silent today". This is the pre-existing class recorded in
`doc/08_tracking/bug/codegen_bare_method_receiver_type_blind_candidate_selection_2026-07-28.md`.

### NOT FIXED -- the bind site is still unidentified. Read this before trying again.

The obvious candidate was `compiler/src/codegen/instr/closures_structs.rs`, which
resolves a bare (dot-less) method name by scanning `ctx.func_ids` for any key
ending in `.unwrap` / `_dot_unwrap` **with no receiver-type test in the filter**,
and whose existing refusal for enum-helper names was gated on
`candidates.len() > 1` -- dead for a single-candidate bind. That file's own tail
comment already says the single-candidate path is "EXACTLY the single-candidate
erased-receiver bind that produced the known thefts, and it is silent today".

Two Stage-2 rebuilds were spent on that hypothesis and **it is wrong, or at least
insufficient**. Both attempts were reverted rather than landed:

| attempt | change | result |
|---|---|---|
| 1 | hoist the guard above the `unique_ids` early-return, drop the candidate-count clause, require `matches!(receiver_ty, None \| Some(TypeId::ANY))` | `FIX_NATIVE_BUILD_RC=139`, signature still present |
| 2 | same, minus the `receiver_ty` clause (exactly `mangle.rs`'s shape) | `FIX2_NATIVE_BUILD_RC=139`, signature still present |

After attempt 2, `Poll_dot_unwrap` still has **269** references binary-wide and
**4** call sites inside `lower_and_check_impl`. The guard never fires for this
bind, so the name does **not** reach that `.or_else` fallback -- it is resolved
somewhere else, most plausibly already qualified as `Poll.unwrap` before mangling
(which is also why `mangle.rs`'s two sibling refusals, both gated on the name
having no type qualifier, do not catch it either). **Finding where a `T?`
receiver's `unwrap` acquires the qualifier `Poll.` is the next lane's target.**

Neither codegen change was landed: an unverified change to method dispatch is a
worse trade than an open bug with a precise record.

#### A false green worth not repeating

`objdump -d BIN | grep -c "call.*Poll_dot_unwrap"` returns **0** on a binary that
calls it 269 times. The bind is emitted as `lea <sym>(%rip),%reg` followed by
`call *%reg`, never as a direct `call <sym>`. That grep briefly "proved" attempt 1
had removed the miscall. Match `_dot_unwrap>` (the symbol reference in objdump's
comment column), not `call`.

### THIRD DEFECT, filed not fixed: a non-exhaustive enum match falls through to 0

`Poll.unwrap` is written with a total two-case `match` and no wildcard, yet its
compiled form ends in `xor %rax,%rax` for an unmatched discriminant. A value
whose tag matches no case silently yields 0 instead of trapping. Had that path
trapped, this defect would have been a loud crash inside `Poll.unwrap` on day
one instead of a day-long hunt for a "zeroed payload". Worth its own record.

### Gate

`scripts/check/check-stage2-option-unwrap-not-stolen.shs` -- **ADVISORY, landed
honestly RED.** Fail-closed, `--selftest` first and fatal (6 fixtures), verdict
last, `PASS n>0` exit 0 / `FAIL` exit 1 / `ERROR` exit 2; every subprocess status
is read directly into a variable on the line after the invocation, never through
a pipe. Given `--stage2 <path>` it performs two checks: a SYMBOLIC one counting
`*_dot_unwrap` call sites inside the driver's HIR-entry function (a correct build
routes an Option unwrap through `rt_enum_payload` / `rt_unwrap_or_trap`, never
through a Simple method), and a BEHAVIOURAL one asserting a hello-world build
emits no malformed-surfaces signature and does not crash. Signature-absence plus
a crash test rather than `rc == 0`, since a Stage-2 build has unrelated failure
modes this guard must not claim to pin. No `--stage2`, a missing `nm`/`objdump`,
or a stripped artifact are all ERROR -- absence of evidence is never a pass.

Measured against a Stage 2 built from `origin/main`:

```
FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s) inside
lower_and_check_impl -- an Option unwrap bound to a user method instead of the
runtime builtin; hello world emitted E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED
(rc=139);
```

The guard shipped with a fail-open of its own, found and fixed before landing: a
relative `--stage2` path did not resolve inside the private temp cwd the
behavioural check runs in, so the invocation failed 127, emitted no signature,
and scored CLEAN. The path is now made absolute, and an invocation that produces
an empty log is ERROR rather than a pass. Promote to MANDATORY once a real fix
makes it green.

### SECOND DEFECT (independent, and the reason this took a day to find): phase 3's `return false` is lost

The guard at `driver_hir_pipeline_lowering.spl:584-586` does `self.ctx.add_error(...)`
followed by `return (self.ctx, false)`. `driver_orchestration.spl` destructures
that into `analyze_ok` and has an `if not analyze_ok:` block that prints
`phase 3 FAILED` with every recorded error. **That block did not run.** Instead
the log shows `phase3:hir_typecheck:done`, monomorphize over `generic_fns=0`,
MIR lowering `functions=0`, and the error only surfacing three phases later,
relabelled `[ERROR] MIR error: ...`, immediately before the SEGV.

So an early `return (ctx, false)` from deep inside the large `me lower_and_check_impl()`
method reached the caller as a SUCCESS verdict. Consequences:

- A fail-closed guard that fires is downgraded to an advisory note.
- An empty HIR program flows into monomorphize and MIR lowering, which is what
  actually SEGVs (`NATIVE_BUILD_RC=139`).
- The operator sees a MIR-stage error for a phase-3 defect.

This is latent only in the sense that the guard still prints *something*. It is
the same family as the already-recorded `c018ee15926` boolean-misread and the
"stale CompileContext snapshot" verdict defects noted in
`driver_source_pipeline_parsing.spl:840-852` and `driver_orchestration.spl:176-182`.
Fixing it alone would convert the SEGV into a clean, correctly-attributed
phase-3 failure — worth doing regardless of the payload root cause.

### FIFTH BLOCKER found underneath (fixed): origin/main could not build a Stage 2 at all

Rebuilding Stage 2 from `origin/main` (f7a49a61c0b) to carry the probes failed
before reaching the driver at all:

```
[CODEGEN BODY] Function 'MirToLlvm.translate_instruction_at' body compilation failed:
  GlobalLoad: unresolved identifier 'load_symbol_slot'
Build failed: native-build aborted: 1 file(s) failed to compile
error: --stop-after-stage2 requires a successful admitted Stage 2 compiler
```

Cause: `be3e6fe4a21` (landed 2026-08-24) replaced the raw `LoadGlobal` payload
decode in `src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl` with
typed accessors and deleted the `load_symbol_slot` local, but left a reference
to it inside the adjacent `if bootstrap_debug:` print. The seed's tree-walk
interpreter never evaluates that branch, so `simple run` / `test` stayed green;
native codegen resolves every identifier in a function body and rejects it.

Note the shape: a *debug print* — exactly the class of line that gets removed
during cleanup — is what made the whole self-host lane unbuildable, and no gate
caught it because every non-native lane is blind to it. This is independent of
the surfaces-payload defect and strictly upstream of it: while it stood, no
Stage 2 existed to reproduce the payload defect on.

Fixed by dropping the stale interpolation (an identical fix landed concurrently
from another lane, so `origin/main` already carries it).

## FIXED 2026-08-24 (lane-errprop) — the lost `return false` is a TUPLE-RETURN-INSIDE-`unsafe` defect

Scope: this section fixes ONLY the propagation loss recorded in "SECOND DEFECT"
above. The surfaces-payload root cause (why the payload is malformed at all)
remains open and is untouched here.

### Reproduced first, in a private lane

Private `git worktree --detach` at `d7a667bb37e`; `git status --porcelain` = 0
before the run. Compiler: the preserved Stage 2 `zpfix2`
(`/mnt/data/worktrees/lane-surfaces-payload/build/bootstrap/zpfix2/stage2/x86_64-unknown-linux-gnu/simple`),
input a two-line `hello.spl`, `SIMPLE_COMPILER_PHASE_PROFILE=1`, exit status
read directly into a variable on the line after the command:

```
NATIVE_BUILD_RC=139
[BOOTSTRAP-PHASE] +102ms phase3:route ready=false config=false n_modules=1 n_sources=1
[BOOTSTRAP-PHASE] +102ms phase3:legacy:entry n_modules=1 n_sources=1
[BOOTSTRAP-PHASE] +102ms phase3:hir_typecheck:done
[ERROR] MIR error: E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: retained module surface payload malformed at HIR entry
```

This is the discriminating pair, and it settles the mechanism:

- `add_error` **did** run — its message survives and resurfaces three phases
  later, relabelled `[ERROR] MIR error: ...`. So the error LIST propagates, and
  every COW-alias / lost-context theory for the *errors* is refuted.
- `phase3:hir_typecheck:done` **still printed**. That line is only reachable
  past `if not analyze_ok:` in `driver_orchestration.spl`, so `analyze_ok` was
  **true**. The BOOLEAN alone was lost, and execution fell through the `return`.

Both orchestration call sites (`driver_orchestration.spl:177`, `:285`) do
destructure and test `analyze_ok`, so "caller ignores the boolean" is refuted at
source level. `CompileContext.add_error` (`driver_types.spl:987`) mutates
through the single owner (`self.errors.push`), so the documented COW-alias class
is refuted there too.

### Root cause

The failing `return (self.ctx, false)` was written **inside an
`unsafe(capabilities: [ffi])` block**. A tuple-shaped return in that position is
lost under native codegen: the terminator does not exit the function and control
falls through past the block.

The census is the load-bearing evidence, and it is 2/2:

| return shape inside an `unsafe` block | sites | status |
|---|---|---|
| tuple `return (a, b)` | **2** | both are the implicated phase-3 guards (`:152` streaming, `:586` legacy) |
| scalar / enum / value | **87** | work fine (`string_core`, `llvm_ir_builder`, `driver_public_shared`, …) |

Those two were the ONLY tuple-returns-inside-`unsafe` in the entire owned tree,
and they are exactly the two guards whose verdicts were observed to vanish. The
87 others are in heavily exercised code and are demonstrably fine, so "return
inside `unsafe` never works" is false — the defect is specific to the tuple
shape.

### Fix (minimal, semantics-preserving)

At both sites the formation probe STAYS inside the `unsafe` block (the extern
call genuinely needs the `ffi` capability); only the verdict return is hoisted
to function-body level, the shape that works everywhere else:

```
var retained_surfaces_wellformed = true
if self.ctx.module_surfaces != nil:
    unsafe(capabilities: [ffi]):
        retained_surfaces_wellformed = rt_heap_ref_wellformed(self.ctx.module_surfaces.unwrap())
if not retained_surfaces_wellformed:
    self.ctx.add_error("E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED: ...")
    return (self.ctx, false)
```

No guard is weakened: the nil check, the probe, the recorded error and the
failing verdict are all preserved, and the probe remains side-effect-free (a
formation probe, never a dereference). Equivalence of the hoisted shape was
checked directly (`trip=true -> ok=false`, `trip=false -> ok=true`).

### Gate

`scripts/check/check-no-tuple-return-in-unsafe.shs` — `--selftest` runs first
and is fatal (3 fixtures: an offending tuple return must be detected; the
hoisted form AND a scalar return inside `unsafe` must stay clean; an empty tree
must scan 0 blocks so the caller is forced to ERROR). Verdict is the last line
of stdout: `PASS — <n> unsafe block(s) checked, 0 tuple return(s)` exit 0 /
`FAIL` naming each site exit 1 / `ERROR — nothing was checked` exit 2. A run
that scans 0 unsafe blocks is ERROR, never a pass.

Measured: `PASS — 1190 unsafe block(s) checked, 0 tuple return(s)`.
Mutation-tested BOTH directions — reintroducing the defect shape at the legacy
site yields `FAIL — 1190 unsafe block(s) checked, 1 tuple return(s)` naming
`driver_hir_pipeline_lowering.spl:608`; restoring the fix returns to PASS.

### Honest limits — what this does NOT establish

- **A native rebuild WAS attempted in this lane and did not finish in time.**
  `bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2
  --backend=cranelift --mode=dynload --jobs=full --output=build/bootstrap/errprop1`
  was started from the fixed tree and ran ~30 minutes, still inside the stage-1
  self-host step (13 live processes, no stage-2 artifact emitted) when this lane
  closed. It was NOT observed to fail — it was simply not finished, so it yields
  no verdict either way and is recorded as an attempt, not as evidence. The
  re-run below is therefore still owed.
- **Not verified by a native rebuild.** Every PRE-EXISTING Stage-2 binary on this host SEGVs
  on a two-line hello world (`zp2`, `zp3`, `zpfix`, `zpfix2` all
  `NATIVE_BUILD_RC=139`; the older `starfive` stage2 fails to build one at all),
  so no working native compiler existed in which to rebuild the driver and
  re-run the guard. The fall-through is *reproduced and measured*; the tuple
  shape is identified by a 2/2-vs-87 census and not yet by disassembly. Whoever
  next gets a working Stage 2 should re-run the reproduction above and confirm
  `phase 3 FAILED (1 recorded error(s))` now prints instead of
  `phase3:hir_typecheck:done`.
- The underlying malformed-payload defect is unchanged; this fix converts its
  SEGV into a correctly-attributed phase-3 failure, which is what the "SECOND
  DEFECT" section asked for.
- Sibling COW-alias instance noted while here, NOT fixed (out of scope, no
  measured failure): `CompileContext.mark_module_poisoned`
  (`driver_types.spl:1025`) does `self.poisoned_modules = self.poisoned_modules.push(name)`,
  the temporary-alias write shape that `.claude/rules/code-style.md` forbids.
