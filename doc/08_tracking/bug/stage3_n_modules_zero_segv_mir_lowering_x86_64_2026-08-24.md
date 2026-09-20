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

## 2026-08-25 (lane `lane-poll-unwrap`, verification lane) — RED re-confirmed on current `origin/main`; THIRD bind-site theory REFUTED by measurement

This lane was opened to finish an interrupted verification, not to add a theory.
It carried out two full sanctioned bootstrap cycles and lands **no code**. Both
results below are measurements; neither is a code reading.

### Scope note — which backend

The reproducer in this record is `--backend=cranelift` (see the Commands
section at the top). That matters and had been lost: `bootstrap-from-scratch.sh`
**defaults to `--backend=llvm`** (`--backend=<name>` help text, line ~4028), and
LLVM 18 is present on this host, so a bootstrap invoked without an explicit
`--backend` builds a *different lane* than this record's evidence. A first run
in this lane was started that way and was discarded unmeasured for exactly that
reason. Every number below comes from the record's own invocation:

```
bootstrap-from-scratch.sh --strategy=adhoc --full-bootstrap --stop-after-stage2 \
    --backend=cranelift --mode=dynload --jobs=full --output=<out>
  -> "Stage 2 admitted; stopping before Stage 3 as requested."   (rc=0)
```

### Finding 1 — the defect STILL REPRODUCES at `3b676a17736`

`origin/main` had moved to `3b676a17736` ("fix(hir): register enum-body method
return types — the second `case Some(x)` defect"), which is adjacent to this
erased-receiver defect, so the baseline was re-measured from scratch rather than
assumed. Fresh seed, fresh Stage 2, pristine tree (the previous lane's
uncommitted edit was removed first, so nothing foreign was in the tree).

```
RED_RC=1
FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s) inside
lower_and_check_impl -- an Option unwrap bound to a user method instead of the
runtime builtin; hello world emitted E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED
(rc=139);
```

Byte-identical verdict to the recorded baseline. **The hir fix `3b676a17736`
does not cover this defect.** Stage-2 sha256
`36cdfad6f671cf9b06e9c9360b162a08b7d499a0d8d14fccc62d51527ddcde93`.

### Finding 2 — theory #3 (the cranelift builtin-first gate) is REFUTED

The previous lane's judgement, recorded in `.bugaddendum.md`, was that the
preempting fix belongs at the cranelift **builtin-first gate**
(`codegen/instr/closures_structs.rs:702`), routing bare enum helpers to
`rt_unwrap_or_trap` *before* name resolution. That is a well-founded reading:
the same file fixed the *identical* defect class twice before by exactly this
mechanism — `ByteSpan.starts_with` and `ByteSpan.slice` were both stolen from an
erased receiver and both fixed by adding the bare name to
`is_bare_builtin_collection_method`, which the `:702` gate consults before any
name-based resolution. `try_compile_builtin_method_call` already maps
`"unwrap" => "rt_unwrap_or_trap"` and `"unwrap_or" => "rt_unwrap_or_value"`, so
the routing target existed and no undefined-symbol/NULL-GOT risk was introduced.

The fix applied was therefore the minimal in-pattern one: add `("unwrap", 0)`
and `("unwrap_or", 1)` to `is_bare_builtin_collection_method`. (Arity excludes
the receiver, which `:704` passes separately — matching the existing
`("starts_with", 1)` rows.)

Measured, same invocation, same gate:

```
FIX_RC=1
FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s) inside
lower_and_check_impl -- ... (rc=139);
```

**Both gate numbers unmoved: 4 call sites, rc=139.** This is not a no-op build:
the two Stage-2 binaries differ,
`e7481b094328bc2ba6e93e5baa572ef6b0132801dff5cbfd32fee0f82ad2084e` vs the RED
hash above, and the bootstrap independently reported "Seed/runtime stale (Rust
source content changed since last build)" and rebuilt the seed. The fix was
compiled in and changed the binary; it did not change the defect.

The patch is preserved, unlanded, at
`/mnt/data/tmp/refuted_closures_structs_fix.patch`.

### What this eliminates, stated as the two-step inference it is

The discriminator `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` was set for the whole
fixed build and produced **zero** output. That reporter is genuinely wired — two
live call sites, `closures_structs.rs:996` and `:1049` — so its silence is
evidence, not a vacuous absence. But both report sites sit *after* the
`unique_ids.len() == 1` early-return at `:962`, so silence on its own is
consistent with either "bound via `import_map`" or "the `:962` early-return
fired".

The second fact breaks that tie: the `:702` gate runs *before* `:962`, so the
applied fix would have preempted the early-return path too. It moved nothing.
Taken together — a `:702` gate that does not fire, and a reporter that never
speaks — **the offending bind does not flow through `compile_method_call_static`
at all.** That points at the `MirInst::Call` / cross-module import route
(`codegen/instr/calls.rs:~3828`, `ctx.use_map.get(func_name).or_else(|| ctx.import_map.get(func_name))`,
fed by the bare-method-name insertion in `pipeline/native_project/imports.rs`
`build_import_map:~606-618`, where >1 candidate becomes `ambiguous` yet a non-`_`
name still keeps arbitrary HashMap-order first-wins).

That is a *direction*, not a proven site. It is deliberately not being acted on
in this lane: three theories have now been refuted by measurement, and the
standing instruction is that an open record beats a fourth blind iteration.

Note for whoever takes it: refusing the bind at `calls.rs:3828` or at
`build_import_map` is **not** sufficient on its own. Unlike the `:702` gate,
those sites have no builtin-routing fallback — the documented fall-through is a
link-time import of the raw name, which this repo has already seen become an
undefined symbol, a NULL GOT slot and the *same* rc=139 by a different cause
(`check-no-unresolved-runtime-symbols.shs`, and the `rt_unwrap_or_trap` incident
in `stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`). A fix
there must also establish where the refused bare name gets routed instead, and
`nm -u` the resulting Stage 2 for an undefined bare `unwrap` before attributing
any surviving SEGV to the original defect.

### The cost problem, and the highest-value next step

Each theory tested here costs a **~40-minute full bootstrap**, because the only
reproducer currently in use is Stage 2 itself. That is what has made three
refutations expensive and it is the reason to fix the harness before the defect.

The *symbolic* half of the gate — the wrong-callee bind — does not need a
bootstrap at all. A small `.spl` fixture with an erased-optional `.unwrap()`,
compiled directly by the seed's `native-build` with `poll.spl` inside the entry
closure, exhibits the bind in minutes and can be disassembled the same way. The
evidence worktree once held exactly this (`zpfix2` in
`/mnt/data/worktrees/lane-surfaces-payload`); it is **gone** — that path no
longer exists. **Reconstructing that minutes-scale fixture should be the first
step of the next attempt, ahead of any further code change.**

### Status of the other on-disk candidate (unmeasured, not discarded)

The previous lane's uncommitted edit (`imports.rs` `is_bare_enum_helper` +
`mangle.rs` refusals) is preserved at
`/mnt/data/tmp/candidate_poll_unwrap.patch` and is **not landed**. It is inert
for *this* record's reproducer: `mangle_mir` has exactly one non-test caller,
`pipeline/native_project/compiler.rs:849`, inside `if use_llvm { #[cfg(feature
= "llvm")] ... }` where `use_llvm = backend == "llvm"` — so on `--backend=cranelift`
it never executes. The previous lane's own self-doubt on this point was correct.
Whether the same rule is needed on the **llvm**-backend path is a separate,
still-unmeasured question; it is out of scope for this cranelift reproducer and
is recorded here rather than silently dropped.

### Evidence paths

- gate verdict, RED baseline: `/mnt/data/tmp/gate_red.log`
- gate verdict, after theory #3: `/mnt/data/tmp/gate_fix.log`
- refuted patch: `/mnt/data/tmp/refuted_closures_structs_fix.patch`
- unmeasured llvm-path candidate: `/mnt/data/tmp/candidate_poll_unwrap.patch`

No code landed from this lane. The gate
`scripts/check/check-stage2-option-unwrap-not-stolen.shs` remains ADVISORY and
honestly RED, which is still the correct state.

### Addendum on the "fast oracle" — it speeds up REPRODUCTION, not fix-testing

A hello-world `native-build` on an already-admitted Stage 2 does reproduce in
seconds (confirmed here against a prebuilt Stage 2: `NB_RC=139` in ~0.1s of
phase output). That is a genuine improvement over a 13-minute Stage 3 run, and
the advisory gate's behavioural half already uses exactly this shape.

But it does **not** shorten the loop for testing a *compiler* fix, and the
distinction matters for planning the next attempt. The wrong-callee bind is
baked into the Stage-2 binary by the seed that built it, so changing the bind
means changing the seed and **rebuilding Stage 2** — the ~40-minute cycle this
lane paid twice. A prebuilt Stage 2 can only ever re-exhibit the defect it was
already built with.

What would actually shorten the fix loop is the *symbolic* half run against a
small fixture compiled **by the seed directly** (erased-optional `.unwrap()`
with `poll.spl` in the entry closure, then disassembled for the `Poll_dot_unwrap`
reference) — no Stage 2 in the path at all. That was attempted here and is
**blocked**: the seed `simple` binary refuses the command outright
(`error: pure-Simple tool 'native-build' unavailable; refusing Rust fallback`,
`driver/src/main.rs:230`), and the bootstrap drives Stage 2 through a separately
built `simple-native-all` binary rather than the seed `bin`. Establishing that
direct-from-seed fixture path is therefore the concrete prerequisite, and it is
the recommended first step of the next attempt — ahead of any further code
change.

## 2026-08-25 (lane-fast-oracle): the ~40-minute fix loop is replaced by a ~70-second one, and the blind early-return is localized

**Deliverable was the INSTRUMENT, not a fix. No compiler source was changed in this lane.**

### 1. The stated prerequisite dissolved: `refusing Rust fallback` is a cwd artifact, not a guard that must be bypassed

The previous lane recorded: *"The seed-direct fixture that would shorten it is
blocked by `refusing Rust fallback` (`driver/src/main.rs:230`); establishing it
is the next lane's prerequisite."*

That refusal is real but it is **not** a policy barrier to this fixture.
`native-build` is a `command_is_pure_simple_tool` name
(`driver/src/main.rs:287-305`), so when the Simple-app dispatch returns `None`
the driver refuses to fall back to Rust (`:228-233`). That dispatch resolves
`src/app/...` **relative to the current working directory**
(`resolve_app_path`). Measured 2026-08-25, same binary, same arguments, exit
status read directly into a variable on the line after the command:

| cwd | result |
|---|---|
| `test/fixture/erased_unwrap_oracle/` | `error: pure-Simple tool 'native-build' unavailable; refusing Rust fallback`, rc=1 |
| repo root | builds, rc=0 |

**The sanctioned way to exercise this path is to invoke the seed from the repo
root.** Nothing was disabled, weakened, allowlisted, or opted out of; the guard
is untouched and still fires everywhere it did before.

### 2. The fast oracle

`scripts/check/check-erased-receiver-unwrap-oracle.shs` — `--selftest` first and
fatal (9 classifier cases), verdict last on stdout, `PASS`/`FAIL`/`ERROR —
nothing was checked` with exits 0/1/2, 0 fixtures = ERROR, build half under
`timeout` with **rc=124 classified as a distinct HANG**, never a pass.

Measured runtime on this host:

| step | cold | warm |
|---|---|---|
| seed `cargo build --release --bin simple` | 3m03s | ~1-3 min incremental |
| one fixture `native-build --backend=cranelift` | — | 22-52s |
| whole gate, 3 fixtures + selftest | — | **70s** |

That replaces the ~40-minute Stage-2 bootstrap per candidate fix.

### 3. It discriminates: RED on `origin/main`, GREEN on a byte-identical shape

Measured on `origin/main` (`3e8c13f4149`), exit status read directly into a
variable on the line after the command: **`GATE_RC=1`, 81s**.

```
case poll_absent (reference):         observed=ERASED_UNWRAP=4242            expected=ERASED_UNWRAP=4242   verdict=OK
case xmod_main (reference):           observed=ERASED_UNWRAP=4242            expected=ERASED_UNWRAP=4242   verdict=OK
case hijack_control (control):        observed=CONTROL_PING=1                expected=CONTROL_PING=1       verdict=OK
case hijack_name_control (control):   observed=NAME_CONTROL=111              expected=NAME_CONTROL=111     verdict=OK
case hijack_erased (reference):       observed=ERASED_UNWRAP=4242            expected=ERASED_UNWRAP=4242   verdict=OK
case hijack_probe (probe):            observed=CONCRETE_UNWRAP=110153921397409 expected=CONCRETE_UNWRAP=111 verdict=THEFT
FAIL — 6 case(s) checked, .unwrap() mis-bound in: hijack_probe=THEFT
```

**The GREEN side is not hypothetical and needed no compiler change to
demonstrate.** `Aaa.unwrap_ctl()` and `Aaa.unwrap()` are the same class, the same
receiver variable, the same call-site shape, and byte-identical bodies
(`111`). They differ in exactly one character sequence: the method NAME.
`NAME_CONTROL=111` is correct; `CONCRETE_UNWRAP` is a pointer-shaped word. Two
further controls bracket it — `CONTROL_PING=1` proves ordinary user methods on
that receiver work at all, and three `ERASED_UNWRAP=4242` cases prove the
oracle reports OK when a bind IS correct. So a fix that flips the probe cannot
be confused with a fix that merely broke the fixture.

The classifier half is additionally mutation-proven by the `--selftest`
(14 cases, fatal, runs first): the incident's `ERASED_UNWRAP=0` shape, a
foreign-value shape, an observed text-valued shape, rc=139, rc=124, a
build failure, and a clean exit with **no sentinel at all** each read as their
own non-passing class, and a correct value with a non-zero exit is not OK.

**Gate polarity, stated so nobody "fixes" it:** `PASS` means the defect is gone.
This gate is therefore **ADVISORY and honestly RED on `origin/main`, which is the
correct state** — the same convention already recorded for
`check-stage2-option-unwrap-not-stolen.shs`. Promote it to mandatory when it
goes green.

### 3b. HONEST SCOPE LIMIT — what the probe does and does not pin

The RED probe is a **concrete-receiver** `.unwrap()` hijack: the receiver's type
is known and local, and a user-defined `unwrap` is nonetheless not called. That
is a defect in the same `.unwrap()` resolution chain, in the same file, and it is
RED in 81 seconds — but it is **NOT proven to be the same root cause** as the
Stage-2 erased-receiver -> `Poll.unwrap` theft. It is recorded as a related,
separately-filed defect
(`concrete_receiver_unwrap_returns_receiver_word_2026-08-25.md`), and this lane
does **not** claim that fixing one fixes the other.

All three erased-receiver fixtures still bind CORRECTLY in a small link, so the
exact Stage-2 theft is **not yet reproduced standalone**. The reason is given in
§4: the theft needs two or more `*_dot_unwrap` keys in `func_ids` at once, and a
small program supplies at most one. Closing that gap is the remaining work, and
until it is closed the oracle is a fast instrument for the `unwrap` binding chain
rather than a proven proxy for the Stage-2 blocker. Anyone using it to accept a
candidate fix must say which of the two it moved.

### 4. HYPOTHESIS (reconciles the prior evidence; NOT proven) — a blind early-return the discriminator cannot see

`closures_structs.rs:909-933`, inside `compile_method_call_static`:

```rust
if candidates.len() > 1 {
    let method_dot = format!("_dot_{}", method_part);
    for (cand_name, &cand_id) in &candidates {
        if let Some(dot_pos) = cand_name.rfind(&method_dot) {
            let prefix = &cand_name[..dot_pos];
            let type_name = prefix.rsplit("__").next().unwrap_or(prefix);
            if ctx.use_map.contains_key(type_name) {
                return Some(cand_id);        // <-- receiver-type-BLIND
            }
        }
    }
    // ... the same shape again over ctx.import_map, another `return Some(v)`
}
```

`candidates` is built at `:876-886` by filtering `ctx.func_ids` for **any** key
ending in `".unwrap"` / `"_dot_unwrap"`. The only receiver evidence consulted
before these two `return Some(...)` is whether the candidate's *extracted type
name* happens to be in `ctx.use_map` — a test on what the module IMPORTS, not on
what the receiver IS. In a Stage-2-sized link `Poll` is in `use_map`, so
`Poll_dot_unwrap` satisfies it.

**This is a hypothesis, not a proven site. What it does is reconcile the previous lane's evidence instead of contradicting it.**
That lane inferred the bind "does not flow through `compile_method_call_static`
at all" because the wired discriminator `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`
(call sites `:996`, `:1049`) produced zero output. Both report sites sit **after**
`:962`; the two returns above sit **before** it. A bind escaping at `:919` or
`:930` is invisible to that discriminator by construction, so the silence was
never evidence of absence. The same explains why the `:702` builtin-first gate
moved nothing: `:702` guards a different, earlier predicate
(`is_bare_builtin_collection_method`) that a bare `unwrap` on an erased receiver
does not satisfy.

**Precedent in the same block, for whoever fixes this:** `:836-843` already
early-returns `None` for bare `has` and bare `len`/`length`, both added after
this identical miscompile class, with the comment that the builtin fallback then
lowers them safely. `unwrap` has no such guard. That is a candidate shape — it is
**NOT applied or measured here**, and it must not be recorded as proven. Note it
is in the same file as, but a different site from, the already-refuted `:702`
theory.

**Why the current fixtures stay green, stated as the open item it is:** the theft
needs three conditions at once — (1) resolution must reach this fallback with a
bare `unwrap` so `type_qualifier == None`, (2) `candidates.len() > 1`, i.e. two
or more distinct `*_dot_unwrap` keys linked in, and (3) the stolen candidate's
type name must be in `use_map`. Every standalone fixture tried so far (this
lane's three, and the four in the earlier lanes) supplies at most one
`*_dot_unwrap`, so the `candidates.len() > 1` block is never entered. Closing
that gap is what turns this instrument RED.

### 5. A SEPARATE defect found while building the instrument — reported, not chased

In both `decoy_present.spl` and `xmod_main.spl`, a `.unwrap()` on a
**concretely-typed** class receiver returns a garbage word instead of its field:

```
DECOY=95601341756065    # decoy_present.spl, expected 7
DECOY=100373692547745   # xmod_main.spl,     expected 7
```

`BUILD_RC=0`, `RUN_RC=0` both times; the values look like heap pointers, i.e. the
callee appears to return the receiver rather than `self.v`. This is a **distinct**
miscompile from the erased-receiver theft (the receiver type here is known and
local) and is deliberately left uninvestigated in this lane. It is the reason the
oracle's GREEN criterion asserts `ERASED_UNWRAP=4242` specifically rather than
"the binary exited 0" — otherwise this second defect would contaminate verdicts.

### Invocation

```sh
cd <repo root>                 # required: outside it the seed refuses, see 1
sh scripts/check/check-erased-receiver-unwrap-oracle.shs --selftest
sh scripts/check/check-erased-receiver-unwrap-oracle.shs
sh scripts/check/check-erased-receiver-unwrap-oracle.shs --seed /path/to/simple
```

### 4b. CORRECTION to §4, from a parallel fixture search in the same lane — read this BEFORE acting on the §4 hypothesis

A parallel search inside this lane established three facts that **narrow §4 and
must not be omitted**. They were found by measurement, not argument.

1. **`--backend=cranelift` does not run the Rust seed's `closures_structs.rs`
   scan at all.** The `[cranelift-direct]` lines these fixtures emit come from
   the pure-Simple `src/compiler/70.backend/backend/cranelift_codegen_adapter.spl`;
   `grep -rn cranelift-direct src/compiler_rust` returns **zero** hits. With
   `SIMPLE_DEBUG_METHOD_DISPATCH=1` a fixture build emits 139
   `[CODEGEN-METHOD-STATIC]` lines and **all 139 name stdlib functions** — none
   from the fixture module. **So the §4 hypothesis about `closures_structs.rs:909-933`
   is NOT exercised by this oracle's fixtures, and the oracle is therefore not
   established as a proxy for whatever the Stage-2 bootstrap's Rust codegen does.**
   `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` printed **zero** lines in every fixture
   build, consistent with that.

2. **`.unwrap()` on a `T?` field or local never reaches
   `compile_method_call_static` in these fixtures.** Disassembly of
   `decoy_present.Holder.take` (`0x2fb1`): load `self.owner` -> indirect GOT call
   -> `test %rax,%rax` -> null branch prints an error and exits -> non-null branch
   calls **`rt_unwrap_or_self`** -> field load -> ret. `nm` shows **no
   `*_dot_unwrap` symbol in the binary at all**. The unwrap is inlined tag-check
   code plus a runtime call, which is exactly why no suffix scan fires and why
   `ERASED_UNWRAP=4242` is correct in every erased fixture.

3. **`func_ids` is per-MODULE, not per-program**, so a decoy and a victim cannot
   be made to co-occur in a fixture. The build logs 7 separate native units; the
   one call that provably does reach the scan (`file_read_text_at`'s bare
   `unwrap`, `src/lib/nogc_sync_mut/io/file_ops.spl:192`) is compiled in a unit
   that cannot see a user-module decoy. **This is a structural reason to expect
   that no standalone fixture can reproduce the Stage-2 erased-receiver theft** —
   it needs one large single-unit compilation, i.e. the self-hosted compiler
   itself. That retires a line of attack rather than leaving the next lane to
   re-spend a day on it.

Also confirmed: `closures_structs.rs:973-981` already returns `None` for
`unwrap` when `candidates.len() > 1`. The §4 `use_map` early-return at `:909-933`
runs **before** that guard, so it remains the only silent multi-candidate window
— but per fact 1, none of that is exercised here.

**Recommended next step, superseding "find a better fixture":** stop pursuing
standalone fixtures for the erased case. Instrument a real bootstrap /
self-hosted build with `SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1` and grep for
`[CODEGEN-ERASED-RECEIVER-BIND] ... 'unwrap'`, which enumerates every live
instance of the bind directly.

### 5b. The second defect is a BACKEND DIVERGENCE, which is stronger than §5 stated

The concrete-receiver hijack in §5 reproduces **only** under
`--backend=cranelift`. On the default backend the same source prints `111`/`222`
correctly. So a user-defined `fn unwrap()` on a class is shadowed by the builtin
(`rt_unwrap_or_self`, which returns the receiver — hence the pointer-shaped word)
on one backend and not the other. Filed in
`concrete_receiver_unwrap_returns_receiver_word_2026-08-25.md`.

---

## 2026-08-25 — BIND SITE FOUND AND NAMED (probe evidence, real self-host build)

### The site

`src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`, in
`compile_method_call_static` — the **single-candidate tail of the
name-suffix binder**. The pre-existing code comment at that tail already
described it exactly, and reported it without changing the pick:

> Reaching here means `type_qualifier` is None (a qualified lookup returned
> above) and `candidates.len() <= 1` (the >1 arms all returned). So this is
> EXACTLY the single-candidate erased-receiver bind that produced the known
> thefts, and it is silent today. Report it (default-off) without changing
> the pick.

Probe output from an instrumented **real** Stage-2 self-host compile
(`--backend=cranelift`, full `src/compiler` + `src/app` + `src/lib` closure):

```
[CODEGEN-ERASED-RECEIVER-BIND] in 'mir_pass_backend_decision_for_descriptor' bare method 'unwrap'(0 args) receiver_ty=Some(TypeId(3505)) bound by name-suffix alone to 'lib__nogc_async_mut__async__poll__Poll_dot_unwrap' (1 candidate(s)) — receiver type is NOT checked; if the receiver is not that type this is a silent miscall
[CODEGEN-ERASED-RECEIVER-BIND] in 'run_named_pass_with_record'   bare method 'unwrap'(0 args) receiver_ty=None bound by name-suffix alone to 'lib__nogc_async_mut__async__poll__Poll_dot_unwrap' (1 candidate(s)) — ...
[CODEGEN-ERASED-RECEIVER-BIND] in 'run_pass_on_module_checked'   bare method 'unwrap'(0 args) receiver_ty=None bound by name-suffix alone to 'lib__nogc_async_mut__async__poll__Poll_dot_unwrap' (1 candidate(s)) — ...
```

The victim functions are MIR-pass driver functions, consistent with the
recorded Stage 3 SEGV at `aot:lower_to_mir`.

### Why every earlier search missed it

An Option/Result-family guard ALREADY existed immediately above, and it was
correct in intent — but it was written as `candidates.len() > 1`.
`func_ids` is **per-module**. In a module that merely USES `.unwrap()`, the
only `*_dot_unwrap` symbol in scope is whichever library defined one — in the
self-host closure, `nogc_async_mut/async/poll.spl`'s `Poll.unwrap`. That
leaves exactly **ONE** candidate, so the `> 1` guard never fired and control
fell into the single-candidate tail.

This inverts an earlier reading. The per-module nature of `func_ids` was
previously cited as evidence that decoy and victim "cannot co-occur" and
therefore that this path was not the site. In fact per-module `func_ids` is
the *mechanism*: it is precisely what reduces the candidate set to one and
slips the theft under a guard that only inspects ambiguous sets. It also
explains why **no standalone fixture can reproduce this** — a small
single-module build never has the decoy in scope at all.

### Claims from the previous investigation that measurement REFUTED

- **"`.unwrap()` on a `T?` never becomes a `MethodCallStatic`."** Contradicted
  in the real build: the bind flows through `compile_method_call_static`. That
  claim was fixture-derived, and fixtures cannot reproduce this defect.
- **The `calls.rs` / `build_import_map` first-wins route** (the "current
  direction" hypothesis, and this lane's own initial hypothesis) is **refuted
  by measurement**. Instrumenting every rung of the `calls.rs` import ladder
  and the `imports.rs` ambiguous-first-wins insertion produced, across a full
  self-host compile: **zero** `imports.rs:ambiguous_first_wins` lines for
  `unwrap` (i.e. `unwrap` was never ambiguous in the import map at all), and
  exactly one `calls.rs:import_ladder` line — for `expr_force_unwrap`, an
  unrelated function that merely contains the substring, resolved correctly
  via `use_map_direct`. The import map is not involved.

### The fix

Change that guard from `candidates.len() > 1` to `!candidates.is_empty()`, so
Option/Result-family names are refused by the suffix binder at **every**
candidate count.

Returning `None` here is a **ROUTE, not a refusal** — the constraint that any
fix must reach the runtime builtin rather than leave a raw name to become a
link-time import (which this repo has already seen turn into a NULL GOT and
the same rc=139 by a different cause). Verified by reading the fallthrough:
`None` drops into the cross-module branch, which **already** excludes this
same name family from its bare `import_map` fallback, so resolution reaches
`try_compile_builtin_method_call`, which maps `unwrap` → `rt_unwrap_or_trap`
(correct Some/Ok-payload-or-trap semantics for any enum receiver). No raw name
survives to link. Qualified lookups are untouched — they return earlier.

### Sibling defect found by the same probe (NOT fixed here)

The same single-candidate tail also steals `kind`:

```
[CODEGEN-ERASED-RECEIVER-BIND] in 'register_block' bare method 'kind'(0 args) receiver_ty=Some(TypeId(14)) bound by name-suffix alone to 'compiler__blocks__blocks__builtin_blocks_data__RegexBlockDef_dot_kind' (1 candidate(s)) — ...
[CODEGEN-ERASED-RECEIVER-BIND] in 'with_block'     bare method 'kind'(0 args) ... same target ...
```

Deliberately NOT covered by this fix: `kind` is not an Option/Result-family
name and has **no runtime builtin to route to**, so the same one-line
widening would turn a wrong-callee bug into an unresolved-symbol bug. Needs
its own remedy (receiver-type check, or a vtable switch). Filed separately.

### Gate

`scripts/check/check-erased-receiver-family-not-suffix-bound.shs` — fail-closed,
`--selftest` first and fatal (5 fixtures), verdict last, `PASS n>0` / `FAIL` /
`ERROR`. Mutation-tested both directions against the REAL pre-fix source (not a
synthetic fixture): PASS on the fixed tree, FAIL naming the mechanism on
`HEAD`'s content.

It pins the SOURCE INVARIANT rather than running a build, because no fixture
can reproduce the defect (see above) and a real reproduction costs a ~40 min
self-host compile. It is explicitly **not** a claim that Stage 2 is green —
that is measured separately by `check-stage2-option-unwrap-not-stolen.shs`.

---

## 2026-08-25 — MEASURED: PARTIAL FIX, MECHANISM CONFIRMED, SECOND SITE OPEN

This is the entry that should hold. The two earlier rewrites of this record
claimed things before measuring them; everything below is a number read off a
binary or a verbatim verdict line, and the places where a prediction was
**wrong** are kept rather than quietly corrected.

### Outcome in one line

The guard fix is **real and correct but insufficient**. It converts 34 call
sites from the wrong user method to the runtime builtin, exactly conserved,
regressing nothing — and the advisory Stage-2 gate stays **RED**, because the
sites the gate counts come from a **second, independent bind site** that this
binder never reaches. Filed separately as
`poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25.md`.

### The differential (the decisive evidence)

Per-function callee counts by disassembly, pre-fix vs post-fix Stage 2, both
built from this same base by the same replayed bootstrap argv:

| function | `Poll_dot_unwrap` | `rt_unwrap_or_trap` |
|---|---|---|
| `run_named_pass_with_record` | 3 → **1** | 0 → **2** |
| `run_pass_on_module_checked` | 3 → **1** | 0 → **2** |
| `lower_and_check_impl` (what the gate counts) | 4 → **4** | 0 → **0** |
| **whole binary** | 307 → **272** (−35) | 117 → **151** (+34) |

**34 sites moved** from the wrong callee to the builtin: `rt_unwrap_or_trap`
gains exactly +34, and the two probe-named functions account for the change.
The whole-binary `Poll_dot_unwrap` delta is −35 rather than −34 because one
further reference, in the unrelated `compiler__types__dim_constraints__DimSolver_dot_solve_constraint`,
is present in an instrumented build of the same fix and absent in the landed
one — build variance between two compiles, not part of this fix. The
load-bearing figure is the **+34 builtin calls** and the per-function rows
above, which are byte-identical across both builds. The two functions the original probe named
were fixed precisely as predicted, so the fix's routing argument (`None` →
cross-module branch → `try_compile_builtin_method_call` → `rt_unwrap_or_trap`)
is **measured true**, not merely argued. `lower_and_check_impl` is untouched.

### Gate results, verbatim, both directions

Negative control — pre-fix Stage 2 (`simple.rejected`, a real bootstrap
artifact from this same base):

```
FAIL -- 2 check(s) performed: 4 Simple '*_dot_unwrap' call site(s) inside
lower_and_check_impl -- an Option unwrap bound to a user method instead of the
runtime builtin; hello world emitted
E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED (rc=139);
```

Post-fix Stage 2: **byte-identical verdict line**. Neither number moved. That
is what the differential explains: the gate's function is not this binder's.

### A prediction of this lane's that measurement REFUTED

Before running the differential, this lane wrote down that the likely
explanation was "the fix is a no-op and its safety comment is false — `None`
probably falls through to a bare `import_map` lookup that still resolves
`Poll_dot_unwrap`". **That guess was wrong.** The differential shows the
routing works exactly as the comment claims. The guess is recorded because it
was written before the check, and deleting it would repeat this record's
existing failure mode.

### Liveness caveat — do not over-read the probe

The new guard returns `None` **above** the single-candidate reporter, so the
probe reading `unwrap=0` proves only that **the guard fired**. It is *not*
independent evidence that the emitted callee changed. The disassembly is what
proves that. The probe was separately shown live (64 bind lines, 12+ other
methods still suffix-bound — `with_note`, `build`, `map`, `kind`,
`lower_const`, `add_port`, …), so its silence on `unwrap` is a real change and
not a broken instrument; but liveness and outcome are different claims.

### Still refuted (re-confirmed on this run)

The `calls.rs` import-ladder / `imports.rs` ambiguous-first-wins hypothesis.
Instrumented across the full self-host compile, the ladder probe fired exactly
**twice**, both for the unrelated `expr_force_unwrap`, resolved correctly via
`use_map_direct`. The import map is not involved. (That instrumentation was
stripped before landing; its findings live here.)

### Seed provenance — why an earlier "failed" Stage 2 was never evidence

An earlier bootstrap in this lane produced
`build/bootstrap/.../stage2/x86_64-unknown-linux-gnu/simple.rejected` with
`status=fail`. That artifact was built from seed `de9cfc3e…`, whereas the
fixed seed is `6f448893…` — **not byte-identical**, so the rejected Stage 2
predates this fix and its sanity FAIL says nothing about it. It is, however, a
perfect negative control, and is used as one above.

### Scope note on the gate's behavioural half

`check-stage2-option-unwrap-not-stolen.shs` runs its hello-world check through
`native-build` on the **script default backend**, not the cranelift path this
defect reproduces on. The symbolic half (disassembly) is backend-independent
and is the half that carries the mechanism claim.

### Unrelated but load-bearing for another lane: this base is CLEAN of the
### `cannot convert array to int` native-build regression

Measured here because a parallel lane is bisecting that regression across ~613
commits and needs brackets. At commit **`4d11699bc5b`**, using the **pre-fix**
seed (so the result is a property of the base, not of this fix):

```
hello world native-build:  NATIVE_BUILD_RC=0
                           binary produced, ran, printed "hello"
                           array_to_int_signature=0
```

So the regression is **absent at `4d11699bc5b`**. Note also that this commit
does **not** contain `37d046a71b1`, the suspected lead. Citable as a known-good
point.

---

## 2026-08-25 — both `Poll.unwrap` bind sites are now fixed; the rc=139 that remains is a DIFFERENT defect

Stated narrowly, because this record has twice been rewritten for claiming more
than was measured. **No self-hosted end-to-end claim is made here, and Stage 3
was deliberately not attempted.**

What is measured, on a Stage 2 built from `c6041e04d4e` + the second-site fix by
the sanctioned bootstrap invocation (757 compiled, 0 failed), by symbol-aware
disassembly:

- `lower_and_check_impl`: `Poll_dot_unwrap` **4 → 0**; observed replacement callee
  `rt_enum_payload` ×6.
- whole binary: `Poll_dot_unwrap` **272 → 0** (the symbol is no longer defined).
- `E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` occurrences: **0**.

So the malformed-surfaces mechanism described in this record — `Poll.unwrap`
returning 0 for a non-`Poll` receiver, 0 being `< 4096`, the formation guard
rejecting a payload that is really a live enum — **is fixed**. The second site
was the cross-module resolution ladder in `compile_method_call_static`, whose
first three steps lacked the Option/Result-family exclusion that its fourth step
had. Detail:
`poll_unwrap_second_bind_site_lower_and_check_impl_2026-08-25.md`.

**What is NOT resolved.** Hello world on that Stage 2 still SEGVs (rc=139), now
in `native_compile` (step 5/6), after HIR lowering, borrow-check, async
processing, MIR optimisation, AOP weaving and the native cache have all
completed. No pre-fix build ever reached that phase, so this is **newly exposed,
not newly introduced** — and it is not evidence that the unwrap fix failed.
Filed separately as `stage2_native_compile_segv_after_unwrap_fix_2026-08-25.md`.

Whether that downstream crash shares a root cause with this record's Stage-3
`aot:lower_to_mir` death is **unknown**: same rc, different phase, no evidence
either way. It is deliberately not asserted.
