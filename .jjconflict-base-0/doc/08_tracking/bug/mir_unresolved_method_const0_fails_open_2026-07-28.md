# Unresolved method call fails OPEN as const-0 while its sibling sites fail CLOSED via rt_panic

- **Status:** OPEN
- **Filed:** 2026-07-28
- **Class:** silent-null / fail-open (wrong-answer risk)
- **Tree measured:** origin/main `bce219fbec1`
- **Related:** Task #145
- **Site:** `src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl:2486-2500`

## Question this answers

Does any configuration let the `const-0 placeholder (silent-null risk, Task #145)`
warning fire WITHOUT an accompanying hard error? A peer observed the warning
firing three times alongside a fatal `MIR lowering error: unresolved method
call: index_of` (rc=1, no binary), which shows only that *in that lane* the
placeholder comes with a hard error.

Answer: **yes, a configuration class exists** — and the defect is sharper than
"sometimes not fatal". It is an asymmetry between three sibling sites.

## The asymmetry (this is the finding)

All three sites handle "construct has no native lowering". `self.error(...)`
only COLLECTS into `MirLowering.errors`; whether that becomes fatal depends on
the consuming pipeline. Two sites defend against that; one does not.

| Site | Compile-time | Emitted MIR | Behaviour in a lane that drops `MirLowering.errors` |
|---|---|---|---|
| `mir_lowering_stmts.spl:~1857` for-in over non-array (#143) | `self.error` | `self.error` + **`rt_panic(msg)`** | binary aborts at runtime with a clear message — FAIL CLOSED |
| `expr_dispatch.spl:~2866` match guards (B5b Phase 2) | `self.error` | `self.error` + **`rt_panic(msg)`** | binary aborts at runtime with a clear message — FAIL CLOSED |
| `method_calls_literals.spl:2494` unresolved method call | `self.error` + a `print` WARNING | `self.error` + **`emit_const(temp, Int(0))`**, NO `rt_panic` | binary is produced; the call silently evaluates to **0** at runtime — **FAIL OPEN** |

The first two explicitly document the reasoning in-tree: emit `rt_panic` "so
pipelines that drop MirLowering.errors (e.g. the native-build worker's
lower_to_mir) still abort with a clear diagnostic". The third site does not do
this, so it is the one that can ship a wrong answer.

## Measured lane comparison (same probe)

Independently measured on `b410e53a7a2`, confirming the mechanism:

| lane | const-0 warnings | hard errors | rc |
|---|---|---|---|
| `native-build` default | 3 | 3 | 1 — loud |
| `SIMPLE_BOOTSTRAP=1` | 3 | **0** | 1 |

The bootstrap lane demonstrably swallows the hard error, so the configuration
question is settled affirmatively: at least one lane drops it. That bootstrap
run then died before codegen for an unrelated reason (`missing argument for
parameter 'span'`), so the *mechanism* is confirmed but an end-to-end exit-0
wrong value is still not demonstrated. See "What remains unproven" below.

## Scale of the class

`self.error()` is defined at `_MirLowering/asm_and_targets.spl:264` and its
body is a single `self.errors.push(...)` — it collects, it never raises. So
every caller that assumes it is terminal is a potential silent-data-loss site.

- **128** `self.error(` call sites across `src/compiler/**`, of which **62**
  are in the MIR lowering layer (`50.mir`): `expr_dispatch.spl` 20,
  `mir_lowering_stmts.spl` 13, `switch_operators_calls.spl` 9,
  `asm_and_targets.spl` 9, `method_calls_literals.spl` 4, `module_lowering.spl`
  3, `function_lowering.spl` 2, `literals.spl` 1, `mir_lowering_ml.spl` 1.
- Only **3 files** contain any `rt_panic` fail-closed mitigation at all.

So the fail-closed pattern is the rare exception, not the rule. Reporting the
count before proposing a class-wide change, as asked: making `self.error()`
raise would be a 128-call-site behavioural change and must not be done blind —
the narrower and safer first move is the single-site `rt_panic` fix below, with
a separate decision on whether lanes should stop dropping the list.

## Which lanes drop the errors

Corroborated by three independent in-tree comments plus the actual plumbing:

- Lanes that DO read `lw.errors` and turn it fatal:
  `_MirLowering/bootstrap_globals.spl:512` and `:619`, and driver_pipeline.
  This is the lane the peer measured — hence rc=1 and no binary.
- Lanes that DO NOT: `method_calls_literals.spl:2487` states "the bootstrap
  lane (driver_bootstrap.spl reads ctx.errors, never MirLowering.errors) and
  the native-build worker drop the list", and `mir_lowering_stmts.spl:1781`
  and `expr_dispatch.spl:2866` independently name "the native-build worker's
  lower_to_mir" as a pipeline that drops them.

So the fatal-vs-silent outcome is a property of the consuming pipeline, not of
the placeholder site. The placeholder site is what decides whether the silent
case produces a wrong answer or an abort.

## Why the WARNING print is not sufficient mitigation

The `print` at :2494 was added to stop this being fully silent, and it does
make the compile-time event observable. But it is `print` (stdout), not
`eprint`, and it does not change the exit status. A pipeline that drops
`MirLowering.errors` still exits 0 and still produces a binary. Any automated
gate keying on exit code or stderr — which is most of them — passes. The
runtime wrong answer (0) is unaffected by a compile-time print.

## Contained fix

Make the unresolved-method-call site match its two siblings: emit an
`rt_panic(msg)` call carrying the same message before the placeholder, keeping
the `emit_const(temp, Int(0))` def afterwards. The const-0 def must stay — the
in-tree comment records that returning an undefined temp produces a
use-before-def local (NULL `llvm::Value*` → ICmp SIGSEGV in llvm-lib) — but
with an `rt_panic` ahead of it the placeholder value is never observed, so the
lane fails closed like the other two instead of returning 0.

NOT applied here: this is the pure-Simple compiler, and it could not be
executed from this session to verify (see below). It should be landed by
someone who can run the native-build lane.

## What remains unproven

An end-to-end silent wrong answer — **exit 0 with a wrong value** — is NOT yet
demonstrated. Two attempts have now stopped short:

1. The bootstrap lane swallows the hard error (measured above) but that run
   died before codegen on an unrelated `missing argument for parameter 'span'`.
2. This session could not execute the pure-Simple lane at all: the deployed
   `bin/simple` is a Rust seed (built 2026-07-28 05:45, contains no
   `rt_index_of`, not linked against LLVM), so `src/compiler/50.mir/` is not
   reachable through it, and a `native-build` attempt exceeded a 2-minute
   budget without completing.

The missing step is a consumer where the placeholder survives to a result.
Note the const-0 site returns an `i64` temp, so the natural probe is an
unresolved method in **value** position whose result is printed or compared —
not a statement-position call, whose placeholder is discarded and would show
nothing even if the lane were fully silent.

## Related stale-doc correction

`doc/08_tracking/bug/native_string_methods_unresolved_in_mir_2026-07-17.md`
claimed the Task #145 guard "convert[s] unresolved calls into hard errors
rather than silently emitting a placeholder". That is false — the code does not
do that — and it is exactly the sentence that would be quoted to close this as
a non-issue. **It has already been corrected in place** by a parallel lane,
which retained the original wording verbatim inside the correction so the claim
is not silently deleted. No further edit to that doc is needed; this doc does
not duplicate it.

Caveat carried forward: the in-tree comment naming the native-build worker as a
dropper may be partly stale, since that worker currently propagates (it is the
lane that produced rc=1 above). The dropping lane confirmed by measurement is
the bootstrap one.

## 2026-08-08: the native-build lane DOES reach codegen, at scale (3,629 / 538)

The step recorded above as missing — "a consumer where the placeholder survives
to a result" — is now partly closed. It was never reached before because Stage 3
died in HIR; with the BGS1 fix landed (`91bb4437a83`) Stage 3 advances through
`monomorphize` into real LLVM codegen, and that run is the first observation of
this defect past the point both earlier attempts stopped at.

Lane: `build/cyc/run_stage3.sh` in the pinned worktree
`/home/ormastes/dev/simple-s3bisect` (pin `22dd136685d`, clean, an ancestor of
`origin/main`), i.e. the **native-build bootstrap lane** under
`SIMPLE_BOOTSTRAP=1` — a stage2-simple compiling `src/app/cli/bootstrap_main.spl`.

Measured on that run's `stage3.log` (16.3 MB):

| quantity | value |
|---|---|
| `const-0 placeholder` substitutions | **3,629** |
| distinct unresolved names | **538** |
| of those, constructor/enum-variant-shaped (leading capital) | 177 |
| of those, method-shaped (leading lowercase) | 361 |
| hard `^error:` lines | **0** |
| `progress.events` terminal state | `failed=0`, `tasks_done=4/6`, reached `phase=monomorphize` then LLVM codegen |

The count is **stable across five independent runs** — FIX1RUN 3,575,
S3RUN_FIX1 3,613, S3RUN12 3,629, S3RUN_LONG 3,629 — each with **0** hard errors.
So this is a longstanding property of the lane, not a regression introduced by
the BGS1 fix, and the invariance across runs is itself the attribution evidence.

The affected names are not exotic edge cases. The top of the census is
`substring` 261, `merge` 248, `slice` 242, `unwrap` 217, `new` 95, `clear` 89,
`check` 85, `concat` 82 — core text, collection and Option/Result operations —
alongside 177 constructor-shaped names including `Named`, `Const`, `Call`,
`Int`, `CodegenError`, `RuntimeError` and `Success`. Every one of these is an
`i64` const-0 substituted for a real value in the compiler's own code.

This upgrades two of the statuses below:

- The in-tree comment naming "the native-build worker's `lower_to_mir`" as a
  dropping lane is **corroborated by measurement**, not stale. The caveat
  carried forward at the end of "Related stale-doc correction" — that the
  worker "currently propagates" — is wrong for this configuration: here it
  drops 3,629 collected errors and still emits objects.
- "Neither attempt reached codegen" no longer holds. This run emitted LLVM IR,
  ran `llc`, and wrote a 1.16 MB object
  (`stage3-simple.app.cli.bootstrap_main.o`, 209 KB `.text`).

### Still NOT proven, and why

An **executed** wrong value remains undemonstrated, because the binary Stage 3
emits cannot execute anything.

Stage 3 now **runs to completion and exits 0** — `STAGE3_EXIT=0`, `WALL=1202s`
against a 3600s budget, peak RSS 10.7 GB — and the artifact it produces at `-o`
is a vacuous 22,896-byte `stage3-simple`: 14 KB `.text`, 42 defined functions,
22 dynamic symbols all libc. Its `main` calls `spl_init_args`,
`__simple_runtime_init`, five stray `__module_init_*_dynamic` stubs, then
`__simple_main` — which reads uninitialised stack and returns — then
`__simple_runtime_shutdown`. There is no `dlopen`/`dlsym`, so this is not a
dynload launcher despite `--mode dynload`; it is a fully linked program that
does nothing. It prints nothing on `--version` and exits 0.

Meanwhile the real object is written next to it and **never linked in**:
`stage3-simple.app.cli.bootstrap_main.o`, 1.16 MB, 209 KB `.text`, **5,869**
defined symbols including `bootstrap_compile_backend_from_args` and
`app.io.cli_ops.cli_handle_compile`.

This is reproducible and deterministic, not an interrupted-run artifact — three
runs of materially different durations produced a **byte-identical** output
(md5 `401436362a7c`): S3RUN12 529s, S3RUN_LONG 948s, S3RUN_3600 1202s/exit 0.
The differing wall times rule out the harness budget as the cause.

So the placeholder survives to codegen and to an object file, but the artifact
that would exhibit the wrong value at runtime was never assembled. That
vacuous-link failure is a *separate* defect from this one and must not be
folded into it — though note that `set_bootstrap_entry_mir`,
`emit_bootstrap_statics` and `lower_runtime_module_initializers` all appear in
the const-0 census above, so a causal link between the two is **plausible and
untested**, and is offered here strictly as a hypothesis, not a diagnosis.

Consequence for anyone gating on this lane: `0 error: lines` and `failed=0`
from a Stage 3 native-build run are **fail-open readings**, not evidence of a
clean compile. The honest gate is the placeholder census
(`grep -c 'const-0 placeholder'`), which no current automated check reads.

## Evidence status

Method rules applied, each of which has caught a separate error in this
investigation:

- **Which tree:** `origin/main` blobs (`bce219fbec1`), never a working copy —
  the shared WC is behind and contested.
- **Which compiler:** the **pure-Simple** compiler (`src/compiler/50.mir/`).
  This diagnostic has zero hits in the Rust seed; they are different codebases.
- **Which symbol:** emitted symbols, not method names.
- **A collected error is not a raised error:** `self.error()` pushes to a list.

Status:

- **PROVED (source-level, `origin/main` blobs):** the three-way asymmetry —
  two sibling sites emit `rt_panic` and fail closed, the unresolved-method site
  emits only a `print` + const-0 and fails open; `self.error()` collects rather
  than raises; the 128 / 62 / 3 call-site counts.
- **PROVED (measured by a peer on `b410e53a7a2`):** the bootstrap lane produces
  3 const-0 warnings and **0** hard errors, so at least one lane drops the
  collected list.
- **NOT PROVED (open):** an end-to-end exit-0-with-a-wrong-value run. Neither
  attempt reached codegen. Until someone demonstrates it, the fail-open path is
  a strongly-evidenced mechanism, not an observed wrong answer.
  **Superseded in part on 2026-08-08** — see the section above: codegen IS now
  reached (3,629 substitutions, 538 names, 0 hard errors, object emitted), so
  only the final "executed wrong value" step is still open, and it is blocked
  by a separate vacuous-link defect rather than by this one.

## 2026-08-16: W1.5 C4 fail-fast plumbing evidence and contained repair

The immutable Phase 4 mixed-tail W1.5 receipt records a pure-Simple Stage 2
launch with `SIMPLE_NO_STUB_FALLBACK=1` that emitted **5,257** unresolved-method
const-zero placeholder warnings before failing later at LLVM text assembly.
The command and terminal evidence are retained under
`build/native_probe/p4_mixed_tail_probe_s2new_20260816/`.

This is not an environment-propagation failure. The frozen resolved command
contains the strict variable, but its existing compiler consumer guards
SimpleOS link-time fabricated symbol bodies. The unresolved MIR arm did not
consult it: it recorded a non-fatal `MirError`, emitted `rt_panic` plus the
unreachable const definition, and continued. The bootstrap flat-module loop
also checked fatal errors only before lowering function bodies, then appended
each partially lowered function without a post-function rejection.

Cycle 1 contains the repair at the two owning seams:

- the unresolved-method arm now records the condition with `error_fatal` while
  retaining `rt_panic` and the unreachable const definition needed to keep
  partial MIR structurally defined;
- the flat bootstrap function loop rejects newly recorded fatal errors and
  exits before adding that function to the shared accumulator.

The source-contract coverage is traced to `REQ-BOOT-STAGE-001` in
`test/01_unit/compiler/driver/bootstrap_flat_nonentry_globals_source_spec.spl`
and
`test/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.spl`.
Execution verification remains pending the separately authorized focused test
cycle. This C4 guard defect is independent of the W1.5 C3 undefined-SSA-local
LLVM-text defect: the repair does not touch MIR-to-LLVM call destinations and
will make C3 temporarily unobservable by rejecting invalid MIR earlier, not
claim to fix it.
