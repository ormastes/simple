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

## 2026-08-03 Stage 4 ownership claim

Claimed by `codex/stage4-x86-phase4` at source revision `69757e3aae7` before
production edits. A retained Stage-3 bootstrap-flat native build now closes the
previous evidence gap:

- an unsupported `Future<T>.map<U>` call emitted the Task #145 warning;
- native-build nevertheless reported `6 compiled, 0 failed` and exited 0;
- the linked executable exited 1 with empty stdout/stderr rather than producing
  a compile-time diagnostic.

The current unresolved-method site does emit `rt_panic`, so this is no longer
the exact historical const-0 runtime behavior. The architectural defect remains:
`bootstrap_lower_flat_hir_module_to_mir` lowers every function with a local
`MirLowering`, then discards its function-lowering errors. Its two sibling
bootstrap-global/extra paths have the same post-function gap. The normal driver
collects those errors and already classifies `unresolved method call:` as fatal.

The owned repair is therefore narrower than making all `self.error` calls fatal:

1. mark the unresolved-method site explicitly with `error_fatal`;
2. after function lowering, make every bootstrap flat/global/extra helper scan
   `MirError.fatal`, emit the diagnostic on stderr, and stop before codegen;
3. retain advisory MIR diagnostics as non-fatal;
4. prove an unsupported method is rejected during native-build while a supported
   non-generic method and the Stage 4 Future declaration-containment fixture
   still compile.

Retained pre-fix evidence:
`build/focused/stage4-nogc-async-future/contract-attempt3-negative.log`,
`.stdout`, and `.stderr`.

### Repair in progress

The owned pure-Simple repair now marks the terminal unresolved-method
diagnostic fatal and drains fatal `MirLowering.errors` in all three
bootstrap flat/global/extra function-lowering helpers. Advisory diagnostics
remain non-fatal. A source regression asserts the fatal site and propagation
boundaries.

The retained Stage 3 compiler necessarily still embeds the old lowering. It
accepted the fresh negative fixture and produced an executable that segfaulted
with exit 139 and empty output. Therefore compile-time rejection is not yet
claimed; it must be proven with the rebuilt Stage 4 candidate.
