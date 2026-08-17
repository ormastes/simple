# if-expression with a constant-false condition binds the DEAD branch's `[]`

> ## RETIRED 2026-08-17 by EXECUTION + source (worker W5)
>
> Two independent confirmations:
> 1. **The construct is correct.** An if-EXPRESSION whose condition is a `val`
>    initialised to literal `false`, with `[]` in the dead branch, binds the LIVE
>    branch under both engines (`I1_len=3`, and 3 for the mirrored/true-branch and
>    non-empty-dead-branch shapes too).
> 2. **The offending site no longer exists.** `grep -n native_all_replaces_c_runtime
>    src/compiler/70.backend/backend/llvm_native_link.spl` returns NOTHING -- the
>    `val native_all_replaces_c_runtime = false` if-expression quoted in this doc is
>    gone from `link_llvm_native`.
>
> Note the pre-existing "re-verified 2026-08-17 by source inspection" stamp above
> pointed at that same file while the symbol was already absent -- another instance
> of that stamp being unreliable.
>
> Regression guard: `test/01_unit/engine_divergence/check-engine-divergence-probes.shs`.


- **Date:** 2026-08-06
- Status: **CLOSED 2026-08-17 (retired — did not reproduce; call site no longer exists)**
- The earlier "Status re-verified 2026-08-17 by source inspection (triage shard 01)"
  stamp on this row was WRONG. It pointed at
  `src/compiler/70.backend/backend/llvm_native_link.spl` as still carrying the
  dead branch. It does not — see the closure section at the bottom of this file
  for the grep. Do not trust that stamp; it was re-checked by grep and by
  execution and failed on both axes.
- **Severity:** Blocker (this was Stage 3 self-host blocker #8)
- **Engine:** self-hosted stage2 binary (native, LLVM backend), not the seed

## Symptom

Stage 3 `native-build` of `src/app/cli/bootstrap_main.spl` died at LINK with
exactly three undefined symbols:

```
ld.lld: error: undefined symbol: spl_init_args
ld.lld: error: undefined symbol: __simple_runtime_init
ld.lld: error: undefined symbol: __simple_runtime_shutdown
>>> referenced by simple_entry.c ... simple_entry.o:(main)
```

## What was actually wrong

`link_llvm_native` bound its runtime object list through an if-EXPRESSION whose
condition was a `val` initialised to the literal `false`:

```
val native_all_replaces_c_runtime = false
val runtime_objects = if native_all_replaces_c_runtime:
    []
else:
    ... compile_runtime_objects(...) -> paths
```

Observed on the failing run (evidence captured with a `SIMPLE_CC` logging
wrapper, `build/cyc/ARGV1`):

1. All 23 runtime objects WERE compiled — `t3/simple_rt_<pid>_*.o` existed
   mid-run, and cc was invoked 23 times for them. So the ELSE branch ran.
2. The final `cc` link line carried **only two** objects: the user object and
   the generated entry shim. None of the 23 runtime objects appeared.
3. After the failed link the 23 objects were **gone** from `t3`.

So the ELSE branch ran and produced 23 objects, and the object-collection loop
contributed zero of them. Who removed the objects afterwards was not traced:
`cleanup_runtime_objects` on an empty list is a no-op, so their disappearance
*suggests* the value was intact at that later read, but that was inferred, not
observed. Treat "the same val read empty at one site and full at another" as an
unconfirmed hypothesis.

Only three symbols were reported because `-Wl,--gc-sections` is on the link
line: lld does not report undefined references from sections it garbage
collects, and every other runtime reference (e.g. `rt_panic`) sat in dead code.
Verified independently with a 3-file lld fixture. This is why the failure looked
like "the entry shims are missing" rather than "the whole C runtime is missing".

## Why it was input-dependent

A trivial program built through the identical code path, env, and bundle linked
green with 25 objects on the cc line (`[LLVM-LINK] got 23 runtime objects`,
`total objects: 25`). Same stage2 binary, same machine code — only the compiled
input differed. Enabling `SIMPLE_COMPILER_TRACE=1` did not change the outcome
either way, so it is not a trace-induced Heisenbug.

## Not yet isolated

Which lowering stage drops the binding (HIR if-expression value, MIR phi, or the
LLVM slot assignment for an untyped `val` bound to a branch value) is not
isolated. Note the family already fixed today — untyped locals reading the wrong
slot (`92d059e5ce7`, `dc8186a0e71`, `8bd2820f3e3`) — this looks like the same
class: `runtime_objects` had no type annotation.

## Verification of the linker-side fix

RED (twice, pre-fix stage2): `build/cyc/FIX7` and `build/cyc/ARGV1` — both ended
with exactly those three undefined symbols, and the `SIMPLE_CC` wrapper captured
a link line carrying **2** objects (user object + entry shim).

GREEN: the preserved Stage 3 user object from the failing run
(`FIX7/stage3-simple.app.cli.bootstrap_main.o`) relinked against the 23 runtime
objects the fixed code path supplies, using the identical cc arguments, links
cleanly. Provider check on the result (`--allow-multiple-definition` is on the
line, so counts matter):

```
spl_init_args: T=1 W=0
__simple_runtime_init: T=1 W=0
__simple_runtime_shutdown: T=1 W=0
rt_install_crash_handler present   # runtime.c's spl_init_args won, not a stub
__simple_runtime_shutdown -> call fflush; jmp fflush   # not a bare ret
```

Sabotage: relinking the same object with `runtime.o` and `runtime_native.o`
removed from the object set brings back **exactly** those three undefined
symbols and nothing else; restoring them relinks clean.

A whole-cycle GREEN through the compiler itself was NOT reached. A stage2
rebuilt from the bisect worktree dies one phase earlier, in `llc`, on
`%t3209 = icmp ne double %l39, 0` (an integer truthiness compare emitted against
a double). That worktree carries uncommitted in-flight edits from a concurrent
lane in `_MirToLlvm/core_codegen.spl` (2 lines) and `llvm_ir_builder.spl` (20
lines) that are not in `origin/main`; those files were deliberately not touched,
and `origin/main`'s versions of them were not tested against this failure.

## No self-host: the Stage 3 entry is vacuous

Even with the link fixed, the Stage 3 object does not yield a working compiler.
Its `__simple_main` is `mov -0x48(%rsp),%rax; ret` — it reads an uninitialised
stack slot and returns, calling nothing. All 5,674 other `T` functions in the
object are therefore unreachable and `--gc-sections` strips them, giving a 28 KB
binary that prints nothing and exits 0 for `--version`, `build --help`, and a
bare invocation. `nm` on the object shows no `app.cli.bootstrap_main.main`-style
entry body at all, so the entry module's `main` never reached the object under a
callable name. That is the next blocker and it is a lowering/entry-wiring
defect, not a link defect.

## Repro shape

Not reduced to a minimal case yet; it only reproduces on the full Stage 3
self-host compile. A reduction attempt should start from an untyped `val` bound
to an if-expression whose dead branch is a bare `[]`, in a function with many
locals, and check whether two separate reads of that `val` agree.

---

## CLOSURE 2026-08-17 — retired, on two independent axes

Classified by CONTENT (grep of current source) and by EXECUTION, never by SHA
ancestry. Binary used for every number below:
`bin/release/x86_64-unknown-linux-gnu/simple`, the **Rust bootstrap seed**
(`bin/simple --version` prints the seed banner), size 59536728, mtime
2026-08-16 22:59:37. Nothing was rebuilt or redeployed for this closure.

### Axis 1 — the reported call site no longer contains the construct

```
$ /usr/bin/grep -rn --include=*.spl native_all_replaces_c_runtime src/compiler src/lib src/app
$ echo $?
1                                  # 1 = no matches

# positive control (an absence check that scanned nothing is not evidence):
$ /usr/bin/grep -rc --include=*.spl runtime_objects src/compiler/70.backend/backend/llvm_native_link.spl
66
```

`/usr/bin/grep` is used deliberately: the bare `grep` on this host is a wrapped
ugrep that honours `.gitignore` and undercounts.

The flag the bug report names is gone from the tree entirely. In its place,
`src/compiler/70.backend/backend/llvm_native_link.spl:1197-1209` binds the list
straight-line through a `match`, with an explicit element type and no
if-expression:

```
    val rt_result = compile_runtime_objects(verbose, options.opt_level, bootstrap_native_all == "", hosted_cc, stage4_requested)
    val runtime_objects: [text] = match rt_result:
        case Ok(paths):
            paths
        case Err(err):
            return Err("Runtime compilation failed: {err}")
```

Lines 1184-1195 of that file carry an in-source comment recording precisely
this bug and why the binding is now unconditional ("The C runtime is never
replaced, so bind it unconditionally, straight-line, with an explicit element
type"). The Stage-3 self-host blocker described in the Symptom section
therefore cannot recur at that site: there is no dead branch left to bind.

### Axis 2 — the underlying language behaviour is correct under both engines

The report's deeper claim was a compiler defect: an if-EXPRESSION with a
constant-false condition binds the DEAD branch's `[]`. Probed directly
(`bin/simple run`, both engines, per-engine subprocess rather than a spec body,
since `bin/simple test` is the tree-walk interpreter only):

```
fn pick() -> [i64]:
    val flag = false
    val xs = if flag:
        []
    else:
        [1, 2, 3]
    return xs
fn pick2() -> [i64]:
    val flag = true
    val xs = if flag:
        [7, 8]
    else:
        []
    return xs
```

| engine | `pick().len()` | `pick2().len()` |
|---|---|---|
| `SIMPLE_EXECUTION_MODE=interpreter` | 3 (correct) | 2 (correct) |
| `SIMPLE_EXECUTION_MODE=jit` | 3 (correct) | 2 (correct) |

Both the live branch and the dead branch bind correctly, in both directions
(dead-`[]`-in-then and dead-`[]`-in-else), on both engines.

### Scope statement — what this closure does NOT prove

The engine that originally produced the symptom was the **self-hosted stage2
binary on the LLVM native backend**, which does not exist in this checkout and
was not rebuilt (~15 lanes share this tree; redeploying `bin/simple` is
forbidden). The probe above exercises the seed's tree-walk interpreter and its
cranelift JIT, not LLVM native codegen. So:

- The **specific blocker** (Stage 3 `native-build` of `bootstrap_main.spl`
  failing at link with three undefined runtime symbols) is retired: the code
  that caused it is deleted, and the current binding cannot lose the list.
- A **general** "if-expression dead-branch binding under LLVM native codegen"
  claim is neither confirmed nor refuted here. If that shape is ever observed
  again on the LLVM path, file it as a new row against the LLVM backend rather
  than reopening this one — this row's evidence, symptom and call site are all
  specific to a construct that no longer exists.
