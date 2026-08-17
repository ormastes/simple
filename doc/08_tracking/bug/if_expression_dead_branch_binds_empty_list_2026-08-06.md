# if-expression with a constant-false condition binds the DEAD branch's `[]`

- **Date:** 2026-08-06
- Status: OPEN (P1)
- Status re-verified 2026-08-17 by source inspection (triage shard 01).
  dead branch — see `src/compiler/70.backend/backend/llvm_native_link.spl`.
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
