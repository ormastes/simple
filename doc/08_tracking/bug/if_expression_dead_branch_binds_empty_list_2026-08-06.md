# if-expression with a constant-false condition binds the DEAD branch's `[]`

- **Date:** 2026-08-06
- **Status:** OPEN (compiler defect). Call site worked around by deleting the
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
3. After the failed link the 23 objects were **gone** from `t3` — they can only
   have been removed by `cleanup_runtime_objects(runtime_objects)`, i.e. the
   same `val` held the real, non-empty list at that later read.

So one read of `runtime_objects` saw an empty list and a later read saw the full
23-element list.

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

A whole-cycle GREEN through the compiler itself was NOT reached: a rebuilt
stage2 now dies one phase earlier, in `llc`, on
`%t3209 = icmp ne double %l39, 0` (an integer truthiness compare emitted against
a double). That is a separate codegen defect and is unrelated to this change.

Separately, the Stage 3 object's `__simple_main` is vacuous — it returns a stack
slot without calling anything, so the linked binary is 28 KB and produces no
output for any subcommand. Fixing the link does not by itself yield a
self-hosting binary.

## Repro shape

Not reduced to a minimal case yet; it only reproduces on the full Stage 3
self-host compile. A reduction attempt should start from an untyped `val` bound
to an if-expression whose dead branch is a bare `[]`, in a function with many
locals, and check whether two separate reads of that `val` agree.
