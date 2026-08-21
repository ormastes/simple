# Seed interpreter: a module-level global clobbers a same-named function LOCAL

Date: 2026-08-21
Status: RESOLVED 2026-08-21 (root cause: `for`-loop bindings were never marked local)
Severity: high (silent wrong value, no diagnostic)

## Symptom

In a script that wildcard-imports many compiler modules and calls across module
boundaries, a function-local binding is silently replaced by a module-level
global of the same name from an imported module.

Measured on `bin/release/x86_64-unknown-linux-gnu/simple` (59,947,080 bytes,
2026-08-21 14:27:35 UTC), `SIMPLE_NO_JIT=1 SIMPLE_MODULE_LIMIT=4000`:

`scripts/check/class_identity_pure_simple_driver.spl:182` does

```
for name in ordered.split(","):
    val opath = dir + name
    val osrc  = rt_file_read_text(opath)
    val orc   = core_jit_interpret(osrc, opath, 999999)
    print "[case] {name} rc={orc}"
```

with `CLASS_IDENTITY_CASES="first_if_else.spl,second_if_else.spl"`. Both
iterations print `[case] Alice rc=0` and read the path
`.../interp_reentrancy/Alice`. `Alice` is the value of
`val name = "Alice"` at `src/compiler/10.frontend/core/test_lang_basics.spl:78`,
a module the driver wildcard-imports (`use compiler.frontend.core.test_lang_basics.*`,
driver line 123).

Renaming the loop variable to `case_name` does not fix it — the run then dies
with `error: semantic: type mismatch: cannot convert dict to int`, i.e. the same
clobber landing on another local.

`.split(",")` itself is correct in isolation (a standalone 6-line probe splits
`"aa.spl,bb.spl"` into exactly `aa.spl` / `bb.spl`).

## Impact

Blocks `sh scripts/check/check-interp-reentrancy.shs`, which now FAILs with 13
offenders (all "no-verdict") purely because the driver never evaluates the
requested cases. The re-entrancy fix it gates
(`pure_simple_interpreter_core_jit_interpret_not_reentrant_2026-08-20.md`) is
itself intact.

## Not yet minimised

Two smaller probes did NOT reproduce, so the trigger needs more than a name
collision:
1. a script importing `compiler.frontend.core.test_lang_basics.*` with a local
   `for name in ["a","b"]` and no cross-module call — correct output;
2. a two-file fixture (module with `val name = "Alice"` plus a function, caller
   with a local `name` and a call to that function per iteration) — correct
   output.

The driver differs in scale (70+ wildcard imports) and in calling
`core_jit_interpret`, which re-enters the interpreter. The suspect area is the
module-globals refresh/seed machinery reachable from
`src/compiler_rust/compiler/src/interpreter_call/core/function_exec.rs`
(`seed_owner_globals`, `owned_globals_snapshot`, `owner_bindings`,
`MODULE_GLOBALS`): those write globals back into an environment after a call
returns, which matches the observed "local is correct before the call, wrong
after" shape.

## Next step

Bisect with the real driver (it is a deterministic reproducer): dump the
binding for `name` immediately before and immediately after the
`core_jit_interpret` call, then walk the globals-writeback path above.

## RESOLVED 2026-08-21 — root cause and fix

### Minimised reproducer (2 files, 11 lines)

`<tmp>/src/pkg/lib.spl`:

```
fn touch(label: text, actual: i64, expected: i64):
    if actual != expected:
        print "FAIL: {label}"

val name = "Alice"
touch("seed", 1, 1)
```

`<tmp>/entry.spl` — the entry file MUST sit outside the package directory; an
entry inside `src/pkg/` resolves the import differently and does not reproduce:

```
use pkg.lib.*

fn main() -> i32:
    for name in "aa,bb".split(","):
        touch("x", 1, 1)
        print "seen={name}"
    return 0
```

Pre-fix: `seen=Alice` twice. Post-fix: `seen=aa`, `seen=bb`.
The scale of the original driver (70+ wildcard imports, `core_jit_interpret`)
was irrelevant — all that is needed is a `for`-loop variable colliding with a
wildcard-imported module global plus ONE cross-module call in the loop body.

### Mechanism

`exec_for` (`src/compiler_rust/compiler/src/interpreter_control.rs:3309`) saved
and restored the loop binding's prior value but never called
`env.mark_local` / `env.enter_block_local` for it — unlike match-arm bindings
(same file, `enter_block_local` at the arm), function params
(`interpreter_call/core/function_exec.rs:669`) and lambda params
(`interpreter_call/core/lambda.rs:42`).

`CowEnv::is_local` (`compiler/src/value.rs:616`) was therefore false for the
loop variable. Every globals write-back path keys off exactly that predicate:

* `publish_live_bound_globals` / `sync_owned_captured_globals`
  (`interpreter_call/core/function_exec.rs:205,279`) filter on
  `!env.is_local(name)`, so on the call in the loop body the loop variable's
  value was PUBLISHED into `pkg.lib`'s global `name`;
* `refresh_bound_global` (`value.rs:956`) then treats every non-local overlay
  entry aliasing that owner/global as a stale copy and OVERWRITES it — putting
  `"Alice"` back into the live loop variable.

Hence "correct before the call, wrong after", and hence renaming the local only
moved the collision to whichever other unmarked binding matched next.

### Fix

Mark the loop binding block-local for the duration of the loop
(`enter_block_local` before `exec_for_inner`, `exit_block_local` in the
unconditional restore loop). Two lines plus a comment, same precedent as
match-arm bindings. No rename, no special-casing of names.

### Tests

`src/compiler_rust/compiler/tests/interpreter_for_loop_local_shadow.rs`
(3 cases: the loop variable is not clobbered — FAILS pre-fix; the module global
is not published over by the loop variable; nested loops keep their own
bindings).

### Still failing, separately

`sh scripts/check/check-interp-reentrancy.shs` is NOT green after this fix. The
class-identity driver now gets past the clobber and dies in a fresh, single-case
process with `array index out of bounds: index is N but length is 0` — a
different defect (empty exported arena arrays), unrelated to local shadowing and
not introduced here: the pre-fix binary fails the same run earlier, with the
clobber symptom `type mismatch: cannot convert dict to int`. That failure
belongs to
`pure_simple_interpreter_core_jit_interpret_not_reentrant_2026-08-20.md`.
