# Seed interpreter: a module-level global clobbers a same-named function LOCAL

Date: 2026-08-21
Status: OPEN — filed, not fixed (root cause not yet isolated)
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
