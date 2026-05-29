# Bug: Native codegen string equality broken

**Date:** 2026-05-27
**Severity:** Critical (blocks bootstrap)
**Component:** Rust seed codegen (native-build)

## Summary

Compiled native binaries produce incorrect results for string `==` comparisons.
The interpreter works correctly. This blocks stage2 bootstrap since the compiled
CLI binary cannot dispatch commands or parse options.

## Two distinct bugs

### Bug A: Local string `==` compares length only

```spl
val a = "human"
val b = "hello"
if a == b:
    print "BUG"   # <-- this branch is taken (both 5 chars)
```

### Bug B: Struct field string `==` always returns TRUE

```spl
val lm = log_opts.log_mode   # value is "human"
if lm == "json":
    print "BUG"   # <-- this branch is taken (different lengths!)
```

## Root cause

The Rust seed codegen generates inline string comparison code that:
- Bug A: compares only the length field, not the content bytes
- Bug B: appears to always evaluate true for struct field access comparisons

The runtime provides correct implementations (`rt_native_eq`, `rt_native_neq`,
`rt_value_eq` in `src/runtime/runtime_equality.c`) that use `memcmp`, but the
codegen never emits calls to them. Instead it generates its own broken inline
comparison.

## Evidence

### Symbol analysis
- `libsimple_runtime.a`: `rt_native_eq` is T (strong, defined)
- Compiled binary: `rt_native_eq` is W (weak stub) -- codegen emits its own weak
  version and never references the real one

### Interpreter confirmation
```
$ bin/release/simple /tmp/test_seed_eq.spl
OK1: human!=hello    # correct
OK2: human==human    # correct
OK3: human!=json     # correct
```

### Compiled binary behavior
```
DEBUG: eq test human==json
OK: human==json is FALSE        # different lengths -- length check passes
BUG: human==hello is TRUE       # same length (5) -- length-only comparison
BUG: lm==json TRUE              # struct field -- always true
```

## Impact on CLI

1. `cli_clean_log_args` strips ALL args: `"--version"` (9) matches `"--verbose"` (9)
2. `log_opts.log_mode == "json"` always true: CLI outputs JSON instead of human text
3. All command dispatch via `match first:` unreliable

## Repro

```bash
bin/simple native-build --entry-closure --clean -o /tmp/simple_debug
echo 'fn main() -> i64:
    val a = "human"
    val b = "hello"
    if a == b:
        print "BUG: same-length different content"
    else:
        print "OK"
    return 0' > /tmp/test_eq.spl
bin/release/simple /tmp/test_eq.spl        # interpreter: OK
/tmp/simple_debug /tmp/test_eq.spl         # compiled: BUG
```

## Deeper blocker: 871 stubbed symbols in stage2

The string equality bug is real but secondary. The compiled stage2 binary has
**871 symbols stubbed as weak functions** by `--entry-closure`, including the
entire `backend__build_native__*` family and `cli_native_build` itself. This
means the stage2 binary can run `--version` but **cannot compile code**.

### Symbol evidence
```
nm /tmp/simple_stage2 | grep -c ' W '   → 871 weak stubs
nm /tmp/simple_stage2 | grep cli_native_build → W (weak, stubbed)
```

### Historical context

The prior "bootstrap" used `bootstrap_emit_seed_wrapper` — a C shim that
`exec()`'d the Rust seed binary. This was deliberately removed in a prior
session. Without it, the stage2 has no compilation capability.

### Architecture options

1. **Restore the seed wrapper shim** — re-enable `bootstrap_emit_seed_wrapper`
   so stage2 delegates compilation to the Rust seed. Fastest path but re-
   introduces the exec() dependency.
2. **Rust codegen fix** — modify the Rust seed's codegen to resolve the 871
   stubbed symbols (emit calls to runtime functions, fix string equality).
   Addresses root cause but requires Rust changes.
3. **Resolve 871 symbols in .spl** — ensure all 871 unresolved modules compile
   and link into stage2 without `--entry-closure` stubbing. Most ambitious;
   currently 27 modules fail to compile without `--entry-closure`.

## Proposed fix (string equality only)

The codegen (in the Rust seed) needs to emit calls to `rt_native_eq` for string
operands instead of generating inline comparison. The function exists in
`src/runtime/runtime_equality.c` and is linked into `libsimple_runtime.a`.

### Verified .spl workaround

`fn str_eq(a, b) -> bool: a.len() == b.len() and a.starts_with(b)` works
correctly in compiled native code (verified via exit codes). However, this
workaround does NOT address the 871-stub blocker — it only fixes string
comparisons if the code reaches them.
