# native-build const-eval: hex-letter parse (FIXED) + residual typed/module-val gaps (OPEN)

Date: 2026-06-28

Lane: `.spipe/simpleos-alpine-harden-musl-busybox` (AC-6b — cross-compile simplebox)

## Part 1 — hex literal with an a-f digit fails const-eval — **FIXED 2026-06-28**

`native-build` aborted with `error: semantic: cannot parse 'c' as i64` (seed
`interpreter_call/builtins.rs:613`) when const-evaluating **any hex literal
containing a letter digit a-f / A-F**. The parser
(`src/compiler/10.frontend/core/_ParserPrimary/primary_expr.spl`) mapped hex
digits with `int(hc) - int("a") + 10`; the `int()` builtin numeric-parses, so
`int("a")`/`int("c")` errored. The error letter was the first hex letter
encountered (`0xc...` → `'c'`, `0x7f...` → `'f'`).

Minimal repro (now passes):
```
val MAGIC: u64 = 0xc5e77b6b397e7b43   # was: cannot parse 'c' as i64
```

Fix: map hex digits via a lookup string (same idiom as
`lexer_struct.spl:lex_escape_hex_value`), no `int(<letter>)`. Verified:
`0xca=202`, `0xff=255`, `0xDEAD=57005`, `0xAbCdEf=11259375`, `0x10=16`, binary
`0b1010=10`, octal `0o17=15`. Regression guard:
`test/01_unit/compiler/hex_literal_const_eval_spec.spl` (7/0).

This is why the kernel `0xc...` LIMINE constants (scanned by `--source src/os`)
tripped the simplebox build. Pre-existing; unrelated to this lane's libc port
(proven by a marker test: renaming the lane's `["c", ...]` library list to
`["zzcmark", ...]` left the identical `'c'` error).

## Part 2 — native-build can't compile a typed/module integer `val` — **OPEN**

With Part 1 fixed, minimal freestanding programs still fail to emit. These are
separate, pre-existing native-build gaps (not hex-specific, not this lane):

| repro | error |
|---|---|
| `fn main() -> i32:`<br>`    val x: i64 = 255`<br>`    if x > 0: return 0`<br>`    return 1` | `method `unwrap` not found on type `Type`` |
| `val M: i64 = 0xca`<br>`fn main() -> i32: return 0` | `undefined field 'kind': cannot access field on value of type 'nil'` |

A plain **decimal** typed local (`val x: i64 = 255`) reproduces the first error,
so it is unrelated to hex. These block any non-trivial freestanding entry
(including simplebox) independently of Part 1.

## Earlier mis-diagnoses (corrected)

The first version of this bug claimed "exit 255, no binary, no error / no emit
for multi-module freestanding entries." That conflated three unrelated things,
none of which is a cross-module emit gap:
1. **120s death** = Simple's own `process_run_timeout` 120s default
   (`process_ops.spl:77`) in the *test harness* — not native-build.
2. **`ld.lld: cannot open simple_rt_runtime.o`** = the **stale deployed**
   `bin/simple` seed; the current cargo seed does not have this error.
3. **The real wall** = the hex const-eval bug above (Part 1), now fixed,
   revealing the typed/module-val gaps (Part 2).

A single pure-Simple libc module (`simpleos_stdlib_num.spl`) compiles to a real
freestanding PIE ELF with the current cargo seed — the libc port is sound.

## Acceptance for closure (Part 2)

- `native-build` emits a real freestanding ELF for a typed-`val` program and for
  `simplebox_main.spl` (`--source src/os --entry-closure --target
  x86_64-unknown-none`), linked against the SimpleOS sysroot.
- Then `build_simplebox("x86_64-unknown-none")` produces a runnable
  `build/os/rootfs/bin/simplebox` and `simplebox seq '  2'` proves
  `libc_strtoul` executes in the compiled binary.
