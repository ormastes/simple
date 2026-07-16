# native_struct_closure_capture_hang

Status: hang no longer reproducible — native-build now loud-fails on unsupported lambda forms (2026-07-16)

**Status:** hang no longer reproducible — native-build now loud-fails on unsupported lambda forms (2026-07-16)
**Severity:** medium
**Date:** 2026-06-05

## Summary

Passing struct objects (e.g. `Channel`) through closure capture hangs indefinitely in native AOT mode. Only `i64`/primitive capture works.

## Reproduction

```simple
use std.concurrent.channel.{channel_new}
use std.concurrent.thread.{thread_spawn}

fn main():
    val ch = channel_new()
    fn worker(seed: i64, ch_arg: Channel):
        ch_arg.send(seed)
    val t = thread_spawn(\: worker(1, ch))
    val result = ch.recv()
    println(result)
```

Compile with `--native`, run: hangs indefinitely even with 1 worker.
Works correctly in interpreter and SMF modes.

## Workaround

Pass the struct's id as `i64`, reconstruct via factory function:

```simple
use std.concurrent.channel.{channel_new, channel_from_id}

fn worker(seed: i64, ch_id: i64):
    val ch = channel_from_id(ch_id)
    ch.send(seed)
```

## Likely Location

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`

## Resolution (2026-07-15)

The pure-Simple MIR path now lifts capturing lambdas with an environment-first
hidden argument and stores scalar or struct handles by value in a portable,
membership-checked closure runtime. The C registry is synchronized and
fail-closed; the pure-Simple runtime checks membership before dereference.

The strict regression is shared with the first-class-lambda bug and covers
hosted/simple-core runtimes under default LLVM and explicit Cranelift. Execution
awaits a fresh runnable pure-Simple compiler artifact.

## Regression evidence (2026-07-16)

Verified with the deployed seed interpreting `src/compiler` live
(`env -u SIMPLE_BOOTSTRAP bin/simple native-build`, `timeout 180`), after a
worktree-local compat unblock for the rt_dict_*/rt_tuple_get seed-extern
mismatch (see below). The HANG does not reproduce in any variant:

- Zero-arg closure capturing a struct, called directly
  (`val f = \: p.x + p.y; f()`): builds, runs, output `7` == interpreter
  oracle. PASS.
- Zero-arg closure capturing a struct, passed as a function argument (the
  doc repro's `thread_spawn(\: worker(1, ch))` shape): LOUD build error
  `MIR lowering error: unsupported MIR expression: HirExprKind::Lambda(...)`,
  exit 1, no binary, no hang. Construct unsupported pending the shared
  first-class-lambda/closure-env work.
- Parameterized lambda capturing a struct, passed as a value: LOUD
  `MIR lowering error: undefined variable: <lambda-name>`, exit 1, no hang.
- Original repro as written: LOUD `HIR lowering error: unresolved name:
  channel_new / thread_spawn` (std.concurrent not resolvable on the bare
  native-build path), exit 1, no hang.

The former infinite spin is gone; every unsupported closure form fails loudly
and names the construct. Full support is tracked by the first-class-lambda /
closure-env item referenced above.

NOTE (environment): at verification time the deployed seed (built 2026-07-11)
predates the rt_dict_keys / rt_dict_contains / rt_tuple_get / rt_array_get_text
/ rt_is_none extern migration (ca1e18c1744, 2026-07-13), which made EVERY
native-build die at startup with `error: semantic: type mismatch: cannot
convert dict to int` (smoke matrix 0/15). Verification required reverting those
call sites to `.keys()` / `.contains_key()` / direct tuple indexing / `!= nil`
(and dropping two `as [Pattern]` casts the old seed cannot evaluate); a seed
redeploy that includes the new interpreter externs obsoletes that compat layer.
