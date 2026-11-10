# native_struct_closure_capture_hang

Status: open

**Status:** open
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

## Addendum 2026-11-11 (lane ne17) — hang shape STALE; exact repro blocked

Fresh seed 46fe8f6b6def (Windows, worktree simple-p3-ne17-20261111):

1. The literal `--native` flag from the reproduction no longer exists in the
   CLI (`build --help` / `run --help` show no native/AOT option);
   `native-build` is the successor path.
2. Struct closure capture through native codegen WORKS in the minimal shape:
   `struct Box: n: i64` captured by `fn get(): b.n`, `print(get() + 1)`
   prints `42` under `native-build --backend cranelift`
   (SIMPLE_NATIVE_BUILD_RUST=1), matching the interpreter.
3. The exact channel repro builds and links (needs llvm-mingw on PATH, see
   the ne17 addendum on the object-cache row) but CANNOT evaluate the hang:
   `rt_channel_*` externs are unbacked on this Windows core-c-bootstrap
   lane — a bare `channel_new(); ch.send(7); ch.recv()` prints the stub `0`
   natively (interpreter prints the value). Both the struct-capture repro and
   the documented i64-id workaround print `0` natively for that reason, so
   no native conclusion about the captured-struct path is possible here.

Verdict: the recorded hang is not reproducible on any shape runnable on this
lane; closure-capture semantics were re-owned 2026-09-27 (by-value,
read-only captures; see `test/01_unit/interpreter/closure_capture_writeback_spec.spl`
and PR #8238 work/p2-closure-capture-writeback). **Grant:** one run of the
exact 2026-06-05 repro on a native lane with the backed channel runtime
(Linux hosted link) to close the residual.
