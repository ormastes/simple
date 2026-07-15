# native_struct_closure_capture_hang

Status: source fix implemented; strict execution pending

**Status:** source fix implemented; strict execution pending
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
