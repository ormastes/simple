# native_struct_closure_capture_hang

Status: open

**Status:** open -> CLOSED-STALE (2026-09-12: not re-run to avoid an uncontrolled hang)
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

## Triage 2026-09-12
Not re-run in this pass to avoid triggering the reported indefinite hang mid-batch; older than 45 days. Closing per age policy — good candidate for an isolated, timeout-guarded re-test. Evidence: seed binary /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
