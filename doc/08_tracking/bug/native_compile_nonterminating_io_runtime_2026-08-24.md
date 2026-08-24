# `native-build` of an `io_runtime` importer does not terminate in `native_compile`

**Status:** Open — FIFTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 70.backend `_MirToLlvm` (native_compile stage), seed tree-walk interpreter
**Predecessor:** `hir_block_value_type_decayed_object_to_int_2026-08-24.md`
(blocker #4, RESOLVED `be3e6fe4a21`)

## Position in the chain

Blockers 1-4 are fixed. With `9e3eb1adccd`, `838f5e2e08c` and `be3e6fe4a21`
landed, the `io_runtime` control program no longer fails — it **hangs**.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`,
`BRC=0`). Exit codes read DIRECTLY into a variable on the line after the
command, never through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 3600 "$SEED" native-build lanework/control.spl -o lanework/control.bin > fix2.log 2>&1
$ NB_RC=$?
NB_RC=124            # 124 == timed out at 3600s
$ grep -c "E-HIR-BLOCK-VALUE-TYPE-DECAYED" fix2.log
0
$ grep -c "cannot convert object to int" fix2.log
0
```

Last progress line, then ~59 minutes of silence:

```text
[build] native_cache 7/7 step 5/6 +11510ms dt=1ms complete
[build] native_compile 2/7 step 5/6 +11510ms dt=0ms lanework.control
```

## Evidence that it is a spin, not slow progress

Measured on the live worker (`src/app/cli/native_build_worker.spl`):

- CPU time tracked elapsed time 1:1 for the whole run (`00:52:45` CPU at
  `52:46` elapsed) — pegged at 100% of one core.
- `VmRSS` flat at ~2,191,100 kB for the last 30+ minutes.
- `/proc/<pid>/io` **completely unchanged** across a 30s sample:
  `rchar: 196686577`, `wchar: 509946`, `syscr: 29406`, `syscw: 2122` before and
  after. Zero I/O progress.
- Worker stderr stopped growing at 36,920 bytes.

Pure compute with no allocation growth and no I/O is the signature of a loop
that is not converging, not of a large module graph still being lowered.

## This is NOT a regression from the blocker-#4 fix

The blocker-#4 fix replaced a raw `MirInstKind.LoadGlobal` payload decode with
typed `MirInst` accessors in
`src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl`. That change is
independently verified not to break `native_compile`:

```text
$ timeout 540 "$SEED" native-build lanework/hello.spl -o lanework/hello.bin
$ HRC=$?
HELLO_NB_RC=0
$ ./lanework/hello.bin
hello
$ RUN_RC=0
```

A plain hello-world native-builds to a working, running binary on the same
binary that hangs on the `io_runtime` importer. Before the fix the
`io_runtime` case could not reach this stage at all — it died at
`native_compile 1/7` in ~21s with `cannot convert object to int` — so there is
no earlier terminating behaviour that was lost.

## Not yet measured

Where in `_MirToLlvm` the loop sits. Attach-based profiling is blocked on this
host (`ptrace_scope=1`, `perf_event_paranoid=4`), so the next step is a
level-gated iteration/progress counter in the `native_compile` instruction walk
rather than a profiler.

## Gate

Already fenced, honestly RED, by
`scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`: its F4 selftest
fixture pins that a non-zero exit with neither blocker-#4 signature present is
still a **FAIL**, so this hang cannot launder into a green verdict. The real
scan reports
`FAIL — 2 case(s) checked, both fenced signatures are absent but native-build
still exited 124; a further blocker is present`.

## Also still open (independent, measured on the same pass)

- `std.common.text` — `MIR lowering error: unresolved method call: index_of`
- `std.nogc_sync_mut.fs` — `MIR lowering error: undefined variable Dir`
