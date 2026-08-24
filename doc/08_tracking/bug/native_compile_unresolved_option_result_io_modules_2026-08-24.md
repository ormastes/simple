# `native-build` of an `io_runtime` importer: `Option`/`Result` unresolved in three io modules

**Status:** Open — SEVENTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 20.hir / 35.semantics (callable dependency origin resolution),
`std.nogc_sync_mut.io.{file_ops,process_ops}`, `std.nogc_sync_mut.io_runtime`
**Predecessor:** `native_compile_explicit_panic_diverging_process_ops_2026-08-24.md`
(blocker #6, RESOLVED — the LLVM `Abort` terminator routed through the
fail-the-build `emit_unsupported_panic` helper)

## Position in the chain

Blockers 1-6 are fixed. With blocker #6's spurious compile error removed, the
`explicit panic()` signature is **gone** (5 occurrences -> 0), and
`native-build` now fails on this, a **different and independent** defect.

This was **not** unmasked by the #6 fix in the sense of being caused by it —
it was reported alongside #6 all along, in that record's "Context reported
alongside" section, where its causal relationship was explicitly listed as
unmeasured. It is now measured: independent.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`, rc=0).
Exit code read DIRECTLY into a variable on the line after the command.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 900 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1
```

```text
error: build failed: 3 failed, 0 unverified, 0 not run, 3 ok of 6 unit(s)
  ERROR: std.nogc_sync_mut.io.file_ops, std.nogc_sync_mut.io.process_ops,
         std.nogc_sync_mut.io_runtime
```

## The correlation that identifies it

The three ERROR modules are **exactly** the three owners of an
`Option`/`Result` dependency-origin report — no more, no fewer:

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Result
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops  dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops  dependency=Result
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Option
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Result
```

each reading:

> no declaration, re-export hop, or explicit import of this name in the owner;
> a later `unresolved type: Option` will be reported against an importing
> module instead

A fourth module, `std.nogc_sync_mut.io.signal_stubs`, carries the same report
for `dependency=fn` but is **not** in the ERROR set — worth understanding, as
it may discriminate the mechanism.

## Note on the diagnostic itself

The report predicts its own downstream symptom ("will be reported against an
importing module instead") — i.e. the compiler already knows the blame is
being attributed to the wrong module. That misattribution is itself worth
fixing: it is the same "diagnostics that lie" half of this chain's recurring
family, and it is why this defect sat classified as background noise while six
other blockers were chased.

## Not yet measured

- Whether `Option`/`Result` genuinely lack an import/re-export hop in those
  three modules (a real source defect) or whether the origin resolver fails to
  follow a hop that exists (a compiler defect). **Not yet determined — do not
  assume the latter because the previous six blockers were compiler defects.**
- Why `signal_stubs` reports the same class but does not ERROR.
- The actual per-module error text. The `3 failed` summary names the modules
  but the underlying `unresolved type:` lines were not located in the captured
  stderr; the full stream is saved to a named file (see below) and should be
  re-read rather than inferred.

## Note on stderr truncation

The worker's stderr is middle-dropped. The full stream is saved to a named
file (`[native-build] FULL stderr (NNNNN bytes) saved to: /mnt/data/tmp/...`).
Read that file; the console output is explicitly labelled unreliable by the
tool itself.

## Operational note

`timeout` kills the `native-build` parent but the `native_build_worker.spl`
child can survive as a multi-GB, 100%-CPU orphan. Check
`pgrep -af native_build_worker.spl` after any interrupted reproduction, and
kill only PIDs belonging to your own working directory — other lanes run their
own workers.

## Gate

Blocker #6's gate
(`scripts/check/check-llvm-abort-terminator-not-unsupported.shs`) asserts the
ABSENCE of the `explicit panic()` signature and, without `--require-success`,
deliberately reports this residual rc=1 by name rather than failing on it.
Three gates in this chain now hold a `--require-success` flag that is
deliberately **NOT** the default, all waiting on exactly this bug:

- `scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`
- `scripts/check/check-ssa-block-reach-not-exponential.shs`
- `scripts/check/check-llvm-abort-terminator-not-unsupported.shs`

Flip all three to require success once `native-build` reaches rc=0.
