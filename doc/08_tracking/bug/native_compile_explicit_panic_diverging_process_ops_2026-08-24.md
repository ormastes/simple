# `native-build` of an `io_runtime` importer fails with `explicit panic() -- diverging, must not fall through`

**Status:** Open — SIXTH blocker in the `io_runtime` native-build chain
**Observed:** 2026-08-24
**Area:** 35.semantics (divergence / fall-through analysis), `std.nogc_sync_mut.io.process_ops`
**Predecessor:** `native_compile_nonterminating_io_runtime_2026-08-24.md`
(blocker #5, RESOLVED — the exponential `ssa_block_can_reach` DFS)

## Position in the chain

Blockers 1-5 are fixed. With blocker #5's hang removed, `native-build` of an
`io_runtime` importer now **terminates** (181 s) instead of spinning past
3600 s — and fails with a real, reported diagnostic.

## Reproduction

Seed rebuilt from the fixed tree (`cargo build --release --bin simple`).
Exit codes read DIRECTLY into a variable on the line after the command, never
through a pipe.

```simple
use std.nogc_sync_mut.io_runtime

fn main():
    val v = env_get("HOME")
    print("control ok")
```

```text
$ timeout 600 "$SEED" native-build lanework/control.spl -o lanework/control.bin
$ NB_RC=$?
NB_RC=1     elapsed=181s
```

```text
error: explicit panic() -- diverging, must not fall through
error: semantic: panic: compile error: explicit panic() -- diverging, must not fall through
```

Five occurrences of `explicit panic()` in the full stderr.

## Context reported alongside (may or may not be causally related)

```text
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops dependency=Option: no declaration, re-export hop, or explicit import of this name in the owner; a later `unresolved type: Option` will be reported against an importing module instead
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.process_ops dependency=Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io_runtime      dependency=Option / Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.file_ops     dependency=Option / Result: ...
[hir-callable-dep-origin-unresolved] owner=std.nogc_sync_mut.io.signal_stubs dependency=fn: ...
```

Also reported, and worth checking independently:

```text
warning: public function `env_get` has 3 co-compiled definitions with 2 differing
signatures ((text)->Optional(text) vs (text)->text); JIT call sites resolve by exact
arg-type match ... a fallback hit may still dispatch to the wrong one.
[compiler_cross_module_private_symbol_collision]
```

`env_get` is precisely the function the reproduction calls, and the control
program's `use` is what pulls in all three definitions.

## Not yet measured

- Which `panic()` site, in which function, raises the diagnostic. The message
  carries no file/line — that is itself a defect worth fixing first, since it
  makes the error nearly unactionable.
- Whether the unresolved `Option`/`Result` dependency origins above are the
  cause (a `panic()` in a branch whose type is unresolved may be
  mis-analysed as falling through) or independent pre-existing noise.
- Whether the `env_get` signature collision is implicated.

## Note on stderr truncation

The worker's stderr is middle-dropped (`16470 of 28470 bytes ... dropped from
the MIDDLE`). The full stream is saved to a named file
(`[native-build] FULL stderr (28470 bytes) saved to: ...`) — read that file
rather than counting over the truncated console output, which the tool itself
labels unreliable.

## Gate

Not yet fenced. Blocker #5's gate
(`scripts/check/check-ssa-block-reach-not-exponential.shs`) deliberately
asserts NON-HANG and NAMES this residual exit 1 rather than asserting exit 0;
its `--require-success` flag turns exit 0 into a hard assertion and should be
switched on as the default once this bug lands. The same applies to
`--require-success` in
`scripts/check/check-hir-block-tail-and-loadglobal-decode.shs`, which is
deliberately still NOT the default for the same reason.

## Operational note

`timeout` kills the `native-build` parent but the `native_build_worker.spl`
child can survive as a multi-GB, 100%-CPU orphan. Check
`pgrep -af native_build_worker.spl` after any interrupted reproduction, and kill
only the PIDs belonging to your own working directory — other lanes run their
own workers.
