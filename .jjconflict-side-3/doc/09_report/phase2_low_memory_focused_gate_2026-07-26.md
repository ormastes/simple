# Phase-2 low-memory focused gate — 2026-07-26

## Scope

This is a narrow executable companion to
`test/01_unit/compiler/driver/low_memory_source_fingerprint_spec.spl`. It does
not replace that spec's driver-order and `low_memory`/VHDL option-gate checks.

## Bottleneck diagnosis

The focused CLI spec is CPU-bound before its assertions because it is a
`std.spec` entry that imports `CompileContext`. `CompileContext` imports the
driver's HIR, MIR, backend, dependency-injection, and frontend surfaces. The
CLI test path must construct that compiler/test closure before it reaches the
small source-reclamation cases. This is test-loading cost, not evidence that
the post-parse reclamation path itself is looping.

## Direct micro gate

`test/02_integration/compiler/phase2_low_memory_source_reclaim_probe.spl` is a
direct `run` entry, not a `std.spec` test. It is deliberately a split fixture:
the executable portion validates registry ownership on a dynamically read
source value, while exact-body source contracts validate the real compiler
path without importing its HIR/test closure or the broad `std.io` facade.

1. read a committed fixture into a runtime-owned text value and copy its alias;
2. call registry-checked `rt_string_free` on the value and its alias, expecting
   `1` then `0` without reading either freed alias;
3. extract the one exact `lexer_release_parse_source_globals` body by
   indentation and require its seven singular cleanup statements;
4. extract the one exact `CompileContext.source_contents_reclaimable` body and
   require `low_memory && backend != "vhdl"`; and
5. extract the one exact `CompilerDriver.compile` body and require singular
   parse → reclaim gate → lexer release → reclaim → source eviction →
   `lower_and_check_impl()` ordering.

Negative-control source strings contain every token accepted by the previous
whole-file checks, but place them in docstrings or sibling methods. The gate
requires all negative controls to remain false, preventing non-executable text
or unrelated bodies from producing a green result.

This is intentionally not a claim that the probe runs HIR lowering itself. A
first direct attempt that imported frontend/HIR was blocked before probe entry
by the existing self-hosted interpreter's `rt_transient_array_scope_begin`
extern gap. The split gate preserves executable ownership evidence while
keeping that unrelated compiler-closure failure out of this focused lane.

The probe emits stable `phase2_low_memory_probe_*` keys and exits nonzero if
any assertion fails. The canonical entry point is the bounded wrapper:

```sh
sh scripts/check/check-phase2-low-memory-source-reclaim.shs
```

The wrapper resolves only a non-symlinked repository `bin/release/*/simple` (or
`release/*/simple`), records its absolute path and SHA-256, runs a bounded
version probe that rejects `Rust-built`, `bootstrap seed only`, and debug
identities, and pins that same artifact through `SIMPLE_BINARY`,
`SIMPLE_BIN`, `SIMPLE_BOOTSTRAP_DRIVER`, and `SIMPLE_FRONTEND_DELEGATE`.
It starts both version and probe commands in new process groups, retains only a
4-KiB head and 4-KiB tail from each stdout/stderr stream, and sends TERM then
KILL to the whole group on timeout. After the direct child exits, it also
bounds FIFO-reader drain. A reader held open past that drain deadline causes
bounded TERM/KILL cleanup of the original group and both readers and an
internal status `125`; only a normal drain preserves the direct child's exit.

Each invocation writes:

- `build/phase2_low_memory_source_reclaim_gate/rerun-command.sh.txt`: the exact
  wrapper rerun with resolved binary path;
- `build/phase2_low_memory_source_reclaim_gate/probe-command.sh.txt`: the exact
  pinned child command;
- bounded `version.*` and `probe.*` logs; and
- `build/phase2_low_memory_source_reclaim_gate/evidence.env`, including the
  binary, command, source, and log paths, byte counts, and SHA-256 values.

The wrapper cannot report pass unless the source contracts are true, the
negative controls are true, the first/second frees are exactly `1`/`0`, the
probe exits zero, and the probe reports `pass`. No Rust seed fallback and no
Stage4 bootstrap are part of this gate.

## Evidence

- overall status: **BLOCKED**. The historical attempts below do not satisfy the
  repaired `1`/`0` gate and must not be cited as a pass.
- first bounded direct-run attempt: exit `1` before probe entry while resolving
  the existing HIR import closure; diagnostic: unknown extern
  `rt_transient_array_scope_begin`. It was not a source-reclamation failure and
  did not execute Stage4 or the heavyweight focused `simple test` command.
- split-probe attempt: exit `1` in under one second. Its executable source
  checks passed (`lexer_release_complete=true`, `hir_after_reclaim=true`), but
  both ownership calls returned `0` because the deployed arm64 launcher emitted
  `unknown extern function: rt_string_free`. The launcher resolves to an
  artifact which identifies itself at runtime as a Rust bootstrap seed; it is
  not an acceptable fallback for this pure-Simple gate. No further attempt was
  made until a self-hosted artifact linked with `rt_string_free` is redeployed.
- the repaired wrapper has not converted this blocker into a pass. Its next
  admissible run must retain the exact resolved pure-Simple binary identity,
  commands, bounded logs, and hashes listed above.
- the FIFO-drain supervision hardening was reviewed statically only; the
  blocked runtime probe was not rerun as part of that repair.
