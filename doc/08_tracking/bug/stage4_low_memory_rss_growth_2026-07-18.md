# Bug: Stage 4 `--low-memory` build grows past 25 GB RSS

## Status

Source plumbing fixed; executable acceptance remains open. The bounded
incremental Stage 4 build was stopped deliberately before host/session failure;
no Stage 4 artifact was produced, so the canonical essential
test/lint/duplication gate remains pending.

The canonical wrapper passed `--low-memory`, but the Stage4 branch bypasses the
ordinary argument parser and rebuilt `CompileOptions` through the fixed-arity
pure-Simple API. That API left `low_memory` at its default `false`, disabling
all existing source/AST/HIR/MIR eviction points. Its sole source caller is the
canonical Stage4 branch, so the fixed-arity owner now enables low-memory mode
directly. The source regression pins the option; bounded RSS and artifact
evidence are still required.

The next active retention owner was `ast_reset()`: every parsed file replaced
the declaration, expression, statement, match-arm, module, and lexer-state
arrays with fresh allocations. The core runtime keeps registered arrays for
the process lifetime, so those resets both retained old buffers and lengthened
later validity scans. All three arena reset owners now allocate only nil module
arrays, clear reusable outer storage in place, and reset one-element state slots
without replacing them. The same fix adds the trait/mutability and GPU pools
that the old reset accidentally omitted. Existing sequential large-then-small
parse coverage remains the stale-state oracle, and a source contract rejects
unconditional arena replacement. A cached current-source compile emitted the
changed compiler objects; final linking stopped on the separately known
`nogc_async_mut__path__join` provider gap, so no RSS or executable PASS is
claimed.

Parser initialization now follows the same ownership rule: it clears the
current-parse diagnostics and struct-name lists, overwrites token/cache
singletons, and reuses the lexer's outer active-lexer slot. The source-specific
`CoreLexer` payload is still replaced. Its `source.chars()` allocation remains
a larger Unicode-sensitive retention candidate, so this bounded container fix
does not claim to close the RSS acceptance item.

## Reproduction

Use the constructor-preserving Stage 3 compiler to build only the full CLI with
`--runtime-bundle core-c-bootstrap`, `--entry-closure`, `--low-memory`, two
threads, and the existing native cache. The exact invocation is the
`bootstrap_native_build_main` command in
`scripts/bootstrap/bootstrap-from-scratch.sh`; this run did not invoke the full
bootstrap pipeline.

Observed on 2026-07-18:

- one `simple native-build` process remained CPU-active (about 100% CPU), so it
  was not classified as a deadlock;
- elapsed time exceeded 10 minutes without an output artifact or progress
  marker;
- RSS reached 24,916,288 KiB (about 23.8 GiB) despite `--low-memory`;
- the process was interrupted once with exit 130 under the runaway/budget
  guard; it was not retried.

## Required fix and regression

1. Add bounded phase/progress reporting to the pure-Simple native-build driver
   so compilation, aggregation, and linking can be distinguished without a
   debugger.
2. Profile retained module/MIR/object state in the Stage 4 entry-closure path
   and release completed-module state under `--low-memory`.
3. Add an isolated Stage 4 resource smoke that samples max RSS and fails on
   timeout or an agreed memory ceiling before the essential-tools gate.
4. After the resource smoke passes, run
   `scripts/check/check-bootstrap-essential-tools-smoke.shs` exactly once with
   the resulting Stage 4 binary.

Acceptance requires a produced full CLI, bounded warm elapsed time/RSS evidence,
and green test-runner, lint, and duplication probes. A CPU-active process with
unbounded RSS is not a passing “slow build.”
