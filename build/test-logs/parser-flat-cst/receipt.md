# Flat CST focused verification receipt

- Candidate: `cd82f862f646b3e26479ab895db6527d4a65039c` (includes `a3ebcec7334068831a75591cd1b753eab6d4d9a4`)
- Recorded at: `2026-08-29T20:27:36.980Z`
- Working directory: `/mnt/data/parser-cst-linked-children`
- Command: `SIMPLE_LIB=src /mnt/data/worktrees/goal-cache-shadow-freeze/release/x86_64-unknown-linux-gnu/simple test test/01_unit/std/parser/treesitter_facade_compat_spec.spl --mode=interpreter --sequential --fail-fast`
- Runtime SHA-256: `d0976e84e863b8d158a78dce8faf172b086662466cddfe57ee65fd30300ed1a2`
- Spec SHA-256 / Git blob: `fe789211c6660b42265d1b164934915db50d99d0f1f6dac8d02c590f81b967d3` / `8bcfefc3c6dd0a279777664ac65eb2231aa5d7af`
- Facade SHA-256 / Git blob: `6375b303e2f6a1dabb5e84b8af6c06149651c540a02b0f52afce68943a624cb3` / `ea5746eea99f7bad2d5ad42051877c7929b99475`
- Exit code: `0`
- Stderr: empty
- Result: `8 examples, 0 failures`; runner summary `Passed: 8`, `Failed: 0`.

The eight passing scenarios cover stable/stale arena handles, foreign and stale
flat edges, malformed negative/out-of-range edges, snapshot copy/reset
generations, canonical root/text access, top-level line population, token-kind
classification, and the exact recursively traversable binary CST.

## Retained runner limitation

The focused spec itself passed. Its post-test `spipe-docgen` step did not:

1. JIT compilation failed and fell back to the interpreter with
   `HIR lowering error: Unknown variable: unsafe while lowering signal_handler_install`.
2. The interpreter fallback then reported
   `semantic: variable always_inline not found`.
3. The runner consequently printed
   `Warning: spipe-docgen failed for 1 spec file(s)` while retaining exit code 0
   for the successful focused test execution.

This receipt records existing output only; the command was not rerun to create
this file. The raw event is retained in the author rollout at ordinal 200,
timestamp `2026-08-29T20:27:36.980Z`, with stdout, empty stderr, and rc 0.
