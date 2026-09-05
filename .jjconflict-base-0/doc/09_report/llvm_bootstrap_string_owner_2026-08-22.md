# LLVM bootstrap string-global ownership evidence (2026-08-22)

Scope: `MirToLlvm.add_string_global` and the two LLVM trailer emitters.

## Correctness and concurrency

- The process-global mutable `_llvm_bootstrap_string_global_text` and its
  reset/read/append functions are removed.
- Both normal and direct-bootstrap trailer paths read the owning translator's
  `string_global_text` field.
- The unit regression interleaves writes to two translators and proves exact
  declaration counts and no cross-owner contamination. A source-contract
  regression rejects restoration of the process-global accumulator.

## Performance and memory model

For `N` declarations of equal encoded length `D`, each cumulative text chain
copies `D * N * (N + 1) / 2` bytes (newline bytes omitted from both rows).

| Path | Cumulative chains | Modeled copied bytes, N=10,000/D=80 | Final retained declaration payload |
|---|---:|---:|---:|
| Before | 2 (process global + translator) | 8,000,800,000 | 3 copies (global, translator, array) |
| After | 1 (translator only) | 4,000,400,000 | 2 copies (translator, array) |

The change therefore removes 50% of cumulative text-copy traffic and one final
payload copy in bootstrap mode. Dispatch also loses one environment lookup and
one helper call per declaration. Ordering and emitted LLVM text are unchanged.

The focused executable test could not run because this worktree has no
`bin/simple` or deployed release binary. Per the compiler-recovery constraint,
the Rust seed was not substituted and no full compiler build was started.
Source-contract checks and `git diff --check` passed.
