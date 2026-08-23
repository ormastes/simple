# No lane can build a green core-C runtime capsule from `origin/main` (2026-08-24)

**Status:** OPEN, pre-existing, and blocking a whole build lane rather than one file.

## Verdict

Built from an isolated `git archive origin/main src/runtime scripts/check` export
(exported `src/runtime` tree `7b18f5cb110234ae4dda6f33c59a0338421d30ce`,
byte-identical to `origin/main:src/runtime`), so this is not a tree-mixing
artifact:

```
core_c_runtime_capsule_reason=rt-mem-guard-native-selfcheck-failed     (rc=1)
```

`scripts/check/build-core-c-bootstrap-runtime-capsule.shs` is fail-closed and
halts at the first failing self-check, so it stops at check 4 of 8. Everything
before that is green: all 13 capsule sources compiled (one pre-existing
`-Wcomment` at `runtime_native.c:11616`), the deterministic repeat-build matched,
and every `nm` provider assertion passed.

## The three failures, and what they are NOT

| self-check | rc | note |
|---|---|---|
| `rt_mem_guard_native` | 133 | SIGTRAP, empty output |
| `rt_mem_guard_stale_slot` | 133 | SIGTRAP |
| `rt_mem_guard_after_sweep` | 133 | SIGTRAP |

**Not caused by `c530678f8ba`** (the transient owner-table change). A control
capsule built from a self-consistent `c530678f8ba~1` export — no tree mixing —
dies at the IDENTICAL step with the IDENTICAL three rc=133 traps. None of that
commit's three behaviours (same-cap resize, tombstone trigger, `cap > 4096`
release) is implicated.

The checks that DO cover that commit's area pass on the same archive:
`rt_transient_heap_scope_selfcheck` — the ownership fence — **77 checks, 0
failures**; `rt_heap_ref_wellformed` 5 checks pass; `rt_string_free`,
`runtime_coverage_core` and `rt_tls13_sha256_sleep` all pass. (The last five were
run manually against the preserved archive, since the builder halts at the first
failure.)

## Why this matters beyond the capsule

The capsule is the artifact a stage-4/5 lane needs. Until these three traps are
fixed, **no lane can produce a green capsule from `origin/main`**, independent of
any compiler-side work. That is a separate blocker from the stage-3 SIGSEGV and
should not be conflated with it.

## Two premise corrections recorded so they are not re-derived

- `rt_core_register_immortal_ptr` is **`static`** (`runtime_native.c:1506`), so it
  can never appear as a global symbol. Its absence from the stage-2 binary was
  overdetermined and proved nothing; the archive MTIME was the real evidence that
  `runtime_native.c`'s half of `c530678f8ba` had never been compiled.
- Pre-commit `runtime_native.c` compiles cleanly against **its own** tree. The
  earlier `conflicting types for 'rt_msync'` / `'rt_file_lock'` failure was purely
  a tree-mixing artifact, not a property of the file.

## `runtime_native.c`'s half IS now proven to reach the artifact

Disassembly diff of `_rt_transient_array_scope_end`, current vs a pre-commit
object built with identical flags:

```
> cmp  x8, #0x1, lsl #12            (== 4096)
> b.ls ...                          (small table -> memset)
> str  xzr, [x20] ; str xzr, [x19]  (ptr = NULL, cap = 0)
> ldr  x0, [x20] ; bl <free>
```

The pre-commit object has no such compare. Source identity confirmed by
`shasum` matching `origin/main:src/runtime/runtime_native.c`. Note the capsule
compiles `runtime_native.c` only — `runtime_memory.c` is not a capsule member —
so this validates exactly the half that had never been exercised.
