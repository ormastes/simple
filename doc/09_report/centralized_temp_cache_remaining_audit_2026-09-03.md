# Centralized Temp/Cache Remaining Producer Audit

**Date:** 2026-09-03  
**Audited HEAD:** `53c00707567feb7be9fdcbadba5cdd5fd74b6176`  
**Scope:** owned, non-vendored `scripts/**` and `src/**`

## Census

A conservative lexical scan for `TMPDIR`, `/tmp/`, `mktemp`, platform cache
paths, and temporary-directory APIs found 1,340 candidate files: 863 scripts,
286 non-Rust Simple/runtime source files, and 191 owned Rust source files.
This is a candidate inventory, not a violation count: it includes tests,
fixtures, comments, examples, policy-aware `TMPDIR` projections, and cleanup
guards. Each migration slice must classify its matches before changing them.

## Implemented Slice

The compiler leak-check tool had two direct producers:

- external ASan/Valgrind work used `mktemp -d /tmp/simple_leak_check_XXXXXX`;
- runtime memtrack dumps used `/tmp/simple_leak_check_runtime.txt`.

Both now resolve beneath:

```text
${SIMPLE_WORKTREE_STORAGE_ROOT:-<cwd>/.simple/storage}/tmp/compiler/leak-check/
```

Each run receives a PID/time-qualified directory. Failure to create managed
storage fails the leak-check run rather than falling back outside the two-root
policy. Runtime dump files are deleted after parsing.

## Remaining Priority Slices

1. Test-runner daemon, coverage, doctest, and in-process evidence files.
2. Compiler interpreter JIT and SimpleOS temporary object outputs.
3. Bootstrap/check scripts that still default directly to `/tmp` or unscoped
   `mktemp`; keep already-migrated macOS M2-M5 producers out of those changes.
4. Owned Rust compiler/tool workers after the shared path contract is available
   in that implementation family.

The slices should remain independent so integration can reject or revert one
producer family without disturbing the centralized root contract.
