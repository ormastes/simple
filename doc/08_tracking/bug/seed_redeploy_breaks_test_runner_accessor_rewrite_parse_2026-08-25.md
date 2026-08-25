# Seed redeployed 2026-08-25 05:16 UTC cannot parse `tooling/easy_fix/accessor_rewrite.spl` — `bin/simple test` and md doctests abort

**Status:** OPEN (observed; owner = the session that redeployed). **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple`, 60,641,352 bytes, mtime 2026-08-25 05:16:29.

## Symptom
Every `bin/simple test <spec|md>` — including the trivial fixture `test/fixtures/doctest/green.md`
which passed at 04:5x on the previous seed — now aborts before executing anything:
```
error: compile failed: parse: in ".../src/lib/nogc_sync_mut/tooling/easy_fix/accessor_rewrite.spl": Unexpected token: expected Colon, found If
```
`accessor_rewrite.spl` is unmodified in the working tree (clean vs HEAD, mtime 2026-08-24 22:10);
the previous seed (`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple`,
60,650,360 bytes, 2026-08-23 04:47) parses it and runs the same doctests green. So the regression is
in the redeployed seed's parser (or a grammar change that landed in `src/compiler_rust` without the
stdlib file being updated), not in the stdlib.

## Impact
No spec or md doctest can be executed through the deployed `bin/simple` on this box until fixed;
`run` of ordinary programs still works. Workaround used by the GPU hardening session: run
`test`/doctests through the 08-23 seed above.

## Reproduce
`bin/simple test test/fixtures/doctest/green.md` → exit 1 with the parse error;
`/mnt/data/worktrees/goal-main-1/bin/release/x86_64-unknown-linux-gnu/simple test test/fixtures/doctest/green.md` → `SDoctest Results: 1 total, 1 passed`.
