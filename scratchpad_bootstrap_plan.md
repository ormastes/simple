# Bootstrap Fix Plan (priority: make bootstrap complete + deploy pure-Simple)

## Goal
`scripts/bootstrap/bootstrap-from-scratch.sh --pure-simple --deploy` completes and
deploys a working self-hosted `bin/release/<triple>/simple`.

## Shipped already
- env-cache hang fix (7f00aaf0) — un-hung stage2
- parse_f64 JIT fix (db0196ec3)
- native_build_main.spl worker resolution (in origin)

## Strategy (lazy: fix the ONE current first-failure, loop)
Do NOT pre-fix every seed bug. Each iteration:
1. Run `--pure-simple` bootstrap, capture FIRST hard failure to a log.
2. Fix that single root cause (prefer .spl; seed Rust only if unavoidable).
3. Rebuild seed only if Rust changed. Re-run. Repeat until stage4 deploys.
4. Smoke test: `bin/simple -c "print(1+1)"` -> 2; `bin/simple lint <f>` no coredump.
   Backup seed first; restore if broken.

## Known blockers (from prior sessions, verify each is still live)
- stage3 self-host = intentional stub in bootstrap_main.spl -> stage4 built by seed directly
- optional-array `.len()` on `[text]?` (Some-wrapping 60fd804c) -> interp returns 0.0
- codegen AMBIGUOUS-METHOD (~50: .insert x42, .set, .clear, .close, .as_str, .get_local)
- parser gap `[text]?:`
- stage4 codegen `cannot parse '0.0' as i64` (separate path from interp .len bug)

## Current step
Re-run bootstrap, find the CURRENT first failure (may have shifted post-fixes).
