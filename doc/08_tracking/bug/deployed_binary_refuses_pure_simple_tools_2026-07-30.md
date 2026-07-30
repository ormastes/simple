# Deployed `bin/simple` refuses `test`/`lint`/`fmt` — all spec verification blocked

**Found:** 2026-07-30 ~12:30 UTC, mid-session, on a shared working copy.
**Severity:** BLOCKER for every workflow that verifies anything. No spec can be
run repo-wide until this is resolved.
**Status:** Open. Not root-caused. Deliberately NOT "fixed" by swapping
binaries — see "Why nothing was swapped".

## Symptom

```
$ bin/simple test <any spec>
WARNING: this Rust-built Simple binary is a bootstrap seed only; do not use it as the normal tool.
Build and use the pure-Simple bin/simple instead.
error: pure-Simple tool 'test' unavailable; refusing Rust fallback
```

Per-tool probe (`<tool> --help`, counting the refusal line):

| tool | refuses? |
|---|---|
| `test` | YES |
| `lint` | YES |
| `fmt`  | YES |
| `build`| no |

So it is not test-specific: multiple pure-Simple tool entry points are
unavailable, while `build` still dispatches.

`--seed-ok` and `SIMPLE_RUST_SEED_WARNING=0` do NOT bypass it (both tried);
the refusal is independent of the seed *warning* suppression knobs.

## Timeline / what is known

- `bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` (symlink, unchanged since 07-25).
- That target is **154 MB, mtime 07-30 09:08** — i.e. it was REPLACED during
  this session. Earlier the same day, `bin/simple test` ran specs normally
  (many green Results lines were collected before ~09:08).
- The current target self-reports as a **Rust seed** ("this Rust-built Simple
  binary is a bootstrap seed only"), which `.claude/rules/bootstrap.md`
  explicitly forbids in this slot: "NEVER copy Rust bootstrap binary to
  `bin/release/simple`", and seed-as-`bin/simple` is "an emergency stopgap
  only, never the resting state; record a bug when you do it." This doc is
  that record.
- The adjacent rollback candidate
  `bin/release/x86_64-unknown-linux-gnu/simple.deployed-noLLVM-2026-07-29.bak`
  (57 MB, 07-29 06:00) **also** self-reports as a Rust seed, so it is not a
  known-good pure-Simple restore point either. Note memory
  `reference_deployed_binary_lost_llvm_codegen_2026-07-29`: 57 MB = the
  no-LLVM build, 154 MB = canonical size.
- The refusal string appears in **neither** `src/` nor `src/compiler_rust/`
  (`grep -rn "refusing Rust fallback"` → no hits), so the running binary was
  built from a source state that is not the current tree. That is itself worth
  chasing: it means the deployed binary cannot be reproduced from HEAD.

## Why nothing was swapped

Restoring a binary in a shared working copy that other sessions are actively
using is an outward-facing change, and the only rollback candidate is also a
seed, so a swap would trade one broken state for another while destroying
evidence. The correct repair is a real bootstrap redeploy producing a genuine
pure-Simple binary — which currently needs a working stage 3 (see
`stage4_memory_parallel_agent_plan_2026-07-29.md`, L7 run history).

## Impact on the memory-infra campaign

Verified-and-landed work is unaffected (it was verified before the breakage).
Held back pending a working runner, because it must not land unverified:

- `src/compiler/80.driver/driver_source_loading.spl` — symlink double-parse
  dedup (`_driver_canonical_source_path` → `_driver_physical_source_key`).
  A compiler-path change; agent-reported 1/1 on a new symlink-fixture spec,
  not independently re-verified.
- `test/01_unit/compiler/bootstrap/entry_closure_symlink_physical_source_dedup_spec.spl` (new).
- `src/app/mem/{live_poll,main}.spl` + `test/03_system/app/mem_cli_spec.spl` —
  `simple mem top --pid` live polling; agent-reported 10/10.

## Next step

1. Determine what makes a pure-Simple tool "available" to the dispatcher (the
   check lives in the deployed binary, not in HEAD — start from `build` being
   the one tool that still dispatches).
2. Produce a genuine pure-Simple binary via bootstrap and deploy it.
3. Re-verify the held changes above before landing them.
