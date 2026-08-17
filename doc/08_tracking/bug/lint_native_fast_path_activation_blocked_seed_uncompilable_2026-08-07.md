# lint native fast path landed but unactivated — seed rebuild blocked by pre-existing E0425s

**Date:** 2026-08-07
Status: OPEN (P2)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

## What landed

`bin/simple lint <anything>` pays a fixed ~4.5s / ~340MB startup tax per
invocation: the seed driver dispatches `lint|fmt|fix` to
`src/app/cli/lint_entry.spl` via raw-source parse+JIT of the whole lint closure
(~380 `.spl` files, including the entire `fix` tool subtree). Measured medians
(3 runs, `/usr/bin/time -v`): 2-line file 4.69s / 344MB; real compiler file
5.73s / 336MB. This violates `.claude/rules/code-style.md` ("Production
wrappers should execute cached compiled artifacts, not raw source").

Fix (same pattern as the July MCP native-server conversion):

1. `scripts/build/build-lint-native.shs` — native-builds the lint entry closure
   into `simple_lint`, smoke-gates it, deploys to
   `bin/release/<triple>/simple_lint` (+ sha256 sidecar).
2. `src/compiler_rust/driver/src/main.rs` — `try_cached_lint_native()` at the
   top of `dispatch_to_simple_app`: execs the deployed `simple_lint` when it is
   present AND at least as new as every `.spl` under the lint/fix/fmt source
   roots (mtime check); falls back to the raw-source path otherwise.
   `SIMPLE_LINT_NATIVE=0` opts out.
3. `src/app/cli/lint_entry.spl` — accepts `simple_lint` as argv[0] so the same
   entry works raw-source and native.

## Why it is NOT active yet

The Rust hook only takes effect after the seed driver binary is rebuilt and
redeployed, and that is blocked twice over:

- **Pre-existing seed compile break on origin/main:** `cargo check -p
  simple-compiler` fails at `compiler/src/interpreter_extern/mod.rs:557-558`
  with E0425: `rt_dict_free_deep_fn` / `rt_free_deep_fn` missing from
  `sffi_array` (verified in a pristine worktree of origin/main, commit
  d5e9913ea8a — unrelated to this change; the hook itself compiles clean
  standalone under rustc 2021).
- **Stage 3 self-host is blocked** (see
  `doc/08_tracking/bug/t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`),
  and per `.claude/rules/bootstrap.md` hand-copying a fresh cargo seed over the
  shared `bin/release/<triple>/simple` is forbidden.

## Activation steps (once the seed compiles again)

1. Fix/absorb the `sffi_array` E0425s (whichever session owns that lane).
2. Rebuild the seed via the documented route (`scripts/bootstrap/...`), NOT an
   ad-hoc cargo copy.
3. `sh scripts/build/build-lint-native.shs` to build+deploy `simple_lint`.
4. Verify: `bin/simple lint <file with known STUB002>` output identical to the
   raw-source path, and cold `/usr/bin/time -v` wall drops from ~4.5s to
   sub-second.

Until then the deployed `bin/release/<triple>/simple_lint` artifact can be
invoked directly (`simple_lint lint <targets>`) to skip the tax.

## Re-verification 2026-08-09

Status confirmed **ARCHITECTURAL-OPEN**. This worktree has no deployed
`bin/simple`/seed binary at all (known worktree-isolation limit — see
`.claude/memory` note on worktree agents lacking `bin/simple`), so the
blocking `cargo check -p simple-compiler` E0425 at
`interpreter_extern/mod.rs:557-558` could not be independently re-probed from
here. The fix this doc describes is already landed (the native-lint build
script, the driver's `try_cached_lint_native` hook, and the `lint_entry.spl`
argv[0] dispatch) — what remains is activation, gated on a seed rebuild that
is itself blocked by an unrelated, pre-existing Rust compile break plus the
Stage 3 self-host block. Both blockers are owned by other tracked docs
(`t3_full_bootstrap_stage3_unresolved_type_byteorder_cache_validator_2026-08-06.md`)
and are out of scope to fix here per `.claude/rules/bootstrap.md` (no ad-hoc
seed hand-copy). No code changed.
