# Self-hosted stage4 `run` (interpreted) drops string interpolation

**Status:** open, blocking self-hosted deploy. **Filed:** 2026-07-30.

## Symptom (PROVED, reproduced twice, isolated from seed delegation)

A freshly-built pure-Simple self-hosted "full CLI" binary (stage4, entry
`src/app/cli/main.spl`, 726→1490-file entry closure, cranelift backend,
source commit `9ea0b39962d76929ac58598d837f9292f3ebf6af`) silently drops
string interpolation when running a script via `run` (the interpreted
path), but only when genuinely self-hosted -- confirmed via the binary's
own `seed sibling not found, skipping delegation:
.../build/bootstrap/simple_seed` message, which proves no fallback to the
Rust seed occurred.

Minimal repro:
```simple
fn main():
    val x = 5
    print("x={x}")
```
Expected: `x=5`. Actual (self-hosted, no delegation): `x={x}` (the literal
placeholder, uninterpolated).

**Delegation masks this.** When run from a working directory where the
relative `build/bootstrap/simple_seed` sibling path happens to resolve to
an existing file, the CLI silently delegates to the Rust seed and prints
the correct `x=5` -- looking like a pass while the self-hosted binary's own
interpreter never actually ran. `-c 'print("x={x}")'`-style one-liners hit
this same delegation path in every test run in this session and are **not
reliable evidence** the self-hosted binary works; only a `run` invocation
from a directory with no reachable seed sibling isolates the self-hosted
binary's own behavior.

## What still works (self-hosted, no delegation, confirmed)

- `check src/app/cli/bootstrap_main.spl` -> `OK` (source parses/type-checks).
- `run` on a script with **no interpolation** (`print("hello from stage3
  self-hosted")`) prints correctly.
- Plain arithmetic (`val x = 2 + 3`) evaluates correctly; only the `{x}`
  substitution inside a string literal is dropped.

## Provenance of the binary that exposed this

- Built manually, stage-by-stage, after two blockers in
  `scripts/bootstrap/bootstrap-from-scratch.sh --full-bootstrap --deploy`
  itself (see the companion report in this pass's landing commit message /
  session record):
  1. A fresh `git worktree` has no `src/compiler_rust/target`; the
     script's own Rust-seed-input fingerprint hard-rejects a **symlink**
     anywhere under `src/compiler_rust`/`src/runtime` (by design --
     `scripts/check/lib/bootstrap-stage3/authority.shs`'s `find ... -type
     l -print -quit` check). A worktree-wide `target` symlink trips it;
     a real `target/` directory containing a symlinked `target/bootstrap`
     subdirectory does not (the walk prunes at the `target` boundary).
     Fixed by making `target/` a real directory before symlinking
     `target/bootstrap` inside it.
  2. `bootstrap_stage3_directory_snapshot` likewise refuses to snapshot a
     symlinked runtime directory (`error: could not snapshot Rust runtime
     authority`) once the seed was rebuilt through the symlink -- fixed by
     physically copying `target/bootstrap` (4.7G) into the worktree
     instead of symlinking it, after which the freshly-built seed
     satisfied every authority check.
  3. The default `--backend=llvm` seed build (via `--full-bootstrap`) did
     not compile in LLVM support (`error: native backend 'llvm' is not
     available in this build`) even though the platform script detected
     LLVM 18 -- matches the already-documented
     `doc/08_tracking/bug/seed_stage2_llvm_method_symbol_lowering_2026-07-17.md`
     family; using `--backend=cranelift` explicitly (the documented
     working stage-2/3 path per `.claude/rules/bootstrap.md`) resolved it.
- After those three fixes, the wrapper script's own "Stage 2" step still
  reported `stage2 native-build failed (exit 1)`, but its own
  `stage2-native-build.log` was stale (mtime predated this session's
  runs by hours) -- **not root-caused**; a hand-invoked `native-build`
  with materially the same flags (`--source src/compiler --source
  src/app --source src/lib --entry-closure --entry
  src/app/cli/bootstrap_main.spl`, cranelift) succeeded cleanly (726
  files, 98.5s, exit 0) from the same worktree/seed/cache root.
- Stage 3 (stage2 self-hosting: stage2 binary recompiling the identical
  source) succeeded identically (726 files, same 22330944-byte output
  size as stage2, sha differs -- expected, embedded build metadata).
- Stage 4 (full CLI, `main.spl` entry) succeeded: 1490 files, 26709488
  bytes, 251s (147.5s compile + 103.6s link), peak observed RSS ~1.1GB
  (nowhere near the ~65GB/64GB-cap historical peak -- no memory-cap risk
  this run). `sha256: 39a507b917c8d05583c386a7f2a27d195ddb0ecc0a702de487
  e07aff51378483`. `strings | grep -c llvm::` = 0 (expected, cranelift).

## Deployment decision

**Not deployed.** A binary that silently drops string interpolation would
regress `bin/simple` for every session on this host -- `"{var}"` syntax is
used pervasively throughout the codebase, including in this very
investigation's own smoke-test output. The existing live
`bin/release/x86_64-unknown-linux-gnu/simple` (the LLVM-enabled Rust seed
redeployed earlier this campaign) is unchanged; a named rollback copy
(`simple.rollback-llvm-seed-2026-07-30`, identical 154094616 bytes) was
taken before this attempt in case a deploy had been warranted.

## "Verify early" result (per this pass's explicit instruction)

**Confirmed: the bootstrap entry closure does NOT pull in
`src/lib/common/web`.** Every successful native-build in this pass (stage
2/3 at 726 files, stage 4 at 1490 files) reported its own file count and
neither matches or approaches the scope that would include
`browser_renderer_protocol.spl`'s dependents; `browser_renderer_protocol.
spl`'s own parse defect (separately fixed at `023a60a05aa`, verified
ancestor of this build's `9ea0b39962d`) was never at issue here regardless.

## Next step (not attempted, root-cause needed)

Root-cause where string interpolation is lost in the self-hosted
interpreter path specifically (compiled/native paths appear unaffected --
the stage4 binary itself, and the seed, both interpolate correctly; only
running an *interpreted* script through the self-hosted binary's own `run`
loses it). Likely candidates by file naming convention:
`src/compiler/95.interp/` (interpreter) or the string-template
lowering/codegen shared between interpreted and compiled paths, given
compiled output does not show this bug. Not chased this pass -- this
report is the deliverable per the "precise account of the wall it hits"
instruction.
