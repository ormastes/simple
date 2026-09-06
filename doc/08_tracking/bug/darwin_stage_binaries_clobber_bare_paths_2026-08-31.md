# Darwin Mach-O stage binaries clobber the bare bootstrap stage paths

**Date:** 2026-08-31
**Status:** ROOT CAUSE FIXED (deploy path); tracked artifacts still wrong at
origin/main pending a Linux bootstrap redeploy (separately blocked — no
pure-Simple full-CLI compiler is deployed; `bin/simple` is the Rust seed by
its own banner). The runnable-stage gate stays honestly RED.

## Measured evidence (origin/main, Linux x86_64 host)

| tracked path | format | verdict |
|---|---|---|
| `bootstrap/stage1/simple` | Mach-O 64-bit arm64 | WRONG — bare path must be host-native |
| `bootstrap/stage2/simple` | Mach-O 64-bit arm64 | WRONG |
| `bootstrap/stage3/simple` | Mach-O 64-bit arm64 | WRONG |
| `bootstrap/stage3/x86_64-unknown-linux-gnu/simple` | ELF x86-64 | correctly scoped |
| `bootstrap/stage3/aarch64-apple-darwin-macho/simple` | Mach-O 64-bit arm64 | correctly scoped |

Linux cannot exec a Mach-O: every probe of the bare paths returns rc=2
("exec format error"), which `check-stage-binaries-runnable.shs` classified as
`fail,rc=2` — reading as a *crashing compiler*. That misclassification misled a
prior investigation into chasing a SEGV (rc=139) that is GONE from the current
tree.

## Root cause

`src/compiler_rust/driver/src/cli/commands/misc_commands.rs`:
`bootstrap_stage_output_path` wrote stage1/2/3 outputs to the BARE
`bootstrap/stageN/simple` paths regardless of host — only the final deploy step
(`bootstrap_stage3_deploy_path`) was triple-scoped. A macOS session running
`build bootstrap` therefore wrote Mach-O artifacts at the unscoped paths, and
because those paths are git-tracked and shared across platforms, the commit
clobbered them for every non-darwin host.

## Fix

1. **Deploy path (root cause):** `bootstrap_stage_output_path` now ALWAYS
   triple-scopes every stage output (`bootstrap/stageN/<host-triple>/simple`,
   via the shared `bootstrap_host_triple()`); the bare paths are never written
   by the tool again. `deploy_verified_bootstrap_stage` guards against the
   now-possible self-copy (fs::copy truncate hazard). Reproduce test
   `stage_outputs_are_triple_scoped_never_bare` in `misc_commands.rs` — FAILS
   against the pre-fix bare-path body, PASSES after.
2. **Gate honesty:** `scripts/check/check-stage-binaries-runnable.shs` now
   inspects the artifact's magic bytes before any exec attempt:
   - foreign format at a bare path → offender
     `wrong-architecture-for-host-at-unscoped-path(deploy-clobber,<fmt>)`,
     never "crashed";
   - foreign format correctly scoped under a non-host triple dir → named SKIP,
     counted separately, never counted as passing;
   - zero executed binaries (even with skips) → `ERROR — nothing was checked`.
   Selftest gains 3 fixtures (must-FAIL bare clobber, must-SKIP scoped foreign,
   must-ERROR all-skipped); 9/9, fatal, runs before every scan.

## Before/after gate verdicts (measured, `--rev origin/main`)

Before:
`FAIL — 15 invocation(s) executed across 5 binary(ies), 13 crashed/failed: bootstrap/stage1/simple:--version(fail,rc=2) ...` (misleading)

After:
`FAIL — 3 invocation(s) executed across 1 binary(ies), 4 crashed/failed/wrong-arch: bootstrap/stage1/simple:wrong-architecture-for-host-at-unscoped-path(deploy-clobber,macho) bootstrap/stage2/simple:... bootstrap/stage3/simple:... bootstrap/stage3/x86_64-unknown-linux-gnu/simple:native-build(fail,rc=1) (1 foreign-triple scoped artifact(s) skipped, not counted as passing: bootstrap/stage3/aarch64-apple-darwin-macho/simple:foreign-triple(macho))`

Note the after-verdict also surfaces a REAL residual defect the noise was
hiding: the correctly-scoped ELF `stage3/x86_64-unknown-linux-gnu/simple`
fails `native-build` with rc=1. That is a genuine artifact problem, kept red
with an accurate reason; repairing it needs the (blocked) bootstrap redeploy.
The historically documented SEGV (rc=139) no longer reproduces anywhere.

## What was NOT done, and why

The wrong-arch bare blobs were not deleted or replaced: a correct Linux stage
artifact can only come from a legitimate bootstrap run, which is blocked (no
pure-Simple compiler deployed). Fabricating or copying binaries would repeat
the incident pattern. The gate stays RED with the accurate reason until a
Linux redeploy lands triple-scoped artifacts.

Related: `doc/08_tracking/bug/stage3_native_build_and_compile_segv_on_hello_world_2026-08-18.md`
(carries the darwin-blob class split from this session).
