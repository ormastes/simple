# Darwin Mach-O stage binaries clobber the bare bootstrap stage paths

**Date:** 2026-08-31
**Status:** RESOLVED 2026-09-12 (macOS aarch64 lane, this worktree). The three
bare Mach-O blobs are gone from the tracked tree and the guard now refuses to
let one back in. See "Resolution" at the bottom.

Previously: ROOT CAUSE FIXED (deploy path); tracked artifacts still wrong at
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

## Resolution (2026-09-12, aarch64-apple-darwin)

The "what was NOT done" paragraph above rested on a premise that turned out to
be false. It assumed the bare blobs held content that would be lost if removed.
Measured:

```
$ shasum -a 256 bootstrap/stage{1,2,3}/simple \
                bootstrap/stage3/aarch64-apple-darwin-macho/simple
e0f02a66389911f1b805f4981a68ef2a244ff139f063480e2c91cccc1740a9c3  (all four)
```

All four tracked artifacts are the SAME BYTES. The bare paths therefore carried
no information that the already-correctly-scoped
`bootstrap/stage3/aarch64-apple-darwin-macho/simple` did not already carry, so
removing them fabricates nothing and loses nothing.

Done, with no binary rebuilt or copied:

- `bootstrap/stage1/simple` -> `bootstrap/stage1/aarch64-apple-darwin-macho/simple`
- `bootstrap/stage2/simple` -> `bootstrap/stage2/aarch64-apple-darwin-macho/simple`
- `bootstrap/stage3/simple` deleted (exact duplicate of the scoped darwin path)

Both surviving readers of the bare paths already prefer a triple-scoped
candidate and fall through when one is absent, so neither needed an edit:
`scripts/lib/simple-compiler-select.shs:105,111` globs `stage3/*/simple` and
`stage2/*/simple` ahead of the bare spellings, and
`scripts/check/check-stage-phase-test-capability.shs:100` tries
`stage3/${SIMPLE_TRIPLE}/simple` first.

### The ratchet that keeps it fixed

The guard's format-first classification could only catch a bare blob that was
FOREIGN to the running host. On the very host that ran the clobbering deploy the
bare blob is host-native, so it was probed like a healthy artifact — which is
precisely why this kept re-landing from macOS sessions and was only ever visible
from Linux. Since the deploy tool always triple-scopes now
(`bootstrap_stage_output_path`), a bare binary artifact is residue *by
construction*, independent of format.

`scripts/check/check-stage-binaries-runnable.shs` now flags any binary artifact
at an unscoped `bootstrap/stageN/simple` path as
`unscoped-stage-path(deploy-clobber-residue,<fmt>)`, after the existing
foreign-format arm so the more specific wrong-architecture reason still wins
where it applies. Script stand-ins are exempt, which costs no coverage (a real
stage artifact is never a script) and is what lets the fixtures use them.

Selftest 9 -> 11 fixtures, fatal, runs before every scan:

- **fixture10 (reproducing)** — a HOST-NATIVE binary blob at a bare stage path
  must FAIL with `unscoped-stage-path`. This is exactly the half fixture 7
  cannot reach.
- **fixture11 (generalization)** — the SAME host-native blob correctly scoped
  under this host's own triple must not be flagged for its path shape; it is
  probed on its merits. Pins the ratchet to the PATH SHAPE, not to a platform.

Sabotage triple (each mutation run through the real selftest):

| mutation | result |
|---|---|
| ratchet block deleted | 10/11 — `fixture10(reason-not-unscoped: ...:--version(fail,rc=126) ...)` |
| script exemption dropped | **3/11** — the script stand-ins are correctly load-bearing |
| condition widened to scoped paths too | 10/11 — `fixture11(flagged-unscoped: bootstrap/stage8/aarch64-apple-darwin-macho/simple:unscoped-stage-path(...))` |

### Evidence

```
$ sh scripts/check/check-stage-binaries-runnable.shs --selftest
check-stage-binaries-runnable: selftest 11/11 fixtures correct
PASS — selftest only, no scan requested (11 fixture(s) correct)

$ sh scripts/check/check-stage-binaries-runnable.shs     # before
FAIL — 12 invocation(s) executed across 4 binary(ies), 4 crashed/failed/wrong-arch:
  bootstrap/stage1/simple:native-build(fail,rc=1) bootstrap/stage2/simple:... 
  bootstrap/stage3/aarch64-apple-darwin-macho/simple:... bootstrap/stage3/simple:...

$ sh scripts/check/check-stage-binaries-runnable.shs     # after
FAIL — 9 invocation(s) executed across 3 binary(ies), 3 crashed/failed/wrong-arch:
  bootstrap/stage1/aarch64-apple-darwin-macho/simple:native-build(fail,rc=1)
  bootstrap/stage2/aarch64-apple-darwin-macho/simple:native-build(fail,rc=1)
  bootstrap/stage3/aarch64-apple-darwin-macho/simple:native-build(fail,rc=1)
  (1 foreign-triple scoped artifact(s) skipped, not counted as passing:
   bootstrap/stage3/x86_64-unknown-linux-gnu/simple:foreign-triple(elf-x86_64))
```

Note two things about the "after" verdict. The bare-path offenders are gone and
every remaining probe names a correctly-scoped artifact — that is this bug's
oracle, met. Also, the historically documented SEGV (rc=139) does NOT reproduce:
all three darwin artifacts answer `--version` AND `compile` cleanly, which is
why 9 invocations produce only 3 offenders.

### Residual, stated rather than papered over

The guard stays RED, for one honest and unrelated reason. Reproduced by calling
the artifact (never by `strings`):

```
$ bootstrap/stage3/aarch64-apple-darwin-macho/simple native-build -o out h.spl
error: bootstrap_main cannot emit a seed-wrapper fallback for out
error: rebuild with the full Simple driver so native-build uses real Simple lowering/codegen
rc=1
```

That is a deliberate refusal, not a crash: these artifacts were staged without
the full Simple driver. Repairing it needs a bootstrap redeploy, which is
tracked separately in
`bootstrap_macos_blocked_seed_compile_and_linux_only_stage3_authority_2026-09-06.md`.
Promotion of this guard from ADVISORY to MANDATORY still waits on that.
