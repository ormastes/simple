<!-- codex-design -->
# Next Beta Full Bootstrap and SimpleOS Multiarch Detail Design

## No UI

This is release automation and environmental verification. No TUI or GUI
surface is added.

## Frozen workflow interfaces

Required job IDs:

- `check-version`
- `build-bootstrap`
- `build-freebsd-bootstrap`
- `bootstrap-memory`
- `whole-tests`
- `simpleos-build`
- `simpleos-mission-critical`
- `release-preflight`
- `create-release`
- `verify-release`

Required SimpleOS architecture IDs:

- `x86_64`
- `aarch64`
- `riscv64`

Required receipt prefix: `release_gate_`.

Required manual step text:

- `Validate immutable beta2 identity`
- `Prove full self-hosted bootstrap`
- `Build and boot SimpleOS release targets`
- `Check resource regression receipts`
- `Publish and inspect the GitHub prerelease`

Test helpers:

- `read_required(path)`
- `expect_marker(source, marker)`
- `expect_absent(source, marker)`

These names are fixed before any sidecar work. No placeholder helper may pass
silently.

## 1. Version and tag validation

Modify `check-version` to expose `version` and `prerelease`. On a tag event:

```text
EXPECTED_TAG=v${VERSION}
GITHUB_REF_NAME must equal EXPECTED_TAG
```

Manual dispatch uses `VERSION`, never a branch ref. Release preparation updates
all canonical version sources discovered by a single maintained version
consistency checker. The release skill is updated to name that checker rather
than keep another stale handwritten list.

## 2. Bootstrap matrix

Replace fallback behavior inside the existing `build-bootstrap` job:

- native runner rows run `bootstrap-from-scratch.sh --full-bootstrap`;
- required emulated rows run the same route inside their canonical emulator/VM;
- every row checks the produced binary identity and a small compile/run probe;
- packaging copies only that checked binary;
- missing runtime uses `if-no-files-found: error`;
- `|| true`, source-only success, and committed-binary substitution are removed.

Do not duplicate the target matrix in Simple source. Workflow rows point to
existing bootstrap targets and platform workflows.

If a currently advertised row cannot produce a full bootstrap after three
fix cycles, the release remains blocked; it is not silently downgraded.

## 3. SimpleOS matrix

Convert `simpleos-build` to a required matrix with static rows:

### x86_64

- run `scripts/check-simpleos-bootstrap-qemu.shs --full`;
- collect the kernel, boot image, transcript, in-guest compiler transcript,
  checksums, and receipt.

### AArch64

- run the existing AArch64 attested builder and catalog QEMU scenario;
- run `scripts/ci/build-simpleos-toolchain.shs --require-all` for the target;
- collect kernel/FAT32 image, transcript, compiler transcript, checksums, and
  receipt.

### RISC-V64

- run the existing RISC-V64 catalog scenario and serial-shell checker;
- run the target-native compiler builder with `--require-all`;
- collect kernel/FAT32 image, transcript, compiler transcript, checksums, and
  receipt.

Each row fails if any expected file or receipt key is absent. Package names are:

- `simpleos-1.0.0-beta2-x86_64.tar.gz`
- `simpleos-1.0.0-beta2-aarch64.tar.gz`
- `simpleos-1.0.0-beta2-riscv64.tar.gz`

## 4. Memory and performance

Add required `bootstrap-memory` steps for:

- `check-stage4-memory-gate.shs`;
- `check-stage4-selfhost-parse-memory.shs`;
- `check-stage4-selfhost-parse-memory-multifile.shs`.

Use the existing GNU-time measurement pattern to emit elapsed seconds and peak
RSS. Upload logs on success and failure. Define
`RELEASE_PERF_REGRESSION_PERCENT=10`.

The first green run writes a baseline artifact keyed by runner label, target,
backend, and command. Comparison activates only when an exact-key baseline is
available. Missing metrics always fail; a missing first baseline does not.

The reproduced broad MCP workspace-symbol 100 MB timeout is tracked separately
unless its owning concurrent lane merges before release. It becomes a release
blocker only if the release/bootstrap hot path invokes it.

## 5. Release preflight

`release-preflight` downloads artifacts from all required jobs and performs:

1. exact expected-name comparison;
2. nonempty file checks;
3. SHA-256 verification;
4. `scripts/check_release_payload.shs` on language packages;
5. receipt schema/status/commit/version/architecture checks;
6. `scripts/check/check-simpleos-mission-critical-release.shs`;
7. confirmation that `release_blockers=none`.

No glob-only collection is accepted as inventory validation. Globs may copy
files only after the exact-name check passes.

## 6. Publication and verification

`create-release` runs only after preflight and whole tests. It publishes
`v1.0.0-beta2` with `--prerelease`.

`verify-release` uses GitHub CLI/API read-only queries to validate:

- tag `v1.0.0-beta2`;
- `isPrerelease=true`;
- target commit equals the workflow tag commit;
- all expected assets exist exactly once;
- checksums are downloadable and valid;
- the release URL is retained in the job summary.

GHCR publication, if retained, uses an immutable beta2 tag and does not move
`latest`.

## 7. Local execution order

1. focused workflow/source contract spec;
2. version consistency checker without changing the version;
3. local Linux x86_64 full bootstrap;
4. stage-4 memory checks;
5. SimpleOS x86_64 full gate;
6. cross/emulated AArch64 and RISC-V64 SimpleOS gates;
7. FreeBSD QEMU full bootstrap;
8. whole test suite once;
9. verify PASS;
10. update version/changelog, commit, and tag locally;
11. ask for push approval;
12. push and inspect GitHub Actions/release;
13. fix/retry at most three cycles.

macOS and Windows native rows run on GitHub Actions.

## Error handling

- Missing tool: fail with the tool name and setup hint.
- Seed/stale runtime: fail before packaging.
- Timeout/OOM: preserve cache and logs, fail the row.
- Missing artifact/receipt/digest: fail preflight.
- Mission-critical blocker: fail before release creation.
- GitHub partial publication: keep the immutable tag/release state visible,
  repair through a new bounded workflow attempt; never move the tag.

## Documentation updates during implementation

Update:

- `.codex/skills/release/SKILL.md` and equivalent release commands;
- release/platform guide pages under `doc/07_guide`;
- generated SPipe manual for this feature;
- release notes and `CHANGELOG.md` only after verification.
