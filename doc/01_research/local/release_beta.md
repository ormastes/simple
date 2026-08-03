# Release Beta Local Research

The release lane already has a strict multi-stage bootstrap owner in `scripts/bootstrap/bootstrap-from-scratch.sh`. Stages 2 and 3 compile `bootstrap_main.spl`; Stage 4 builds the full CLI and runs the redeploy and essential-tools gates; Stage 5 builds and handshakes MCP/LSP; deployed release mode runs the whole interpreter suite.

The last retained fresh build passed Stage 2 and failed Stage 3 on names imported through facade globs. The former facade traversal skipped nested globs for mixed modules; removing the gate without cycle detection caused multi-GiB growth. The main working copy now uses a per-root shallowest-depth memo and permits mixed-module traversal. Isolated strict native-build candidates compiled 728/728 modules; a fresh full chain is still required.

Existing focused release evidence is `test/01_unit/scripts/release_checker_contract_test.shs` plus `release_checker_contract_spec.spl`. It covers executable size/strip policy, notices/font/archive safety, SimpleOS scenario selection, and MCP/LSP archive identity/checksum staging. It does not prove live QEMU, a full CLI, cross-platform packages, or a GitHub workflow run.

`.github/workflows/release.yml` declares Linux x86_64/aarch64/riscv64, FreeBSD x86_64/x86, Windows x86_64/aarch64, and macOS rows. The recorded lane excludes macOS execution. Its current dirty diff weakens the full-package job by accepting an absent executable payload as source-only; that contradicts a fail-closed beta release and must not be accepted as completion.

Reusable owners:

- `scripts/bootstrap/bootstrap-from-scratch.sh` — strict bootstrap, Stage 4 qualification, MCP smoke, deploy and whole-test gates.
- `scripts/check/check-bootstrap-essential-tools-smoke.shs` — exact full-CLI command sanity.
- `scripts/check_release_payload.shs` — safe directory/archive payload validation.
- `scripts/check-mcp-release-assets.shs` — tagged MCP/LSP native payload validation.
- `scripts/check-simpleos-bootstrap-qemu.shs` and `scripts/check/check-freebsd-bootstrap-qemu.shs` — canonical QEMU entrypoints.
- `test/01_unit/scripts/release_checker_contract_{test.shs,spec.spl}` — focused release contract evidence.

Open questions: none for research; requirement scope selection remains explicit in the options documents.

## Latest remote workflow evidence

The latest `Release` run, `30682874548` at commit `4b86bfb7a84ff80d468790a9b12931739d22be8d`, failed. Linux x86_64/aarch64/riscv64 and FreeBSD x86_64 legacy package jobs passed, but both Windows rows failed during checkout, FreeBSD x86 failed during cross compilation, and the SimpleOS job failed during its full kernel build. Consequently installation testing, the full package, whole tests, GitHub release creation, and GHCR publication were skipped. This directly disproves AC-5 through AC-7 for the current remote state.
