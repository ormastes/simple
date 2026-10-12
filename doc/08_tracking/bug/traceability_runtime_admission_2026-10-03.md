# Traceability lane lacks an admitted verification runtime

Status: OPEN prerequisite; owner: root; discovered 2026-10-03.
Feature: `simple_traceability_sdn_slop`.

## Evidence

The isolated worktree has no `bin/release` deployment. The main workspace's
usual release paths were absent at inspection. `C:/dev/simple/bin/simple.exe`
exists, but no source/build provenance was identified. `bin/simple.cmd` checks
Rust bootstrap/debug executables and may select them when release tooling is
absent (main-workspace wrapper inspected lines 6–58). Its name does not prove
a pure-Simple Stage 4 lane. WSL Ubuntu is installed, but the checked project
release-binary paths were absent there too.

This is not a failing feature test and not evidence of a newly introduced
compiler regression. No seed was executed to generate substitute results.

## Affected obligations

All compilation/runtime SSpec, docgen, production CLI/hook/runner/native UI,
whole-suite, NFR and release qualification results remain NOT RUN until the
runtime prerequisite is satisfied. Authored source, documentation, and static
review may continue; they cannot discharge these obligations.

## Unblock condition and resume

Identify an existing admitted pure-Simple Stage 4 CLI with its immutable source,
binary digest, build-input provenance and supported host; or coordinate an
authorized build with the bootstrap owner. Do not restart another session's
build or assume its retained log proves a live process. User has been asked
for an admitted local/remote runtime and receipt.

Once admitted, bind its absolute path and digest in this lane's execution ledger,
run deliberate-red/zero-executed runner calibration, then compile and execute
the focused authored specs exactly once. Use source-matched test imports from
the isolated candidate. Record commands and real receipts; then generate the
mirrored manuals and continue the complete acceptance/NFR matrix.

Unavailable hosts remain open per host criterion. An implementation handoff
must not close this prerequisite or mark the feature complete.
