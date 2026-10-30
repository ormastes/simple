# Linux bootstrap archiver prerequisite fails too late

Status: implemented; focused shell regression passed; full bootstrap not rerun.

The reviewed Linux stage2 attempt compiled 1616 native units successfully, then
failed creating the core-C runtime archive because `llvm-ar` was unavailable.
The native Rust owner correctly rejects GNU `ar`; the shell preflight had not
checked that prerequisite. This is separate from Cranelift handle diagnostics.

Added an early Linux prerequisite using the exact non-Windows native tool
candidate order and successful `--version` probe. Do not substitute `AR`, relax
the native owner, alter tool authority receipts or claim Stage2 admission.

Validation: `sh scripts/bootstrap/tests/preflight-authority-milestone-test.shs`
passed the existing two progress/error routing cases and new archiver cases:
real working/broken/absent executable probes; missing all four candidates with
AR set to a working executable refuses; second candidate wins in native order;
PATH llvm-ar is accepted only after preceding candidates fail. The isolated
existing routing fixture needed its newly introduced unrelated cache-lock
helper stubbed and empty shared-cache context set. No production lock changed.

The check runs after the seed-only exit, before pure-stage source compilation,
and only on Linux. It is prerequisite availability, not tool-byte authority,
Stage2 qualification or full manager acceptance. Existing archive discovery and
strict owner remain authoritative at use time. Tool authority schema alignment
is separate: its generic ar role still does not itself prove native LLVM archive
tool selection. The live frozen Linux source and cache were not modified.

Original Linux terminal evidence: `/work/bootstrap-stage2-p2-diagnostic-retry-20261029/logs/aarch64-unknown-linux-gnu/stage2-native-build.log`,
SHA-256 `ba10082764a5c48a4dabd2f1aba0e46304542c91e03d4e6cd30327ba58ced74d`.
Native closure reported `compiled=1616 reused=0 failed=0`; subsequent core-C
archive creation failed for missing LLVM archiver. No P2 link/publication or
native compiler qualification is claimed from that run.
