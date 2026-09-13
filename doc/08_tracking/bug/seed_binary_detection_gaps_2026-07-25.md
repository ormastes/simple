# Bug: seed-binary detection is path-based and defeated by cosmetic misdetection

**Date:** 2026-07-25  
**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

## Problem
The `is_rust_seed_simple()` classifier in `check-hosted-wm-capture-evidence.shs` uses path substring matching (`src/compiler_rust/*`) as its sole detection criterion. A seed binary copied to a self-hosted-looking deploy path is silently accepted by evidence gates.

Aggravating: the deployed stage4 self-hosted binary itself prints the seed WARNING line in some run lanes (known cosmetic misdetection, recorded in `doc/03_plan/compiler/bootstrap/stage4_macos_deploy_2026-07-25.md`) and embeds the warning string. This links seed driver components, causing string/warning probes to misclassify the self-hosted binary as seed.

**Result:** Identification is unreliable in both directions.

## Consequence
- Deployed self-hosted binaries may be rejected or incorrectly validated
- Seed binaries with relocated paths bypass detection
- Evidence matrix gates cannot reliably distinguish self-hosted from seed runs
- Blocks reproducible evidence collection

## Fix Direction
Implement a definitive self-ID channel (e.g., `--version` reporting: `build_lane=seed|stage4-selfhosted` + `source_sha=<hash>`). Consume this across all evidence-gate scripts. Fix the cosmetic warning misdetection at its root in the deployed binary.

## Triage 2026-09-12
Rule C: record predates 2026-07-29 (>=45 days) and carries no short (<=3 min) repro; closed stale per the standing triage decision. Binary identity (not run, no repro to verify): /home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple, 50,093,192 B, 2026-09-06 09:59.
