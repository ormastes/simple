# Historical bootstrap failure evidence

These three files are byte-identical copies of existing legacy `.env` receipts, retained as historical evidence rather than new configuration. They were read and hashed during the 2026-11-03 KST P0 inventory. No commands from these files were executed, and no new compiler test is claimed.

| File | SHA-256 |
|---|---|
| `stage2-rejection.env` | `f5e46d7700cb0fd249f67a8c5e6acfef9573fe33f8fb9319480a22eb87d10f1c` |
| `stage2-verification-summary.env` | `eb785c1f15d4d2284292b1838189955e5aadc8c0a884794c1d656f56e07d0832` |
| `stage2-process.env` | `bd1f3a298e7c34a55ceef1a147f08ee0211c2de9f65800e94b09eb464c214c9a` |

Original root: `/private/tmp/simple-tuple-value-contract-20261101/build/cross-bootstrap/tuple-value-contract/worktree-storage/build/bootstrap/stage2-compiler-tests/aarch64-apple-darwin/`.

Mappings: `rejection.env`, `verification/summary.env`, and `verification/campaign.UkPNkE/process.env`, respectively. Paths inside receipts describe that historical execution environment. Successful narrow smoke probes do not override the full qualification rejection. Failed-run RSS and elapsed time do not establish the performance gates of the new TargetHIR plan.
