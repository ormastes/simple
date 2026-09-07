<!-- codex-design -->
# Agent Tasks: macOS Bootstrap Reverse-Reference Harmonization

Shared contract owner freezes `ReverseReferenceKeyV1` and the checker/helper
names in the matching SPipe plan before any lane starts.

| Lane | Scope | Sidecar |
|---|---|---|
| Contract | framing, projection receipts, fail-closed reasons | N/A until scheduled |
| Apple Silicon | native Phase2/3 and thin-slice evidence | N/A until scheduled |
| Intel macOS | native Phase2/3 and thin-slice evidence | N/A until scheduled |
| Reuse | compatibility manifest, corruption and concurrency fixtures | N/A until scheduled |
| Universal | composition, native admission, promotion without rebuild | N/A until scheduled |

**Merge owner:** compiler bootstrap/cache integration owner.
**Final reviewer:** independent best-available normal/highest-capability reviewer
who implemented no lane and reviews both architectures plus mutation-red cases.

## Cross-Lane Handoff

- **Stage 3 recovery guard owner:** implements only the non-mutating authority
  preflight and its mutation-red shell contract. The guard may emit
  `pass`, `pending`, or `refused`; it never starts a compiler, takes the output
  lock, mints authority, inspects a live candidate, or deploys.
- **Stage 3 root-cause owner:** supplies retained terminal failure evidence and
  source fixes only. Failed-lane artifacts and cache objects are evidence, not
  candidate or parent authority, and must not be copied into recovery.
- **Stage 3 retry-readiness owner:** may consume a guard receipt only after
  independently re-deriving the same tuple. A retry remains forbidden until
  the guard passes; the known stale main-worktree tuple is an expected
  `refused`, not a repair target.

- **M3 owner:** bind `PhaseCompatibilityExpectationV1` and
  `phase_compatibility_admit_v1` to the exact manifest receipt digest,
  `m2_owner_generation`, and `m2_root_generation`; the current driver
  expectation at `driver_aot_native_output.spl` supplies only key, compiler,
  provider, target, and schema identities. M0/M1 deliberately does not alter
  that reuse boundary.
