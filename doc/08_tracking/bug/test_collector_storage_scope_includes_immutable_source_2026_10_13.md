# Test collector scans immutable source and prior evidence

Status: observed bootstrap orchestration performance defect; narrower layout is a private proposal. Bug DB reconciliation pending (qualified DB provider unavailable).

The sealed NEXT17 launcher uses output parent `W/grouped-next17` and storage root `W`, where W is `build/native_probe/phase1-current-whole-20261012-sol`. W also contains the immutable source-v2 and prior test evidence. The actual pinned storage observer traversed180,913 entries/2,591,863,343 bytes before the run and181,239 entries/2,597,063,674 bytes afterward, for only5,200,331 bytes of new artifacts.

The worker completed17 original files in122.1647248 seconds, with176 actual named PASS observations matched to the canonical reader. Collector-inclusive time was199.8704005 seconds. The77.7056757-second difference includes initial/post storage scans, launch and sealing; it is not an isolated storage benchmark or native compiler measurement. All row and outer Jobs closed0. Strong consumed-entry source qualification remains HOLD and no native product is qualified.

Evidence: `build/native_probe/phase1-current-whole-20261012-sol/grouped-next17/FINAL_SEAL.json` SHA256 `6e067002be9e29f73b85a6bc3be22ce5a0aa3697a872b588c98e01c2812b8773`; outer receipt `46c2f270e7f368f6f20be8fb96db54b61d64ba298b8deb34fd7d2687d8b73134`. The prior grouped64 run also included the full W storage scope; its successful originals must not be replayed for this correction.

The existing collector requires storage==output_parent.parent (or its specifically named artifacts sibling). Simply changing storage to Q while leaving output_parent=Q is invalid. The proposed future layout is output_parent=Q/outer-attempt, storage=Q, with all row data, temporary files, request/results and controller evidence under Q. Immutable source/tool reads remain separately pinned. This narrows accounting to actual owned writes without relaxing containment or growth rejection.

Private packet: `build/native_probe/test-collector-scope-20261013-sol/`. Proposed acceptance uses the actual pinned collector for a real owned payload, an output/storage mismatch rejected before child launch, and an actual payload exceeding the growth limit. This is not an operating-system write sandbox, and the check must not claim interception of arbitrary writes outside Q. Source-backed fixture/owner write analysis remains required for each future batch. The sealed NEXT17 runner and source were not changed or rerun.
