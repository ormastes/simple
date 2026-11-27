# Containment candidate and V4 request boundary

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/containment_profile_v1_spec.spl`.

Six authored scenarios, NOT_RUN. This is profile data plus fail-closed refusal evidence to execute, not installed containment or runtime qualification.

| Scenario | Assertion |
|---|---|
| Exact candidate | Canonical profile roundtrip; only exact CLI policy and selected profile digests match. A changed runtime digest cannot substitute. |
| Strict profile | Unknown/duplicate/wrong-version/noncanonical fields, relative/noncanonical/control-containing paths, unsupported manager and invalid SHA refuse. |
| Backward compatibility | Empty selector preserves exact literal V1/V2/V3 retained bytes and frozen semantic hashes. |
| V4 boundary | Explicit terminal/user fields roundtrip with absent or selected numeric user; downgrade, missing/unknown/empty/tampered selector refuse. |
| Actual legacy refusal | Real provider prepare/create and public create builder reject the selected candidate before native command construction, state reservation or executor consumption. |
| Actual common entrypoint | Digest-bound common create rejects the selected candidate, returns its projectable scoped owner and leaves executor, state and clock consumption unchanged. |

Every raw-byte mutation fixture asserts it differs from its source before testing rejection, preventing a missing replacement needle from passing vacuously.

Golden provenance: V1 `de002d...` and V2 `28394...` reuse the previously authored historical fixture expectations. V3 `579660...` was independently calculated once with Python hashlib from the unchanged pre-V4 canonical digest algorithm and exact `linux_container_leaf_fixture_v2` values plus UID1000/GID1001/keep-id. Literal SDN bytes were transcribed from existing sorted-key encoding rules. These are source-derived expected values, not output captured from an admitted Simple runtime.

| Pending matrix | Status |
|---|---|
| Profile/schema/semantic hash and retained codec | Implemented source; authored scenarios NOT_RUN. |
| Old provider/factory/create path refusal | Implemented refusal gates; authored actual-branch scenarios NOT_RUN. |
| Installed containment constructor and common API route | Not implemented by this checkpoint. |
| Actual runtime executable observation and profile identity | Not implemented or qualified; candidate digest is trusted-local-admin mutable-path observation intent, never sealed execution proof. |
| Fixed flags, bounded exact inspect correlation, native capture/teardown | Separate required implementation and runtime acceptance. |

No build, check, native test, positive configured factory, capture or teardown qualification is claimed. The request carries only a digest, never a runtime executable path. No generic wrapper, native registry or permission bypass is introduced.
