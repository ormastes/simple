# Loader anonymous executable source ownership

Executable: `test/01_unit/os/kernel/loader/anonymous_executable_image_v1_spec.spl`.
Requirement: REQ-SOSIX-MEMORY-SOURCE-001. Manual scenario record; hosted
interpreter diagnostic evidence, 4 executed / 4 passed / 0 skipped / 0 dropped.

| Scenario | Steps and observable assertions |
|---|---|
| Runtime installation | Admit the audited RV64 identity; exclude ARM64, x86_64, unknown and empty identities. |
| Ownership and immutability | Seal binary input; mutate input/output; retained bytes remain exact. Reject foreign owner/generation and release. Release once, reuse the slot and reject the stale reference. Recover the original charge. |
| Rejected creation | Reject mismatched digest, zero owner, zero generation and empty bytes; charge remains unchanged. |
| Capacity and retirement | Retain 256 independent single-byte images, reject the 257th, release all images and recover the original byte charge. |

This validates storage contracts, not permission to execute or live guest
behavior. Runtime serialization failure keeps a fail-stop quarantine and is
not included in the successful-cleanup claim.
