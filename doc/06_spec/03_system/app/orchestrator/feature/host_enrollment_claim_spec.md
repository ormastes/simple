# Finite signed host filesystem claim

Status: **AWAITING_VERIFICATION — NOT_RUN**. Authored specification manual, not generated execution evidence.

Implementation: `src/lib/nogc_sync_mut/orchestration/host_enrollment_claim_v1.spl`.
Executable: `test/03_system/app/orchestrator/feature/host_enrollment_claim_spec.spl`.
Fixture: `test/fixtures/orchestration/host_enrollment_claim_fixture_v1.spl`.
Requirements: `doc/02_requirements/feature/host_enrollment.md`.
Architecture: `doc/04_architecture/host_enrollment.md`.

| Requirement | Authored case | Assertions |
| --- | --- | --- |
| HOST-ENROLLMENT-04 | Retains real signed claim and exact private root objects before returning facts | Real secure parent, canonical public policy with fixture Ed25519 keys, canonical HostConfig, real signed credential; returned facts match disk, exact input/configuration and policy digests, canonical credential/binding, manifest/claim nonce and binding agree, root mode 0700 and file modes 0600, no journal created |
| HOST-ENROLLMENT-03 | Same positive case continues with duplicate and signed alias attempts | Original native machine ID determines a fixed slot; repeated credential and a core-authorized worker_2 physicalHostId alias refuse. The alias installs matching worker_2 key scopes, updates grant/operation host IDs and configuration/policy digests, and recomputes both real signatures while retaining the same native machine ID. Original enrolled claim remains byte-identical; original root configuration and policy bytes remain unchanged |
| HOST-ENROLLMENT-04 | Rejects signatures and expired clocks before parent lock creation | Corrupt actual approval signature and expired positive clock refuse; neither claim nor lock appears |
| HOST-ENROLLMENT-04 | Exact commit-boundary approval expiry | Immutable captured private clock-file path advances 100 -> 150 -> 190; first two authorization instants remain valid, final exact approval expiry refuses before exclusive claim/root creation |
| HOST-ENROLLMENT-03 | Retains preexisting pending/unknown evidence | Precreated canonical creating claim and separate unknown interrupted claim both refuse adoption and retain identical bytes |
| HOST-ENROLLMENT-04 | Refuses signed configuration outside supported local scope | Signed absolute journal escape, wrong controller, exclusive device budget, and exact configuration-digest mismatch refuse before claim or lock mutation |

Production `host_enrollment_claim_v1` obtains Unix milliseconds from the existing SOSIX Unix-microsecond clock. The explicit clock callback is a local test seam, not an authorization CLI option. Full authorization runs before the first filesystem mutation and repeats after taking the bounded parent lock, with reloaded installed policy and refreshed nonregressing positive clock. Immediately before exclusive claim publication, a third positive nonregressing clock sample rechecks approval expiry and existing grant scope/policy/expiry without repeating Ed25519 verification. Exactly one unlock follows every successfully acquired lock, including handle zero.

Fixed parent artifacts are `.host-enrollment.lock` and `host-claim-<sha256(native_machine_id)>.sdn`. Existing slots always refuse; they are never overwritten, deleted, adopted, or interpreted as spare capacity. The creating claim initially has an empty root, then records the new private child as soon as it exists. Root objects are `host-config.sdn`, `authority-policy.sdn`, `enrollment-credential.sdn`, `enrollment-binding.sdn`, and `host-root.sdn`. Exact readback precedes the final enrolled claim publication. Before either pending-to-root or final replacement, the original pending bytes/nonce must still match.

All errors after exclusive claim publication retain the claim and any created child/files. A crash or publication failure between root creation and its path update can leave an orphan private child while the original creating claim remains. Manual reconciliation is required; no automatic scan, deletion, root replacement, rollback, journal opening, capacity release or workload launch is implemented. Unlock failure also returns an error while retaining published artifacts.

Trusted caller prerequisites: obtain actual native machine/boot/provider observations and an installed administrator-owned parent tree. The synthetic IDs in this fixture are explicit test inputs. Policy/digest/mode validation alone does not authenticate an arbitrary parent, and this path does not claim race-free descriptor-relative IO, live native observation, provider execution or boot continuity.

Unexecuted inventory: all five SSpec cases, compilation, actual production clock/entropy/lock behavior, private publication and seeded signature verification remain NOT_RUN in this change. Disk-full/readback/entropy failures, claim-byte interference, policy replacement during lock acquisition, process crashes, and unlock failures have not been induced or tested. No fake failure hooks were added. Existing source checks on each error path are not runtime evidence.

No build/test slot was allocated. The shared global limit is five CPUs; local tooling after that instruction used `taskset -c 0-4`. No compiler, SSpec, provider or deployment command was executed.
