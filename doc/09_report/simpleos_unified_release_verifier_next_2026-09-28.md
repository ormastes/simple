# Unified SimpleOS release verifier: next evidence boundary

Reviewed `origin/main` at `fdc600a4d3f56b068715ffe650e0841db17700ea` and PR #1983
on 2026-09-28. Source inspection only; no guest, test, release, or performance
qualification is claimed.

## Finding

The six `require_unified_release_verifier_v1` calls in
`test/03_system/os/feature/simple_platform_unification_spec.spl` must remain
fail-closed. There is no existing authenticated production release transaction
to consume in place of that helper. Adding another value validator would not
produce the missing evidence.

The selected authority is
`doc/02_requirements/feature/simple_platform_unification.md`: REQ-010 requires
the ordinary compiler inside SimpleOS; REQ-017 requires retained guest bootstrap
evidence; REQ-018 requires immutable-candidate qualification and reboot
persistence; REQ-019 prohibits synthetic/source evidence from closing live rows.

The new cross-reference from this inspection is that the production `src/os`
references to `SimpleOsReleaseEvidenceManifestV1` are confined to
`src/os/services/evidence/release_evidence_ledger_owner_v1.spl`. The ledger
consumes a manifest; it does not acquire candidate bytes, launch a machine,
authenticate guest workflow receipts, or observe reboot persistence. Its
contract explicitly requires an embedding service to persist successful state.

PR #1983 adds `src/os/kernel/loader/simple_guest_version_owner_v1.spl`: a
loader-owned, single-consumption scheduler observation for exactly `--version`.
Its stated scope excludes candidate identity, cold boot, same-session export,
guest compilation/execution, and reboot persistence. Consequently merging that
PR alone cannot close even the unified `guest-version` release row.

## Missing producers and sequencing

1. **Candidate and derived-state owner (independent of #1983).** Acquire and
   retain the actual immutable candidate identity, create an isolated writable
   derivative, and bind the firmware and sealed launch plan. Existing image
   composition readback is useful input, but does not establish an immutable
   release transaction or prove that a later guest used those bytes. This is
   the first implementation lane; design its retained authority and lifecycle
   before adding a public API. A caller-supplied digest or immutable boolean
   cannot substitute for the owner.
2. **Cold-boot session producer.** Launch that derivative through the release
   firmware path and retain authoritative session identity, boot observation,
   timestamps, logs, and NVFS/SOSIX evidence bound to the same transaction.
3. **Guest workflow export.** Integrate #1983's retained version receipt with
   that session; add authenticated ordinary-compiler run/build/execute owners.
   Bind compiler, source, produced artifact, output/status, and receipt identity
   rather than parsing pass-looking serial markers. The formatters in
   `src/os/sosix/qemu_fs_toolchain_evidence_v1.spl` do not provide this authority.
4. **Persistence producer.** Observe marker write and sync, cold reboot the same
   derivative, and observe marker read under a distinct authenticated boot
   session. Bind the marker and state identities across those observations.
5. **Release consumer.** Authenticate the preceding owner receipts, confirm the
   original candidate remains unchanged, assemble the manifest, and consume it
   through the existing ledger with durable recovery. Replace the test helper
   only with this production consumer and retain per-stage assertions.

The execution order already required by
`doc/03_plan/sys_test/simple_platform_unification.md` still applies: admit the
pure-Simple native runner, execute source contracts, stage real products,
execute image admission, and then qualify live transactions. The report adds
no alternative gate and does not mark any requirement complete.

## Handoff

No production code or tests changed. No independent existing receipt source was
found that can safely turn a live release row green. The next useful scoped
task is the candidate/derived-state retained-owner design and implementation,
followed by cold-boot integration; #1983 can progress separately. Full release
qualification remains RED until all producers and their native/live evidence
exist. No commit or push was performed.
