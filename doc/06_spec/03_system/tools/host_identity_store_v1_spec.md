# Actual retained host identity store V1

Status: **AUTHORED_NOT_RUN**. Manual companion to
`test/03_system/tools/host_identity_store_v1_spec.spl`, not generated output.
No tests, builds, native calls, SSH process, key generation or docgen ran.

Prepare disposable real OS fixtures independently. The executable spec never
uses fake file descriptors, synthetic handles, claimed permission booleans,
unsupported-host skips or insecure self-installation. Do not point it at live
SSH identity state. Retain actual owner results for diagnosis when cleanup
fails. Only public known-hosts data enters the fixture environment.

| Fixture setting | Preparation |
|---|---|
| SIMPLE_HOST_IDENTITY_FIXTURE_ROOT | Fresh disposable final root, or an absent final child beneath an existing trusted private parent. Linux ancestry forbids group/other write; final root/journal UID is the actual effective user, mode0700. Windows parent is a real protected private-root fixture. |
| SIMPLE_HOST_IDENTITY_FIXTURE_PUBLIC_LINE | Actual public canonical known_hosts line independently prepared from a genuine public Ed25519 key. No private key or secret is allowed in this environment setting. |
| SIMPLE_HOST_IDENTITY_UNSAFE_ROOT | Separate actual symlink/reparse or unsafe-permission/owner root fixture. It must be refused rather than repaired. |
| SIMPLE_HOST_IDENTITY_UNSAFE_LEAF_ROOT | Protected root/journal with the leaf consisting of 64 lowercase b characters followed by .key installed as a real symlink/reparse or unsafe-mode file. Its target is disposable and independently checked unchanged. |

1. **Use a fresh disposable protected root and public known-hosts line.** Open
   actual storage, retain its owner and copied alias. Read the digest-derived
   .hosts leaf and require actual absence. A missing target must not receive a
   pathname. Repeated test executions require a fresh fixture root; existing
   storage is never deleted to manufacture this precondition. Linux execution
   must use the canonical main thread with genuine retained procfs origin.
   Transport preflight validates the actual current protected root before any
   target publication: Linux succeeds, while Windows returns the dedicated
   identity-store-transport-projection-unavailable capability limitation.
2. **Publish through actual protected staging.** Require Published, file_synced,
   no pending cleanup and exact full byte readback. Linux requires actual
   namespace_synced; Windows requires false because its native journal does
   not flush directories. Request a pathname only after actual protected-file
   read validation. Linux compares its journal/leaf suffix without capturing
   bytes. Windows requires the dedicated projection-unavailable result after
   that positive read; actual file/native failures must keep their distinct
   errors. No GLOBAL??/GLOBALROOT prefix is stripped into an SSH pathname.
3. **Observe the untouched winner.** Attempt different UTF8 at the same leaf;
   require Existing with both sync flags false and complete original readback.
   Reject path traversal and invalid UTF8 without attempting publication.
   Publish a separate .profile record at the same 64-hex stem; require its own
   Published outcome, then Existing for a conflicting UTF8 record and full
   original profile readback. The .hosts bytes must remain unchanged. This is
   role separation, not profile authorization or SDN validation: production
   profile consumers derive their actual stem from canonical strict SDN.
4. **Consume canonical cleanup.** Close before asserting collected results.
   Require no remaining owner; copied reads/path requests fail, and a copied
   close cannot replay native release. Reopen the actual state and compare full
   persisted public bytes; repeated publication is Existing, with no durability
   inferred for this invocation. Compare the complete persisted .profile bytes
   independently after reopening.
5. **Refuse actual unsafe ancestry.** Open the separately prepared unsafe root;
   require a nonempty refusal diagnostic, never Ready. If a native cleanup owner
   was returned, retain and close that actual owner before assertions.
6. **Preserve cleanup truth after unsafe reads.** Read the actual unsafe .key
   fixture, requiring bytes=None, absent=false and cleanup_pending=true. Follow
   with invalid read/publication arguments and require pending cleanup to stay
   true. A path request must fail. Close the canonical resources before asserting.

The following remain **MANUAL_NOT_RUN**, requiring actual isolated native
fixtures or fault hooks rather than fake successful assertions:

- Concurrent publishers/processes: exactly one no-replace winner; a losing
  operation observes a safe Existing target without overwrite, an explicit
  uncertain error, or refusal to acquire the Windows journal owner.
- Metadata/name substitution between checks, stale stage collisions, symlinks,
  reparse points, hardlinks, owner/mode/ACL drift, principal change and Linux
  fork inheritance: explicit refusal and no deletion of substituted objects.
- Genuine Linux fork/PID-namespace collision: on an isolated PID1 parent with
  an actual open store and a retained private stage obligation, create a real
  nested PID namespace whose child is also numerically PID1, inheriting the
  registry. Invoke copied read/publish/path/preflight/close in the child. The
  retained procfs origin proof must refuse before mutex/registry access; parent
  stage/directory descriptors must not be closed or unlinked. Parent operations
  and its actual stage binding must remain intact. Repeat ordinary fork and
  bind-mount/procfs substitution variants. No synthetic PID or boolean proves
  this case, and there is no executed process fixture here.
- Genuine Linux worker-thread call: create an actual worker thread and invoke
  copied owner operations there. Require main-thread refusal before mutex or
  registry access, then prove the canonical main-thread owner still works and
  closes once. The source guard's contract deliberately narrows this adapter.
- Missing final root: independently leave only the final child absent beneath
  a trusted existing parent, then run the positive fixture. Linux must actually
  create root/journal with 0700 before private bytes and sync their parents;
  Windows must use actual protected child_directory and journal creation.
  Existing unsafe parents must refuse, never be repaired or bypassed.
- Partial write, interrupted/failed fsync, successful publication followed by
  failed cleanup, failed Linux close and Windows retained native close: preserve
  exact remaining ownership, never retry a consumed raw fd, never infer absence
  from failure and never delete a published destination to compensate.
- Crash/restart and power loss: verify actual persistence per OS. Windows
  namespace_synced=false is a limitation, not a power-loss guarantee.
- Private OpenSSH-key bytes and pin identities: use the real shared codec and
  genuine generated key fixtures in the consumer's separate integration tests.
  Storage's UTF8 acceptance alone establishes no cryptographic validity.

No private bytes are logged, embedded in SDN, captured in steps, or placed in
the fixture environment. The threat boundary trusts the same OS user and
administrators/root; stronger OS keystore protection remains a separate TODO.
