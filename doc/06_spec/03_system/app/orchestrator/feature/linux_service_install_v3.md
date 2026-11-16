# Fixed signed Linux service installation

Status: AUTHORED_NOT_RUN. The two fixture functions consume genuine original
protected readers, native identity loans, and real signed enrollment requests.
No fixture factory constructs a reader/native owner from DATA. The configured
provisioning driver is NOT_AUTHORED, so these helpers are not claimed as
executed system coverage.

Since signing step 5 the installer reaches the protected parent writer only
through `operation_health_linux_install_v1`, which requires the sealed
`LinuxServiceVerifiedEnrollmentV1` from the single io verifier
(`std.nogc_sync_mut.io.host_linux_service_records_v4`). The owner opens the
parent with `create_final=false`, re-verifies the proof against the policy read
through its own writer before and after every publication, and drains its own
descriptors before returning. A carrier is returned only for a partial close.

`host_linux_service_install_duplicate_fixture_v3` requires an actually absent
claim, performs installation, drains any partial-close carrier, and then
installs the same request again, which must be observed as the exact duplicate
with the protected claim bytes (original nonce and timestamp) unchanged. The
earlier competing-writer and stale-carrier assertions no longer apply: the
writer is never held across calls, and a fully closed install returns no
carrier to go stale.

`host_linux_service_install_signature_fixture_v3` corrupts a real approval
signature and checks the precise signature refusal before any writer opens,
then reads the original parent again to prove no claim appeared.

Neither fixture closes the borrowed parent/native inputs or interprets a failed
assertion as permission for further effects. Faults during native publication,
sync, or close still require an external fault/provisioning driver; they have
not been simulated by hardcoded booleans or claimed covered.

Accepted residual risk (signing step 5 review r1, P2): native identity and the
original parent reader both import owner_health, so the owner cannot re-check
them per publication. The installer checks them before and after the whole
owner entry; the writer's own currentness and the installed-policy signature
re-verification still run before and after every publication. A caller that
skips the installer and calls the public verifier and owner entry directly can
omit the native machine check; what it can publish is still only a byte-exact,
installed-key-signed association, and startup re-verifies the records
(including approval expiry) before trusting them. Since step 5 the fixed-child
residue phase names the child file only, as before.
