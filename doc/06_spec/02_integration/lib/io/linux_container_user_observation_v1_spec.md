# Read-only native container user observation

Source: `test/02_integration/lib/io/linux_container_user_observation_v1_spec.spl`.
Status: two authored modern SSpec scenarios **NOT_RUN**; this is a manually
reviewed mirror, not generated docgen. Actual native C evidence is distinct.

| Step | Oracle | Status |
|---|---|---|
| Verify the compiled fixture identity before running actual native observations | Exact pre/post binary SHA256, bounded subprocess exit/stderr/output; the actual C fixture asserts native facts, ownership, child exit17 and FD counts | SSpec NOT_RUN; underlying C fixture ran once with61 checks PASS |
| Use the production owner facade and retain structured failure ownership | Invalid PID returns the production typed error with no published native token; owner-free failure close succeeds | AUTHORED_NOT_RUN |

The actual native fixture is
`src/runtime/test/linux_container_user_observation_v1_selfcheck.c`; its evidence
is `linux_container_user_observation_v1_native/evidence.sdn`. It observes a real
gated child, not fabricated mapping data. Missing executable, wrong hash, missing
kernel support, timeout, exit77, unexpected stderr or output all fail the SSpec.

The C pass does not prove native Simple ABI, real Podman identity, distinct
user-namespace mapping, race-free immutable executable staging or Windows ACL
behavior. Those remain required pending gates. Native observation has no
signal/reap/adoption, chmod or execution authority; tokens stay owned until an
explicit successful close. No decoder may reconstruct a token from wire data.
