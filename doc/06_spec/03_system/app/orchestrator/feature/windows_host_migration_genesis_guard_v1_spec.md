# Fresh managed Host admission requires a real migration fence

Status: **AUTHORED_NOT_RUN**. The matching executable spec is
`test/03_system/app/orchestrator/feature/windows_host_migration_genesis_guard_v1_spec.spl`.
No compiler, runtime, native, SPipe or docgen campaign was run.

REQ-WINDOWS-HOST-MIGRATION-GUARD-001: genuine signed fresh Host enrollment must
return `machine-managed-claim-migration-fence-unavailable` when the actual
machine WAL is empty and no genuine migration-fence producer exists.

The scenario reads administrator-prepared native-private signed inputs, opens
the actual installed machine authority, observes an empty WAL head, and closes
that exact writer. It then invokes the production Host enrollment factory.
After the refusal and retained cleanup, it reopens the actual machine authority
and requires the WAL head to remain empty. Native open outputs and failed
closes are retained before assertions; Host and machine cleanup owners remain
in separate explicit fixture slots. There is no manually seeded charge,
caller readiness boolean, fabricated fence, label adoption or skipped oracle.

The disposable real Windows installation must have a managed machine policy
with exact issuer, authority-policy digest, native machine/provider and engine
policy pins matching the genuinely current signed fixture. Set
`SIMPLE_WINDOWS_MANAGED_HOST_FIXTURE` to its actual native-private deployment
parent. Fixed source children are `authority-policy.sdn`, `host-config.sdn`,
`engine-policy.sdn`, `broker-policy.sdn`, `enrollment-binding.sdn` and
`enrollment-credential.sdn`; the signed binding must name that same parent.
The spec does not install or alter these inputs. A nonempty pre-existing
machine WAL fails the fixture precondition; it is never cleared or rewritten.
Failed initial writer cleanup/read or a nonempty head explicitly stops before
enrollment. An unexpected Ready/recovery outcome or pending deployment cleanup
explicitly stops before the second machine open. The test does not rely on
nonfatal expectation behavior to guard later effects.

This tests the refusal contract when executed. It does not measure zero engine
invocations, prove legacy absence, supply a whole-provider writer fence, or
qualify positive migration or existing-charged recovery. Existing installed
provider probes can execute during machine-owner opening; no supplied-policy
observer or Host publication is authorized by the refused claim.
