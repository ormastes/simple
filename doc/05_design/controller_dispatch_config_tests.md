# Dispatch configuration installation test scope

Seven executable scenarios and matching native probe use real secure_temp_dir,
exclusive marker publication, file modes, no-follow reads, symlinks, fsync and
private-tree cleanup. Canonical synthetic PUBLIC policy fixtures adapt the
existing local_authority_policy_spec pattern. They exercise installation and
loading only, not cryptographic verification. No fake fsync/read success exists.

Owner source reviewed SHA-256: `72c97d076f481e439e4a522ad684180f9e23c60059ca1843ee7cd83cd89b5213`.
No owner source change was made by this test task. Within the documented trusted
administrator/private-root/ancestor model, no P0/P1 defect was found.

Remaining trust limitations must stay explicit: host_root is syntax-only here;
the actual consumer must validate the host owner marker/authority/configuration.
Path/mode checks cannot prove UID ownership or make mutable ancestor traversal
race-proof. Decoded public keys and positive synthetic expiry do not establish
current signature validity. The fixture does not test production wall-clock
acceptance or use a policy snapshot as an authorization oracle.

Partial file behavior is deliberately bounded: a complete policy publication with
missing config can be completed on identical retry. A failed later config write
can leave policy retained; there is no rollback promise. No claim is made that
truncated immutable content is repaired or every crash/power-loss window passes.
Conflicting canonical config/policy tests require original committed bytes remain
unchanged. Outside symlink targets are read independently to verify no mutation.

Artifacts: controller_dispatch_config_spec.spl under system orchestrator feature;
controller_dispatch_config_native_probe.spl under test fixtures; matching authored
manual under doc/06_spec. All runtime/admitted/manual-generation/coverage results
are NOT_RUN. This test-only task performs no build or owner code mutation.

The host-agreed providerIdentityDigest extension is being added by the source
owner. Fixtures construct provider_identity_digest as a valid64-character pin,
assert its exact retention and reject malformed digest input. This pin is
administrator-provisioned data, not automatically trusted host-status discovery.
It is distinct from OperationEnvelopeV2.environment_digest; the host-authority
reference maps to intent.fence.authority_id rather than physical operation.host_id.
The reviewed source hash above identifies the pre-extension source, not a claim
that the evolving owner file is frozen or was edited by this test task.
