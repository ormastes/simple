# Native Windows deployment owner

Source: `test/02_integration/lib/host_windows_deployment_v2_spec.spl`.
All five scenarios are **NOT_RUN**. Real Windows private ACLs, actual common
Docker observation and real Ed25519 verification are required; missing platform
or fixtures fail rather than skip or emulate success.

Provision an administrator-owned native-private directory in
`SIMPLE_WINDOWS_DEPLOYMENT_PRIVATE_PARENT`. Normal fixtures read its exact
`engine-policy.sdn` and `broker-policy.sdn`; the former must describe an actual
supported healthy Windows Docker installation. Fixtures create fresh private
machine-parent children, install public deterministic test keys, and sign exact
bindings with native-clock-bounded grants. These are test-only trust roots.

1. Run the actual producer, close its retained nine-file/two-root owner and
   reopen the same fixed machine claim/direct child. Require physical config
   intent and completed residue; do not claim broker enforcement or service
   readiness.
2. Corrupt a real SDK signature while pinning a deliberately poisoned observer
   policy. Require the signature error before observation-policy parsing. The
   poison fixture never observes an engine during setup. Exclusive creation at
   the fixed claim name then provides positive absence evidence for that name;
   no ambiguous existence predicate is accepted as proof.
3. Request enrollment again after completion. Require retained recovery state,
   then explicitly reopen and compare the original claim digest and root child.
   The duplicate cannot overwrite the fixed claim or replace its deployment.
4. Seed an actual private partial claim with no completed child. Require reopen
   refusal and positive exclusive child creation afterward, proving reopen did
   not allocate/adopt a replacement. This is a seeded interrupted prefix, not
   evidence from an executed crash/fault campaign.
5. Create another actual private tree whose records and metadata describe its
   new parent, but reuse the original signed credential. Require the exact SDK
   signed-binding mismatch; private metadata alone cannot mint the role.

Fixture-created private parents, partial claims, absence probes and stage
artifacts remain on disk for separate administrative cleanup. Closing retained
handles is not deletion, claim release, production cleanup proof or permission
to run another enrollment. Failed-close injection, post-reopen elapsed grant
expiry, native clock-regression injection and Windows link/runtime performance
are not qualified by these authored cases.
