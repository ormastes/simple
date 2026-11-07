# Static service enrollment V2

Authored pure source design. NOT_RUN; no native readiness, ACL, boot-counter or durability qualification.

`HostServiceEnrollmentBindingV2` binds physical host alias/service scope, observed namespaced machine identity, provider identity, installed parent, exact raw config/public-authority-policy/engine-policy/broker-policy SHA256 pins, policy revision and physical/broker CPU+memory partitions. `engine_policy_digest` is serialized as required `enginePolicyDigest`; it hashes **exact installed raw bytes**, not a normalized engine policy. Changing it changes the canonical signed payload digest. Missing, noncanonical or malformed pins reject; there is no fallback to provider identity digest.

This static binding deliberately carries no native boot or live service epoch. The actual Container service factory must mint a fresh epoch on each startup, compare actual observed native machine/provider facts, and keep admission quarantined until real same-journal reconciliation. Namespaced observed IDs, including the Windows MachineGuid colon namespace, remain data; the codec never fabricates an observation or proves boot continuity.

The authorizer derives `host_enroll_v1` over this exact canonical payload, compares host/memory/environment/policy/context and delegates to the existing dual-role signature verifier. No second crypto implementation is introduced. Actual installed root authenticity and byte loading remain separate trusted native-capability prerequisites; a valid digest or static broker file is not filesystem authority, enforcement, or readiness.

Validate positive physical resources and strictly smaller positive reserved broker partition **before subtraction**. Allocatable CPU/memory is physical minus the signed broker partition once, with no rounding, mutation or per-helper duplicate debit. This pure calculation does not establish broker/job capability enforcement. Native consumers must compare the actual installed broker policy pin and obtain their own broker capability.

Executable source specifications contain seven cases: real signature acceptance and canonical roundtrip; signed pin/partition mutations; arithmetic edge/overflow-shaped inputs; signature corruption/exact expiry/context drift; noncanonical/oversized/unknown/backend data; canonical parent spellings without ownership inference; required raw engine pin and malformed/missing field. All remain NOT_RUN. The raw claim refactor and Windows private-root factory are intentionally outside this pure checkpoint.
