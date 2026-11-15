# Machine container policy V1 pure codec

Status: **AUTHORED_NOT_RUN**. Authored manual mirrored from
`test/01_unit/lib/common/contracts/container/machine_policy_v1_spec.spl`.
No tests, compiler, native fixture, installed-policy reader or doc generator ran.

This codec validates typed policy metadata, encodes canonical SDN with one
final LF, hashes those exact bytes and strictly decodes the same schema.
`kind: machine-container-policy` and wire `version: 2` are explicit. The V1
source API names remain stable. Legacy wire V1 is rejected; migration requires
an administrator to review and install explicit V2 bytes. The codec performs
no automatic upgrade, policy replacement, writer reset or charge release.
CamelCase keys
describe machine identities, mode, resource ceilings, ordered provider policies
and local principals. It proves no native machine identity, installed-file
provenance, authenticated principal or capacity authority.

| Requirement | Authored actual production assertions |
|---|---|
| REQ-MACHINE-CONTAINER-POLICY-001: exact canonical integrity | Roundtrip every field and exact nested opaque policy text including multiline escapes; require canonical byte equality and SHA-256 of those exact bytes; changing nested text or resources changes the digest. |
| REQ-MACHINE-CONTAINER-POLICY-002: authority separation | Standalone requires empty managed authority and empty authority-policy digest, and at least one explicit local principal. Managed requires a valid nonempty managed authority, a lowercase SHA-256 authority-policy digest and zero local principals. Reject inconsistent modes and duplicates. |
| REQ-MACHINE-CONTAINER-POLICY-003: bounded strict schema | Validate identifiers, named backends, digests, exact principal strings, opaque text, resource units and count/size ceilings. Reject unknown/missing/duplicated/mistyped fields, wrong kind/version, invalid semantics and noncanonical bytes. |

1. Encode the standalone fixture with opaque multiline provider text, spaces,
   quotes, backslashes and a Unicode native identity. Decode every field and
   compare provider text and canonical bytes exactly. Compare its digest with
   SHA-256 of the actual encoded bytes.
2. Change the final newline in opaque provider text and independently change
   CPU units. Each digest must change.
3. Roundtrip managed mode with an explicit managed authority and no local
   principals. Refuse managed local grants, absent/invalid managed authority,
   standalone managed authority, standalone without local principals and
   unknown modes.
4. Managed authority text is the exact expected authenticated controller issuer,
   not a host-enrollment journal identifier. Roundtrip `controller:team.prod`
   and a 256-byte issuer; refuse empty, control-bearing or oversized issuers.
   The actual issuer must later establish
   `HostConfig.controller_ref == verified credential.signed.issuer_id`.
   `managedAuthorityPolicyDigest` pins the exact actual retained enrollment
   authority-policy bytes independently from that issuer name. Replacing the
   signing-key policy under the same issuer changes the encoded machine policy
   digest; malformed, missing and uppercase pins are refused. Standalone must
   carry an empty pin. V2 with a missing pin and legacy V1 both refuse.
   These are pure schema/integrity assertions, not an executed cryptographic
   wrong-key admission test. Actual native proof/claim tests remain NOT_RUN.
   The codec preserves expected metadata and proves no authentication.
   Reuse the existing builder identifier grammar: ASCII `[A-Za-z0-9_-]`,
   length 1–128, for authority and physical host only. This is
   deliberately stricter than the general 256-byte identity ceiling. Admit
   256-byte arbitrary native identity text; reject empty, control-bearing or
   oversized UTF-8 identities, including multibyte overflow.
5. Preserve exact local principal spelling. Case-distinct strings remain
   distinct metadata pending native authentication. Refuse exact duplicates,
   empty strings, C0/C1 control characters and strings beyond 256 UTF-8 bytes.
6. Admit only `linux-podman` and `windows-docker-process`, lowercase hexadecimal
   64-byte identity digests, and nonempty opaque provider text without NUL.
   Preserve ordinary newlines and equals. Refuse invalid names/digests and
   empty, NUL-bearing or individually oversized provider text.
7. Allow different identity digests under one backend and the same digest under
   different backends. Reject an identical backend/digest pair even when its
   policy text differs.
8. Admit CPU 1–64000 millis and memory 1–1125899906842624 bytes inclusively;
   refuse values immediately outside either interval.
9. Admit 1–16 provider entries and up to 128 exact standalone principals;
   reject no providers, a seventeenth provider and a 129th principal. Managed
   mode's zero-principal requirement remains stricter.
10. Fill actual canonical output to exactly 1048576 bytes, decode it, then
    reject one extra byte and an escaped newline expansion. Reject empty or
    oversized decoder input. Exact escaped-size preflight uses the shared
    serializer's size helper before serializing large opaque provider text.
11. Mutate real encoder output to exercise schema/type/version/kind checking,
    nested provider validation, duplicate principals, semantic mode separation,
    comments, trailing data, missing final LF and malformed syntax.

`policy_bytes` is UTF-8 text under the frozen interface, not arbitrary binary.
It remains opaque and is bounded to one MiB per provider, with the whole
canonical envelope also bounded to one MiB. Native providers must independently
decode their exact policy schema and verify actual backend identity. The pure
fixtures deliberately make no claim that opaque sample text is a valid native
engine policy. This codec does not authorize a machine-policy reader or resolve
the independently reviewed native root-provenance boundary.

All assertions are authored, unexecuted coverage intent. Runtime, Unicode,
performance, native provenance and platform qualification remain unverified.
