# Closed primary connection metadata codec V2

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests or builds were executed.
The specs call the actual public encoder and decoder with metadata fixtures.
They do not construct opaque native absence proof or connection capabilities.

Source: `src/lib/common/contracts/container/primary_connection_evidence_v2.spl`.
Spec: `test/01_unit/lib/nogc_async_mut/container/primary_connection_evidence_v2_spec.spl`.

| Authored case | Intended assertion |
|---|---|
| Exact roundtrip | Request/identity digests and native slot/generation survive canonical encoding with the exact eleven provider-format fields |
| Inclusive boundaries | Slot 0 through 2147483647 and positive i64 generation boundaries preserve their values |
| Digest validation | Empty, short, long, uppercase and nonhex request/identity digests refuse at both encode and decode |
| Numeric bounds | Negative or above-i32 slots and nonpositive generations refuse without narrowing |
| Field set | Every missing field and unknown extension refuses |
| Strict types | Quoted integers, numeric booleans, numeric text fields, floats, null and boolean slot values refuse |
| Metadata domain | Wrong version, kind, resource domain or provider refuses |
| Fixed closure flags | Closed must be true and both pending flags false |
| Canonical source | Leading space, extra/missing newline, CRLF, comments and duplicate keys refuse |
| Source boundary | Empty and above-4096-byte input, malformed syntax and nondictionary roots refuse |

The wire format matches the provider's existing canonical SDN record plus one
newline: version 2, kind `container-primary-connection-closed`, resource domain
`engine-attach-connection`, and provider `windows-docker-process`.

Successful decoding establishes only schema-valid canonical metadata. It never
proves native absence, grants cleanup or IO authority, authenticates a peer,
settles Host resources, or proves workload completion. The actual provider must
check native absence against its retained owner before encoding this record;
no decoder can recreate that native proof.
