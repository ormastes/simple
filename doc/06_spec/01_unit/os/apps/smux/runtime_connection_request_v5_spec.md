# Generic runtime connection envelope V5

Status: **AUTHORED SOURCE-ONLY NOT_RUN**. No tests or builds were executed.

Source: `src/os/apps/smux/runtime_connection_request_v5.spl`.
Spec: `test/01_unit/os/apps/smux/runtime_connection_request_v5_spec.spl`.

The codec accepts exactly five canonical SDN fields: integer `version: 5`, kind
`smux-runtime-connection-request`, and text `action`, `bindingUid`, `payload`.
Canonical source has no trailing newline. The wire cap is 2097152 UTF8 bytes;
the strict unpadded Base64URL token cap is 2796203 bytes.

| Authored case | Intended assertion |
|---|---|
| Original action roundtrips | The frozen fourteen actions, including host-progress and host-cancel, retain their original bytes/token/digest cases unchanged |
| UTF8 payload | NonASCII text, quotes, newlines and backslashes roundtrip without payload normalization |
| Exact schema | Five fields and fixed domain/version; action, UID and payload changes alter the digest |
| Field set | Unknown and individually missing keys produce exact schema errors |
| Types and domain | Field coercion, wrong version and wrong kind produce distinct exact errors |
| Canonical source | Leading space, trailing newline and duplicate keys refuse |
| Action allowlist | Unknown, legacy and differently cased verbs refuse |
| Original binding identity | Host, host-progress and host-cancel require empty UID; the other original actions require a valid builder identifier |
| Original payload rules | Original eight payload-bearing actions require data; host-progress/host-cancel/progress/cancel/release/input-observe require empty payload |
| NUL exclusion | Action, UID, payload and serialized source reject embedded zero bytes |
| Inclusive size caps | An exact 2097152-byte canonical envelope and 2796203-byte token roundtrip; one extra wire byte refuses |
| UTF8 and escaping | Multibyte payloads and escaped newlines use encoded byte size, including envelope overhead |
| Strict tokens | Padding, foreign alphabet, invalid length, unused-bit aliases and token-bound violations refuse |
| Wire boundary | Empty, oversized, malformed and nonobject source produce exact errors |

Size validation uses the existing canonical text-size helper and a small
empty-payload envelope to account for quoting and escaping before allocating
large output. Token decoding re-encodes the decoded text to reject alternative
Base64URL spellings, then enforces the same strict envelope boundary.

This is metadata only. It neither authenticates a client nor issues grants,
constructs retained native owners, or performs a server action. The authenticated
dispatcher must apply actual issuer, enrollment, target and native checks.
`host-progress` only observes the server-retained pending/completed host execution
result; its empty UID and payload convey no effect or replay authority.
`host-cancel` only cancels that retained continuation; its empty UID and payload
cannot request another execution or create a grant.

## Additive protocol3 delta

The original fourteen-action snapshot is preserved by these SHA256 identities:

- Source: `6147146ac361db35b8615f1d0afabfbd4ccbe2d5d201f0fc32d9cc123f9e278a`.
- Spec: `eed21c65f43c8ea785393020c7a4c65e1ebdcb99ed83af6b30ab75b7cc8b2471`.
- Manual: `d3ab0d2e485a55beedf2e4780507e03507deaa68ebebd7ae0a18da0913c1e8c5`.

This delta adds exactly seven actions, for twenty-one total. Version, kind,
five-field schema, canonical encoding, NUL rejection and both size limits are
unchanged. The original fourteen-action fixture and test bodies are unchanged;
seven new authored cases exercise the additive classification and boundaries.
Every case remains **SOURCE-ONLY NOT_RUN**.

| Added action | bindingUid | payload |
|---|---|---|
| capabilities | Empty | Empty |
| geometry-resolve | Valid builder identifier | Required |
| geometry-issue | Valid builder identifier | Required |
| geometry-resize | Valid builder identifier | Required |
| geometry-observe | Valid builder identifier | Empty |
| geometry-revoke | Valid builder identifier | Required |
| geometry-cancel | Valid builder identifier | Empty |

New cases call real validate/encode/decode/token APIs for all seven roundtrips;
reject scoped/payload-bearing capabilities; reject malformed geometry UIDs;
enforce four required and two forbidden geometry payloads; reject unnamed
aliases; repeat schema/version/canonical/token/NUL refusals on every addition;
and preserve exact wire/token caps on geometry-resize. Negative encoded inputs
are canonical metadata assembled from actual encoded schema fields, never
native capabilities or fabricated positive consumer results.

These additions recognize envelope metadata only. Dispatcher handlers, issuer
checks, geometry rights, opaque ownership and native effects remain separate.
This codec delta establishes no implemented consumer behavior or native PASS.
