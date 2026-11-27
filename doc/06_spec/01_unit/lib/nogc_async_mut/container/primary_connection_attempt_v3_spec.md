# Primary connection terminal-attempt metadata V3

Status: **AUTHORED_NOT_RUN**. Requirements: HOST-03, MUX-02, CTR-02.

Source: `test/01_unit/lib/nogc_async_mut/container/primary_connection_attempt_v3_spec.spl`.
This is an authored manual; docgen and test execution have not run.

The production codec has exactly two terminal metadata dispositions:
`not-opened` requires both pipe identity fields to be SDN null, while
`pipe-closed` requires a bounded slot and positive generation. Neither encoding
contains a `closed: true` or authority flag. Both bind request and consumption
digests, use the fixed Windows provider/attach-attempt domain, and prohibit
pending read/write claims. SDN null is the canonical wire form of absent Simple
option values.

## Ten authored cases

1. Round-trip both dispositions, all correlation fields and fixed flags.
2. Reject either or both invented pipe identity fields on `not-opened`.
3. Require both closed-pipe fields; preserve slot and generation boundaries.
4. Reject negative/overflow slots and nonpositive generations.
5. Reject malformed, uppercase, short and long digests on both codec boundaries.
6. Reject every missing field and extra authority/old-closure fields.
7. Reject pending IO and scalar type coercions.
8. Reject foreign versions, domains, providers and dispositions.
9. Reject duplicate keys and noncanonical source spellings.
10. Enforce UTF8 byte bounds and reject malformed/nonobject documents.

Each case calls the actual pure encoder/decoder. Successful decoding proves
only schema/canonical-byte validity. It cannot mint a successful claim,
no-connection proof, native pipe closure, helper settlement or parent-resource
release. Those require the separate private proof producer and retained Host
writer. No native calls, Windows fixture qualification, journal integration or
fault injection are covered by this codec inventory.
