# smux primary control V4 request

Source: `test/01_unit/os/apps/smux/runtime_primary_control_request_v4_spec.spl`.
Status: **NOT_RUN**. Manually authored companion; no executed acceptance evidence.

Seven scenarios assert explicit input attempt and byte-offset roundtrips;
attempt, offset, and requested-prefix bounds; positive resize attempts with zero
byte offsets/prefixes and legacy zero decode; delegated nested V1 validation and canonicality; exact typed V4
fields and authority-addition refusal; full-request digest and canonical token
binding; raw byte/token limits and representative authenticated-frame headroom.

The codec accepts input attempt sequences from 1 through 1152921504606846975,
offsets within the UTF-8 payload byte length, and requested prefixes from 1
through 4096 bytes. A prefix may exceed remaining payload bytes; the native
owner bounds the actual prefix. This codec neither retries nor creates attempts.
Resize preserves V1 geometry validation, permits explicit positive attempts up
to the same ceiling, and requires offset and maximum to be zero. Legacy resize
attempt zero remains decodable for an explicit unsupported handler response;
decode acceptance alone grants no effect. Other actions require all three
metadata fields to be zero and preserve V1 validation.

Canonical SDN is limited to 2800 bytes and its unpadded base64url token to 3734
bytes. Nested V1 requests retain their existing bound. Escape-heavy values can
fit V1 yet exceed the V4 bound and are refused. A normal 128-byte credential
and primary-control verb fit the server's separate 4096-byte frame budget at
the V4 token ceiling; the authored representative frame assertion is not a
server-dispatch or native input test.

No native session, authority issuance, input effect, retry guarantee, or cleanup
success is constructed or claimed by these pure request-codec specifications.
