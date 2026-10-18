# Missing managed parser owner and compiled entry

Owner: Astra feature acceptance. Scope: two missing runtime files consumed by
the existing grouped runner/qualification fixture. Base `648420d`; maximum three
repair/check cycles; this is cycle one. Highest-model review is required.
No compiler/process launch is authorized in this lane.

`managed_parse_group_install_v1` admits the canonical snapshot, exact target,
bounded aggregate source bytes and each source digest. The action owner reads
and hashes the exact bounded bytes it passes to the real parser; it does not
ask the parser to reopen a pathname. Flat globals remain serialized within the
process. The bridge already resets parser pools per module, allowing errors
around a valid independent module without losing their diagnostic receipts.

The action arms/takes the existing flat capture bridge and publishes raw flat
payloads matching the ordinary compiler frontend cache payload. Durable cache
hits require canonical module receipt, source identity, blob digest and decoder
acceptance. A separate authority digest binds snapshot, producer, target,
codec, parse kind and the existing frontend feature fingerprint. Missing or
invalid authority/receipt/blob means a miss; unreadable cache I/O and reported
parser policy errors are explicit errors. No error parse is cached.

Authority sidecars use the per-module CACHE-2 key plus `.authority`, binding
worker/cache/target/module/source identity without batch snapshot, slot or
generation. Canonical sidecar fields additionally bind parse kind, flat codec
and actual frontend feature identity. The existing reaped-generation parent
copier now validates and carries this sidecar together with the verified module
receipt/blob. Missing, malformed or wrong-key sidecars remain cold. Parent
validation uses only existing lightweight wire/digest contracts; it does not
import the parser, flat codec or frontend cache owner. Worker consumption
independently requires its actual codec and feature fingerprint, so a copied
incompatible sidecar cannot produce a hit. Worker image/compatibility/target
authority remains bound by CACHE-2 during parent key construction.
This packet depends on the separately owned CACHE-2 contract correction
`025173cd1d4`; no request/result snapshot binding is weakened.

Diagnostics use canonical `DiagnosticV1` JSON within the existing SDN result
codec, preserving original located parser text and deterministic diagnostic
identity notes. No replacement diagnostic schema or invented byte span is
introduced. Source/cache/policy errors have explicit distinct stable codes.

The compiled entry decodes the admitted install/action protocols, publishes
the exact installed marker expected by the runner, validates mailbox hashes,
writes canonical results, and validates shutdown identity. It uses existing
argument/file/clock facades, no local process/env extern or subprocess. Its
loop has a seven-day ceiling matching the existing broker policy maximum;
the broker's tighter admitted process deadline remains the lifecycle authority.

New SSpec uses actual parser behavior, rich AST lookup, captured blob parity,
canonical diagnostic/SDN round trip, durable reuse, cache corruption negatives,
source changes, target/policy rejection and entry marker/shutdown/mailbox checks.
Runtime, docgen and live process qualification remain UNRUN. No nine-feature
completion, Phase3 admission or release PASS is claimed.
