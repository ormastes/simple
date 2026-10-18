# Missing managed parser owner and compiled entry

Owner: Astra feature acceptance. Scope: two missing runtime files consumed by
the existing grouped runner/qualification fixture. Base `648420d`; maximum three
repair/check cycles; this is cycle two. Highest-model review is required.
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
acceptance. A separate authority sidecar binds the per-module key, codec,
prepared source, cfg decisions and actual frontend feature/capture policy. Missing or
invalid authority/receipt/blob means a miss; unreadable cache I/O and reported
parser policy errors are explicit errors. No error parse is cached.

Authority sidecars use the per-module CACHE-2 key plus `.authority`, binding
worker/cache/target/module/source identity without batch snapshot, slot or
generation. Canonical sidecar fields additionally bind parse kind, flat codec
and a digest of actual frontend feature/capture policy, prepared bytes and cfg
decisions. The existing reaped-generation parent
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

Cycle-two parity correction shares the ordinary frontend's domain extraction
and checked advisory preparation. The worker first uses the existing explicit
snapshot OS/architecture cfg evaluator (whose `cpu` predicate aliases arch),
then parses/restores the exact prepared bytes. It reattaches extracted domains
and applies the same desugaring on both paths. Flat artifacts remain reference
parser pool payloads, not serialized final desugared modules: an ordinary
frontend consumer repeats preparation, domain attachment and desugaring. The
original source digest stays request-bound; transformed bytes and decisions
add cache authority rather than replacing original input identity.

OPEN SUPPORT GAP: `SIMPLE_CAPTURE_WRITE_CHECK=warning` deliberately suppresses
capture for a successful warning parse. V1 results require a flat artifact and
cannot honestly represent this successful noncacheable outcome. Installation
therefore explicitly refuses warning mode; a post-install change fails policy
validation before parsing. This temporary limitation does not close full worker
acceptance. Future support must add a versioned noncacheable-success result with
canonical warning diagnostics and parent consumption semantics, or extend the
canonical capture/restore policy to retain and replay warning evidence without
silencing warnings. It must preserve ordinary warning-success semantics and
prove cold/warm parity before warning mode can be admitted. No fake artifact,
policy bypass or conversion of warning-success into source ERROR is acceptable.
