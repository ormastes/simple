# Aspect predicate and instance identity driver slice

Status: implementation candidate for parts of REQ-DTA-E1/G1. This is not an
admitted plugin loader, a traversal-plugin generator, or completion of F1.
The selected requirements remain in `doc/02_requirements/feature/dir_tldr_aspect.md`.

## Ownership

`compiler/00.common/cache_contract/aspect_plugin_model_v1.spl` owns the pure
`Pointcut` trait and `SelectorPointcutV1`, closed plugin configuration schema,
canonical identity and bounded descriptor pool. Predicate compilation delegates
to `pointcut_selector_parse_v1`; matching, shard identity, advice application
identity and weave deltas retain their existing owners.

`compiler/80.driver/cache/aop_match_cache_driver_v1.spl` owns the serialized
pool and the new `aop_plugin_match_shard_acquire_v1` entry point. It obtains a
descriptor and invokes the same single-flight/shard acquisition used by the
legacy path. The existing selector-plan cache uses `SelectorPointcutV1` and
still avoids parsing on an exact source hit.

The new entry point requires an explicitly supplied plugin code digest. It
does not derive code identity from an advice name, registry key, compiler
version string or mutable source file. Existing registry claims have no
admitted plugin definition/configuration producer, so their legacy weave path
continues unchanged. Connecting that producer remains required work.

## Identity and bounds

The definition declares each field as `Instance` or `Scope`. Names can be
plugin-specific; there is no hard-coded list of directory/matcher spellings.
Inputs must contain every declared field exactly once and no other field.
Duplicate declarations, duplicate values, invalid names and invalid code
digests fail before insertion.

The code digest must use the existing SHA-256 registry format. The instance
key is SHA-256 over a domain-separated, UTF-8-byte-length-framed encoding of
the code digest, sorted field names and roles, and instance-field values.
Scope values are removed; their declarations and roles remain in identity.
Reclassifying a field changes the key. Input order does not change the key.
No configuration text is case-folded or trimmed: semantic value normalization
belongs to the plugin's admitted configuration producer.

A descriptor retains only instance values. Reusing it cannot retain the first
request's directory or matcher. A hash hit additionally requires exact
canonical identity equality. Limits are 128 fields, 65,536 combined input
bytes, and an explicit pool capacity of 1–4,096 descriptors. The driver uses
256. A full pool refuses new identities and still serves existing identities;
there is no executable-code eviction or memory-reclamation claim.

`created_count` counts descriptor construction, not native library loads,
plugin code executions or successful plugin admission. The pool is owned by
one serialized driver loop; it provides no standalone thread-safety guarantee.

## Directory and behavior separation

The new driver API obtains matches only from its explicit selector and
`DirectoryJoinPointFactsV1`. Per-directory results retain
`pointcut_match_key_v1(selector, facts)` and the existing digest checks. Plugin
code/configuration does not change those pure selector results; advice/body
changes belong in the existing advice-application key. Unsupported selectors
or incomplete facts are rejected by the new entry point.

Persisted directory inputs must first pass the directory-TLDR owner's
admission factory; the API is not proof that arbitrary public facts were
admitted. The parallel TLDR work owns `DirectoryTldrViewV2`. A future F1
planner view may combine that admitted view with immutable prior shard/apply
state, but this slice creates no competing `DirTldrView` or on-disk format.

Future placement names are `Placement` (trait) and `AspectPlacementKindV1`
(closed enum). Static MIR injection remains the only weaving owner. No dynamic
around-advice, partial-facts unweaving, or new weaving engine is introduced.

## Evidence scope

New unit and driver specs cover parser parity, cross-directory reuse, scope
removal, sorted identity, code/config/schema invalidation, malformed input,
capacity refusal, collision verification and per-directory cache independence.
Full SSpec/driver execution and plugin-production integration remain pending
until an appropriate runner and admitted producer exercise those paths.

On 2026-11-14, a receipt-matched pure-Simple Stage 2 producer compiled an exact
extraction of `plugin_config_canonical_v1`, its data types/helpers and the
existing digest registry validators into one native AArch64 object. Eleven
native checks passed, including UTF-8 byte framing and negative configuration
cases. This proves that extracted normalization path, not SHA generation,
pool behavior, trait dispatch, full driver wiring or the SSpec harness.
The evidence directory is `/tmp/aspect-plugin-canonical-probe-20261114`;
producer SHA-256 is
`3b38223677dd46f92c29c12f20566dc9e65c6b65b1456c9c89c95907b5e106ec`.

Performance remains unqualified. The new convenience API canonicalizes and
hashes configuration on each acquisition. The eventual producer should obtain
the descriptor at its configuration boundary and carry it across directory
visits; a reviewed prepared-descriptor driver entry point is still needed to
avoid repeated normalization. No NFR-DTA latency or shared-instance execution
claim follows from the construction counter or the focused native test.
