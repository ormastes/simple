# TLDR-aware HIR cache manual

Status: source-only; seven executable criteria UNRUN. No measured performance,
RSS, native ABI, or lifetime claim.

The ordinary HIR codec version is `spl-hircodec-v5-admitted-abi`. Its extension
stores canonical sorted admitted symbol IDs after the generated module body.
Each ID must name a decoded Function symbol with a concrete type. The restored
map references that module's existing type graph; it does not recreate provider
IDs or deserialize a second type graph. Counts are bounded by decoded symbol
count before map allocation. Duplicate, descending, missing and invalid IDs
reject the cache entry. The generated codec remains unchanged.

The canonical portable codec remains guarded by its existing unavailable
generator gate. Its public encoder additionally refuses nonempty admitted ABI
metadata explicitly, even if the generator-availability gate is later changed.
This patch does not qualify or silently extend the canonical portable format.

Cache identity adds schema-domain-separated, sorted, length-framed authority
fields: module, source, producer, variant, ABI and payload digests. Module names
and digests are ASCII-validated before framing. No-header builds retain their
existing closure digest; malformed or duplicate-owner inputs return an empty
key and cannot masquerade as no headers. No payload or archive is hashed again.
The original closure/static-projection digest remains in the key. The admission
owner must still bind target/aspect/capture inputs and reject unsealed policy.

Both ordinary and strict header-bearing builds can use the cache. Strict mode
without admitted headers remains uncached. Existing explicit-semantic-policy
cache restrictions stay in place. The identity is computed once per selected
HIR pipeline, outside its per-module loop. Existing compiler identity and codec
version checks prevent old objects/entries being reused as this format.

Criteria:
1. Empty import list preserves the old key; admission order does not change it.
2. Each of the six authority fields changes the key independently.
3. Empty digest/payload and duplicate owner fail closed.
4. Existing static-projection/closure identity remains binding.
5. Actual parsed/lowered imported-function ABI survives module codec roundtrip.
6. Missing/duplicate/out-of-range extension IDs are rejected.
7. An admitted type inconsistent with its symbol is rejected on encode.

Execute through a rebuilt pure-Simple compiler with the candidate codec. The
current b467 compiler cannot qualify its successor's codec by loading a file.
Run cache-hit native call behavior, changed source/configuration invalidation,
and repeated decode/drop lifetime/RSS checks before asserting a speedup. Those
native and lifetime criteria remain UNRUN, as does ordinary unsupported-body
source routing in the independent planner lane.
