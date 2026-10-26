# Seed test-result cache can reuse results without sufficient identity

Status: SOURCE_CONFIRMED_RUNTIME_REPRODUCTION_PENDING. Canonical bug DB
reconciliation is pending while qualified database tooling is unavailable.

The bootstrap-only Rust owner is
`src/compiler_rust/driver/src/cli/test_runner/result_cache.rs`.
`CachedResult` records file size and modification time rounded to whole seconds;
`ResultCache::check` accepts equality of those two fields. The persisted key is
a normalized path. Source content, imported dependencies, compiler identity,
execution mode and host capability configuration are absent from this owner.

Consequently, a same-length edit within the recorded second, preserved file
timestamps, or a producer/configuration change is not sufficient to invalidate
a stored result. This is a source-derived counterexample, not an executed
reproduction or a count of observed false passes.

The new seed's test request must use `--no-cache` and its own result database
until trustworthy cache identity is implemented. Preserve previous passing
rows as historical producer evidence; do not count them as newly executed or
qualified results for a different producer. This bypass concerns test-result
certification, not valid compiler object/frontend caches.

Required reproduction and prevention controls: equal-size changed contents
with preserved timestamps; different contents within one timestamp second;
changed imported dependency; changed compiler, backend or execution mode;
changed applicable skip/capability facts; unchanged inputs; and corrupt or
legacy cache records. All are currently UNRUN for this bug.

The repair must use a complete execution identity and input/dependency identity,
with bounded memory and no repeated full-source hashing on warm checks.
Do not replace missing identity with a newer timestamp. Review the canonical
pure-Simple test-cache owner for the same defect before accepting parity; its
current behavior is not established by this Rust source inspection.
