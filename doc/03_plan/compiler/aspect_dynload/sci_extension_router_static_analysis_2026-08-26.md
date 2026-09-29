# SCI extension router — static complexity and memory analysis

Scope: authored source review only. No runtime, build, test, benchmark, SPipe,
optimizer, or gate claim is made by this document.

## Startup routing

`simple_core` admits the canonical SCI once with the existing decoder. That
one-time cold phase is `O(S)` time and memory for image size `S`, including
directory and layered digest validation. Extension routing then extracts the
already-admitted section 10, lexically scans one selected token, and delegates
to the existing sorted-index reader. For section size `R`, `N` namespaces, and
an equal-hash run of `C`, current routing is `O(R + token_bytes + log N + C +
provider_id_bytes)` because the admitted-section accessor returns an owned
section copy. Exactly one route record is decoded on a hit and zero on a miss.

The existing file adapter owns the canonical `O(S)` SCI byte array. Decode
authenticates the directory, every section, the complete composition digest,
and the nested section-10 digest before lookup; the separately admitted
artifact SHA prevents a different valid SCI from being substituted. Routing
adds only bounded result text: namespace, key, optional value, provider ID,
and diagnostics plus the `O(R)` admitted-section copy. It does not allocate per
registered namespace, construct a runtime registry, or retain a second
provider lifecycle. CLI-0 help/version remain ahead of extension routing; the
existing simple-core provider admission/query/invoke/release/close owner is
reused. The generic reader materializes lookup-key bytes and the selected
provider ID; these are output-proportional, not `N`-proportional allocations.

There is one dispatch decision on the SCI record's integer `route_kind`; no
reflection, function-valued table, or dynamic language dispatch was added.

## Configuration/artifact generation

`sci_compile_extension_config_v1` is explicitly outside startup. It parses the
source once, emits one route per namespace, and delegates ordering and encoding
to the single existing SCI generator. Its live memory is `O(S + N + A)`, where
`A` is emitted artifact size. Existing generator duplicate detection and
selection ordering are `O(N^2)` build-time work; no second sort or artifact
copy is introduced here. SHA-256 is computed once for the exact configuration
text and once for the generated artifact.

The authored, intentionally unexecuted spec mutates namespace membership and
provider binding. Each mutation must change both hashes and the selected route;
removal must fail closed. These are correctness contracts, not runtime proof.
