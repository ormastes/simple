# Target 6 entry-scoped cold graph contract

Status: focused native graph and route PASS; production driver cutover OPEN.

An entry-closure compile may lower fewer modules than the frozen inventory
contains. The existing V2 builder correctly demands one draft per `.spl` in
that inventory. V3 now represents a different, explicit scope: one entry
source identity, the digest of the full frozen inventory, and exactly the
closed set of modules reachable from the entry. V2 retains full inventory
coverage. No omitted module is synthesized to make a partial graph appear
complete.

The canonical V3 payload and action digests bind the entry identity. Decode
checks root presence, direct/reverse edge closure, and reachability of every
stored module. The cold builder checks every submitted source digest against
the full inventory. The existing archive verifier reads and verifies each
reached package archive before its compare-and-swap index publication. Warm
routing refuses V3 for a different entry or an unscoped full build.

Focused no-stub ARM64 native evidence used the frozen pure-Simple Stage2
capsule SHA-256
`5d71c26b371b83d0041e10b815dae153a38b9f7c61aa0931f3473aaee919e2f6`:

| Entry | Compiled units | Result |
|---|---:|---|
| `cold_hir_compact_output_index_spec.spl` | 323 | 6 examples, 0 failures; V3 subset, missing import, extra node, and persisted archive publication |
| `package_index_route_spec.spl` | 67 | 7 examples, 0 failures; full/different entry refusal plus existing route cases |
| `package_module_index_spec.spl` | 44 | 3 examples, 0 failures; V1/V2 canonical roundtrip and publication |

The final compact-spec binary SHA-256 is
`940ad4b7ed165adcf252f64a68c2e96711356da1e1872d4d4e26cbe59611da70`;
the route and legacy-spec SHA-256 values are
`ca0be67c2591785de1a62e24ec76fe9f244fef3f6b0c6deaa436367977db815e`
and `e8c3edb43f81c58295dca2907c7c0147aafcff6e4488abad38b709107eb1e28a`.
The simple-core archive was an isolated hosted bootstrap aid for these
focused specs, not product runtime authority.

Production still needs to retain typed HIR receipts before source/HIR
eviction, generate real per-package action/interface archive receipts, and
call the scoped publisher from the driver. It also needs the system SPipe,
compile/check/bootstrap/MCP/LSP/daemon route gates, and native time/RSS
cohorts. V3 decoding performs an extra linear reachability check; no measured
production latency or RSS claim is made here.
