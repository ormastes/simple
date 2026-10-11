# Stage 2 package-route conditional construction — 2026-10-11

Canonical attempt 3 from clean source `2247e563fa60fc4dc1a28a8346d1806fefcc39b5`
passed full preflight, including its 20 GiB disk floor (27 GiB available), then
failed Stage 2 discovery at `package_index_route.spl:143:18`: expected expression,
found Else. Strict construction refused a seed fallback. No admitted Stage 2
runtime was produced. Attempt 2 had stopped at the post-Cargo disk check
(18 GiB versus 20 GiB); the earlier attempt stopped below its initial floor.
The three-attempt canonical cap is exhausted; no fourth bootstrap was run.

The production correction puts the existing conditional entirely on one line.
It preserves the schema-version comparison and both selected/changed branches.
This is a source-layout compatibility fix, not a parser repair or proof that the
rejected mixed layout is valid language syntax. The production transition,
validation and invalidation owners are unchanged.

A separate modern SSpec control reproduced the mixed-layout construction error
at line 9:18 (construction exit 1, zero executed examples). After the identical
layout correction, its isolated constructor compiled 44 modules with zero
failures. The produced native program ran once: **4 examples, 0 failures**, exit 0.
The scenarios inspect legacy, current, future and empty current-schema inputs.
Rust seed usage was restricted to construction; only the produced native program
executed the scenarios. This control does not execute the full package-cache route.

The production fix has not completed canonical bootstrap or the required
compiler/lib/MCP/LSP/full-suite checks. Runtime admission and release verification
remain unqualified. The default-factory defect and graph SIGSEGV are separate,
unresolved defects; their test changes are excluded from this focused release PR.
The original 20 REQ-TRC /40 AC-TRC and WP0–WP7 retain their scope and open gates.

Evidence is retained under the owning worktree's `build/session/` and
`build/native_probe/`, including attempt 2/3 transcripts, frozen control sources,
producer metadata and native observations. Ignored records are private host audit
material. Their SHA-256 hashes establish integrity, not authenticated admission.
Two clean retired checkouts were sparsified after proving branch/status and all
ignored-file hashes unchanged (4 and 53,163 files); no artifacts were deleted.

## Frozen grammar evidence digests

| Host-relative path | SHA-256 |
| --- | --- |
| `build/native_probe/traceability-stage2-route-grammar-20261011-red/spec_source.spl` | `94a01392fe8e34de00103c54a29848ea89cd293e076882cd3ab26d025c90a473` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-red/construction.log` | `f1352cd7ac0a6a5f877b59684b91c53a7899c63af0f7c80db28a7581c05ca10f` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-red/construction-status.txt` | `4355a46b19d348dc2f57c046f8ef63d4538ebb936000f3c9ee954a27460dd865` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-red/producer.json` | `824c11a405d7d1e1910e5781e8f521616fb05bcf4b68d4a78bc0302122edb050` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/spec_source.spl` | `eed40b7bb8d685713b076e847e92b952b1c9c2c3f57d8435761adad0b2284d27` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/construction.log` | `b0ed92646a6cc690d3cdaa46024447a8d7fd5f2c959675789b613a133cf8b626` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/construction-status.txt` | `9a271f2a916b0b6ee6cecb2426f0b3206ef074578be55d9bc94f6f3fe3ab86aa` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/producer.json` | `824c11a405d7d1e1910e5781e8f521616fb05bcf4b68d4a78bc0302122edb050` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/execution.log` | `4675c9209265d226216916222e89cea81bac43cf8420dd5d4358b683dc82049b` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/execution-status.json` | `1881c6f382ffed5fb922b94a3b67163d9a30df95cc6099dc60080f925d62b553` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/production_source.spl` | `832530b702b64dce9e206a58c5d1dd589c9183a3cbbaa49f9d60f77f995a8b93` |
| `build/native_probe/traceability-stage2-route-grammar-20261011-control/simple` | `2d5b24fedfe5059c19ca2499f611501b4dcbb6deaf4eedf5a2d28a58ef4cef76` |

## Release integration update

Release commit `a7c39dc8f5d` independently repaired the production conditional
using a complete block-form `if`/`else`, preserving the same schema comparison
and both branch values. The original PR2968 single-line production hunk is now
superseded and is omitted during conflict resolution. The release owner remains
byte-identical to that already-landed implementation.

The four-case single-line construction control and historical evidence above
remain useful regression material. They do not qualify the current block-form
production owner, repair the parser, or satisfy runtime/admission gates. No
historical passing test was replayed during this evidence-only integration.
