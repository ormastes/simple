# Item 5 immutable artifact mapping acceptance criteria

Status: NOT_IMPLEMENTED. These are planned observable acceptance criteria, not executed evidence.

Scope: I5-02, I5-03, I5-04 and I5-08: immutable bytes, mapping identity, sealed compiled artifacts and retained-root receipts.

Authority: the selected requirements in `doc/02_requirements/feature/runtime_optional_provider_binary_size_optimization.md` and the existing I5-01 through I5-14 acceptance plan remain intact. This package does not certify the whole item, any host, or any release.

The matching SSpec contains explicit failing skeletons only. It intentionally has no implementation helpers, fake success or execution results. No runtime, compiler, verification or doc generation is requested for this scaffold.

| Criterion | Requirement | Setup | Action | Observable threshold | Status |
|---|---|---|---|---|---|
| I5-P02-AC01 | REQ-002 REQ-013 REQ-015 | Install a sealed compiled provider with a trusted digest-bound manifest and independently recorded bytes and section identities. | Demand one capability and inspect the actual mapping receipt and payload result. | Mapped bytes match the admitted digest; one provider generation is mapped; the expected payload result and root reasons identify that artifact. | NOT_IMPLEMENTED |
| I5-P02-AC02 | REQ-002 REQ-012 | Alter one payload byte while retaining the original trusted artifact digest. | Demand the capability from the mutated artifact. | Typed digest refusal; zero callable permits, initializations and effects from the mutated provider. | NOT_IMPLEMENTED |
| I5-P02-AC03 | REQ-002 REQ-013 | Pin the admitted artifact; replace its pathname with a different valid provider before mapping. | Continue the same admission using the held artifact authority. | Either the original pinned bytes are mapped or a typed identity-change refusal occurs; the replacement provider performs zero initializations and effects. | NOT_IMPLEMENTED |
| I5-P02-AC04 | REQ-002 REQ-012 | Hold admission at the digest-to-mapping boundary; modify the original backing artifact in place. | Resume the admission without issuing a fresh authority receipt. | Only verified immutable original bytes may become callable; otherwise typed identity or digest refusal; mutated bytes perform zero effects. | NOT_IMPLEMENTED |
| I5-P02-AC05 | REQ-002 REQ-013 | Create a plausible receipt naming the correct artifact digest but without the admitted producer or trust authority. | Attempt demand admission and mapping using that receipt. | Typed trust or receipt refusal; zero published mapping permits, provider initialization and effects. | NOT_IMPLEMENTED |
| I5-P02-AC06 | REQ-002 REQ-013 | Keep manifest and artifact digests coherent; independently change pinned member name, offset, extent or payload digest, including an extent outside archive bounds. | Demand each changed member through production mapping admission. | Every divergent member is refused before mapping or payload execution; no receipt binds an out-of-bounds or mismatched section. | NOT_IMPLEMENTED |
| I5-P02-AC07 | REQ-002 REQ-015 | Install an independently loadable sealed pure-Simple provider; make its original source unavailable and observe source-read and parse counters. | Demand its capability through the installed compiled artifact. | Expected functionality works; zero provider source reads, source parses and source-compilation invocations. | NOT_IMPLEMENTED |
| I5-P02-AC08 | REQ-013 REQ-015 | Produce a real provider mapping receipt with section, dependency, constructor, export and metadata-root inventories; create independent mutations omitting a reason or changing an artifact identity. | Inspect the admitted receipt and submit each mutation to the production receipt gate. | Every retained mapping root has a reason bound to the exact artifact generation; incomplete or identity-divergent receipts are refused and never certify admission. | NOT_IMPLEMENTED |

Executable skeleton: `test/03_system/runtime/provider/item5_pending/p02_immutable_mapping_spec.spl`.
