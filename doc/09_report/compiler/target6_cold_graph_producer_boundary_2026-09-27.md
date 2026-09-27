# Target 6 cold graph producer boundary (2026-09-27)

Status: source audit; current-source runtime and performance proof pending.

The frozen-inventory graph builder is present, but no production caller can
yet supply its complete typed artifact inputs. This report records the exact
ownership gap before any driver cutover.

| Required fact | Current production evidence | Required cutover work |
|---|---|---|
| Typed module identity, ABI, and direct imports | `cold_hir_semantic_seed_v1.spl` derives these from a `HirModule` and verified source content. `driver_hir_pipeline_lowering.spl` retains HIR for the current request's `ctx.sources`. | Prove that the selected index inventory is covered by those HIR modules, or define an exact package-scoped partition bound to the parent SCV snapshot. Do not fabricate rows for sources outside the lowered set. |
| TLDR section directory and SMF payload | `cold_hir_abi_smf_section_v1.spl` emits one actual ABI section from typed HIR. `package_export_smf_build_v1` now assembles caller-supplied section bytes in canonical order and binds the complete payload, offsets, extents, and section digests; `package_export_smf_payload_validate_v1` checks those bindings on admission. It does not create the other semantic sections. The watcher `smf_manifest.spl` maps source paths to compiled SMF artifacts; it is not the typed export producer. | Emit initializer, provider, generated-source, reverse-reference, and deep export bytes from their real owners, then pass them through the byte-bound builder before building a TLDR header. |
| Interface/action archive receipts | `interface_action_archive.spl` decodes and admits pinned archives. The only production constructor of `InterfaceActionArchiveV1` is its decoder. | Produce archive members and receipts from typed compiler outputs, then pass their actual digests to the cold draft assembler. |
| Persistent generation | `compiler_entrypoint/admission.spl` is the only production caller of `package_module_index_publish_v1`; it publishes an empty snapshot-binding generation. | Publish a validated graph generation from the cold builder after artifact production, and preserve one immutable generation for each request. |
| Warm compatibility markers | `driver_source_pipeline_loading.spl` reads producer, root-generation, and variant-digest environment markers. No production owner sets those three markers. | Set markers from the admitted graph generation and configuration variant, then remove the binding-only cold fallback when the full route is qualified. |

The existing AOT SMF writer is not that typed section producer.
`driver_aot_smf_output.spl` concatenates backend object bytes from the
current MIR modules into one executable SMF. `smf_writer.spl` lays out code,
template, dependency, driver-manifest, and launch-metadata sections plus one
`main` symbol. It does not emit per-module exported symbols, public types,
layouts, or constants for `PackageExportSmfV1`. Its `note.sdn` section also
uses a zero extent in the table, while the TLDR section-directory validator
requires a positive extent. The cold producer must issue typed export bytes
from HIR and validate their own bounded section directory; treating the AOT
image as a package TLDR would bind unrelated or absent semantic facts.
The ABI section uses `hir_abi_interface_encoded_v1` so its digest equals the
existing typed ABI identity. A focused scenario passes those actual bytes to
the new package export builder and verifies the resulting directory. This is
still a partial producer; no complete package export SMF may be published until
the remaining semantic section owners supply their own bytes and receipts.
The new payload admission check has not run on a current-source test worker.

The isolated archive reader now validates digest bytes and canonicalizes
dependency digests with the shared heap sort. This removes native text
comparison and quadratic sorting from that admission step. It does not
produce missing archive content or prove a time/RSS result.

The next executable gate is a current-source test worker. The three bounded
build attempts and retained logs are in
`doc/09_report/compiler/target6_test_worker_build_2026-09-27.md`; this session
must not repeat them. A qualifying worker must run the cold draft, SCV
recovery, graph, SCC, archive, and warm-route scenarios before production
publication or performance claims are accepted.
