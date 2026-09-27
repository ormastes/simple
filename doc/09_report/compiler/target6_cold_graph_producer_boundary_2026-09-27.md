# Target 6 cold graph producer boundary (2026-09-27)

Status: source audit; current-source runtime and performance proof pending.

The frozen-inventory graph builder is present, but no production caller can
yet supply its complete typed artifact inputs. This report records the exact
ownership gap before any driver cutover.

| Required fact | Current production evidence | Required cutover work |
|---|---|---|
| Typed module identity, ABI, and direct imports | `cold_hir_semantic_seed_v1.spl` derives these from a `HirModule` and verified source content. `driver_hir_pipeline_lowering.spl` retains HIR for the current request's `ctx.sources`. | Prove that the selected index inventory is covered by those HIR modules, or define an exact package-scoped partition bound to the parent SCV snapshot. Do not fabricate rows for sources outside the lowered set. |
| TLDR section directory and SMF payload | `package_tldr_metadata.spl` defines and validates `PackageSmfSectionV1` and `PackageExportSmfV1`. A source search found no production constructor of either record. The existing watcher `smf_manifest.spl` maps source paths to compiled SMF artifacts; it is not the typed section producer. | Emit real sections from compiler-owned SMF bytes, with offsets and digests checked against the artifact before building a TLDR header. |
| Interface/action archive receipts | `interface_action_archive.spl` decodes and admits pinned archives. The only production constructor of `InterfaceActionArchiveV1` is its decoder. | Produce archive members and receipts from typed compiler outputs, then pass their actual digests to the cold draft assembler. |
| Persistent generation | `compiler_entrypoint/admission.spl` is the only production caller of `package_module_index_publish_v1`; it publishes an empty snapshot-binding generation. | Publish a validated graph generation from the cold builder after artifact production, and preserve one immutable generation for each request. |
| Warm compatibility markers | `driver_source_pipeline_loading.spl` reads producer, root-generation, and variant-digest environment markers. No production owner sets those three markers. | Set markers from the admitted graph generation and configuration variant, then remove the binding-only cold fallback when the full route is qualified. |

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
