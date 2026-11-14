# Named aspect ownership checkpoint — 2026-11-14

**Status:** Source implementation checkpoint; full parser, cache and tooling runtime qualification remains open. This is not get/set support or completed P0 admission.

The canonical flat parser now accepts named `aspect Name:` bodies containing existing `on pc` advice. Duplicate lexical names are diagnosed; legacy module-level advice keeps an empty name and receives a migration warning. Advice signatures and selector support are unchanged. Deferred get/set selectors remain rejected.

## Identity and transport

AST advice, HIR advice and both existing weaving-rule records append defaulted owner name/module fields. Existing constructors remain explicitly legacy. Built-in logging uses `simple.builtin.logging` / `CompilerLog` rather than impersonating a user aspect.

`ParserModule.name` is not an authoritative module identity. The shared frontend binds `SourceFile.module_name` after either parsing or AST-cache restoration, before desugaring. Binding creates fresh advice records and replaces every previous module context. Direct flat-parser users retain unresolved module identity; named advice without authority is rejected at HIR lowering and the driver AOP validation gate, including cached HIR input.

Advice-interface cache domain v2 binds both module and lexical name. HIR codec and canonical identity versions advance; old header payloads are rejected. The flat-pool header is uniquely `spl-flatpool-v16-field-array-sizes-aspect-owner-v1`. It does not claim compatibility with the separate, unmerged visibility-v17 layout. A future combined integration must retain both metadata sets and assign a fresh version.

## Actual evidence

The real imported codec generator first reproduced the original 99-declaration codec byte-for-byte; see [baseline report](aspect_codec_generator_baseline_2026-11-14.md). The same executable regenerated the owner payload, with seven additions and one replacement. No generated codec was edited manually.

- Generator executable SHA-256: `2b78217c925aa434aa1c5c4c0846ecdffccbbbac05f395f500ee24073749319c`.
- HIR definitions input SHA-256: `1084a7936fe66c822e8886ef7400c05b3da179da7254b3fcf2bd130a94828e49`.
- Generated codec SHA-256: `12f526cdad709b38e1f94d5c21c5e182d939c8f04468684d7cf057db41b51a35`.
- Receipt: `/tmp/aspect-codec-baseline-evidence-20261114/owner-generation.sdn`; real generator execution exit 0.

A bounded admitted pure-Simple P2/core-c native projection compiled and ran successfully, reporting **12 checks, 0 failures**. It uses exact production record definitions, owner rebinding, HIR advice lowering and weaving conversion, with only a recording diagnostic collaborator. It checks legacy defaults, unresolved-owner rejection, authoritative module replacement without mutating prior records, and name/module transport into weaving rules. This does not execute the full production parser or HIR pipeline.

Evidence: `/tmp/aspect-owner-transport-native-20261114/{extraction.sdn,compile.log,compile.rss.env,run.log}`. Generator attempts remain four total; owner transport is one distinct criterion/attempt. No repeated green run was used.

## Tests added but not executed

Production-parser specs cover named and legacy syntax, duplicates, the ordinary function name `aspect`, lexical owner restoration from flat cache, authoritative rebinding and old flat-header rejection. HIR specs cover unresolved owner rejection, owner transport, real encode/decode round trips and old HIR-header rejection. Cache specs separate differing owner modules/names and legacy identity. These SSpecs and full imported compiler/core/lib/MCP checks remain **UNRUN**, not passes.

## Remaining integration and parity

The interpreter consumes existing HIR advice and the shared matcher; it has no new independent named-aspect parser here. Its full source-to-execution route remains unqualified. Tree-sitter outline parsing has no corresponding named-aspect projection in this patch; its highlighting query still labels `aspect` aspirational. LSP document symbols, outline/hover owner presentation, catalog/pack owner serialization and end-to-end tooling parity therefore remain open. These are not covered by the native transport projection.

Typed accessor helper emission and every field-site consumer remain unimplemented. No helper is generated and no field weaving is enabled by this checkpoint. The [accepted architecture](../../04_architecture/compiler/aop/aspect_generated_accessors_2026-11-14.md) retains result/liveness, physical helper ownership, visibility, evaluation-order, no-aspect identity and broader field-place obligations for subsequent packets.
