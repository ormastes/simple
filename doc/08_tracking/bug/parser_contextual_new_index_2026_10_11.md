# Contextual new identifier indexing emits unsupported allocation AST

Status: OPEN. Canonical bug ID: `parser_contextual_new_index_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/3000

Original failure: new[index] follows allocation parsing because contextual keyword lookahead omits LBRACKET; EXPR_NEW tag50 lacks bridge lowering. Dot access was not the defect.

Workaround commits:

- `d9719ec822307887511eb3637f35a3b4fc48f8d5`; recovery parent `f25bf97f47c021359e5321e1c8ae0b584d1cce4f` (review only).

Current qualification: C36 affected source HIR7/MIR7/native7 PASS; ARM ELF183 123144bytes SHA256cb00e8c8b1ccecf28560992b786fc9d25e1d91d3bddcbb66716c44862cb7d4d1. Behavioral unit spec not executed.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/manual-affected-source-objects-c36-reviewed-fixes/semantic-facet/result.json`.

Reproducing/prevention source: `src/compiler/00.common/cache_contract/semantic_facet_manifest_v1.spl`.

Background fix owner and removal condition: Parser contextual keyword/index owner. Restore six renamed bindings only after original new[index] and legitimate new-allocation disambiguation regressions pass native lowering.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: d9719ec822307887511eb3637f35a3b4fc48f8d5 -> d9719ec822307887511eb3637f35a3b4fc48f8d5 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Affected ARM object source aeb2517fac0a3f287aed4347d75235ac8976161d includes d9719ec822307887511eb3637f35a3b4fc48f8d5; behavioral spec unexecuted.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.
