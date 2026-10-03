# Attributed collection factory admission

**Requirements:** REQ-PSC-001, REQ-PSC-003, REQ-PSC-005

**Executable source:** `test/01_unit/compiler/hir/attributed_collection_factory_spec.spl`
**Execution status:** BLOCKED — no admitted source-matched pure-Simple compiler is available for this worktree. This is a manual draft, not a generated or passing test receipt.

## Reject a wrong resolved factory family

1. Declare distinct adaptive text set and map types and a factory whose signature returns the map.
2. Admit that factory as the source of an attributed text set.
3. Check that HIR reports `attributed collection factory returns AdaptiveTextMap, expected AdaptiveTextSet` before MIR execution.
4. Repeat with a factory returning `text` and check that the non-adaptive return is rejected.

## Preserve two independent sites

1. Use one correctly typed text-set factory at two distinct `ast://` identities.
2. Check that both attributed calls admit without diagnostics; the parser's site literals remain separate arguments.

## Preserve unknown and unrelated calls

1. Pass a factory whose return signature is unresolved and an unrelated method name.
2. Check that this narrow guard does not claim proof or issue a family mismatch for either call.
3. Declare a user type also named `AdaptiveTextSet` in `app.custom_collections`; check that its method is outside stdlib adaptive admission.

SPipe docgen must replace this draft after the executable spec runs on an admitted compiler. A matching family alone does not prove generic key capability, exact source/target identity, plan selection, or MIR lowering.
