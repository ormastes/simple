# Native outline declaration boundaries

Manual companion to `test/01_unit/compiler/frontend/native_outline_declaration_boundaries_spec.spl`. Authored manually; execution and generated documentation: **NOT_RUN**. No timing, coverage, protocol or full source-view qualification is claimed.

The helper `lsp_native_outline` creates the released canonical `TreeSitter` through `treesitter_new`, explicitly disables heuristic mode, and invokes `parse_outline`. No source-view adapter or unlanded contract participates.

| Scenario | Production assertions |
| --- | --- |
| Consecutive inline bodies | Both function names and exact declaration/body UTF8 byte spans; constructor authority fields initialized |
| Inline class methods | Both method names/ranges and following outer function |
| Nested multiline body | Both functions, bounded first body and exact second declaration range |
| Inline assembly | Following function, braced payload, nonlegacy metadata and exact assembly/payload spans |
| Opaque expression block | Following function, block kind, parent context and exact block span |
| Import forms | Native `use` and `import`, grouped items, star, relative module/group, alias, lazy modifier and exact import end offsets |
| Relative prefix token controls | Actual DotDot/Ellipsis module/group/star forms, exact ends and DotDotEq native rejection |
| Interspersed imports | Both imports and both functions remain represented |
| Unicode | Korean/emoji before declaration and inside body retain canonical byte offsets |
| Malformed neighboring import | Actual native error message is retained |

Steps: prepare the real fixture; invoke the production owner; check the observed contract; check the neighboring failure case. The fixtures use literal byte-range oracles, not values calculated by the implementation under test. Multiline body bounds allow the owner's structural newline/dedent span, while checking the following declaration exactly.

Pending command, only after an admitted self-hosted runtime is available:

```sh
SIMPLE_LIB=src "$SIMPLE_BIN" test test/01_unit/compiler/frontend/native_outline_declaration_boundaries_spec.spl --mode=interpreter
```

Runtime admission, generated-manual verification and broader compiler/MCP/LSP gates remain pending. This isolated owner repair does not complete VIEW requirements, source sessions, authentication, diagnostic workers, actions or performance targets.
