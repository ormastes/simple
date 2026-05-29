<!-- codex-design -->
# All Regions Detail Design

Filed: 2026-04-22

## Staged Implementation

Phase 1 implements planning and tracking artifacts plus feature requests.

Phase 2 implements raw domain-block carrier support for `schema{}` and `style{}`:

- lexer/parser raw payload capture;
- AST node or declaration carrier;
- Tree-sitter outline entry;
- parser tests for nested braces, unterminated payloads, and identifier compatibility;
- no semantic validation beyond approved block kind and payload preservation.

Phase 3 implements `schema{}` semantics:

- field names, optionality, defaults, ranges, regex, units, identity fields, field IDs;
- JSON Schema export for validation;
- Protobuf-compatible numbering/evolution checks for wire contracts.

Phase 4 implements dedicated domain semantics by priority: style/ui, rtl, music, bim/city, cad.

## Error Handling

Raw block parse errors should report block kind, opening span, and missing closing brace. Semantic passes return `Result<T, E>` and must not silently coerce invalid domain syntax into SDN.

