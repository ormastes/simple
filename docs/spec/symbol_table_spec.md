# symbol_table_spec

*Source: `simple/std_lib/test/features/stdlib/symbol_table_spec.spl`*

---

Symbol Table Cross-Refs - Feature #202

Overview:
    Full symbol table with cross-reference support for code navigation.
    Includes RefKind enum, SourceLocation, Reference, QualifiedSymbol classes,
    and query methods for finding references, implementations, callers, and
    inheritance chains. Foundation for LSP implementation.

Syntax:
    val table = build_symbol_table([ctx1, ctx2])
    val refs = table.find_references("Parser")
    val impls = table.find_implementations("Serializer")
    val graph = table.build_call_graph()

Implementation:
    - RefKind enum: Import, Call, Implements, Inherits, Uses, Instantiates, Overrides
    - SourceLocation: tracks file, line, column
    - Reference: links from_symbol to to_symbol with kind
    - QualifiedSymbol: module path and optional parent
    - Query methods: find_references, find_outgoing_references, find_implementations
    - Call graph building: build_call_graph, build_reverse_call_graph
    - Inheritance analysis: get_inheritance_chain
    - Symbol filtering: get_symbols_by_kind, get_public_symbols

Notes:
    - Foundation for LSP implementation
    - Supports call graphs, inheritance chains, and impact analysis
    - Complete cross-reference tracking
