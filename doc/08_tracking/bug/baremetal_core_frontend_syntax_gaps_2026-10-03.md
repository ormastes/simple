# Baremetal syntax facts missing from the self-hosted core frontend

**Status:** OPEN — source triage only; runtime UNRUN.

**Source base:** release/1.0 `c4c353326bdce0e56930464bfafed8ab1e83c604`.
**Executable regression:** canonical `test/01_unit/compiler/native/baremetal_syntax_spec.spl`, repair commit `9b10374b22a568c2a8d9a687b044407856b990ac` (separate branch). The regression intentionally fails when a promised fact is missing; no string-literal check counts as coverage.

The four gaps below are not isolated bridge assignments. Each needs an owning grammar/flat-AST representation decision before the bridge can carry a truthful fact. No compiler change is proposed from this read-only trace.

| Feature | Current parser path | Missing fact / repair boundary |
| --- | --- | --- |
| `@volatile` field and module binding | `core/_ParserDecls/fn_struct_decls.spl:989-1065` sends member `@...` to `parser_parse_member_attribute`; `enum_module_body.spl:637-710` consumes all member names but records only `unsafe`/`danger`. Top-level `@volatile` falls through the generic decorator arm at `enum_module_body.spl:1199-...:1670` and is reset after the next declaration. | `core/_Ast/decl_nodes.spl` has no volatile field/binding slot. `flat_ast_bridge/module_assembly.spl:228-264,945-959` constructs `ParserField`/`ParserConst` with `is_volatile:false`. Add validated field and binding grammar, flat slots/reset/codec, then propagate. A bridge-only `true` would fabricate volatility. |
| `@repr(C)` struct | The module decorator reader stores raw spelling in `PENDING_DECL_ATTRS`, but the generic unknown-attribute arm consumes it without a typed declaration fact. `parser_pending_asm_placement` in `enum_module_body.spl:740-763` deliberately selects function placement attributes and excludes `repr`. | `core/_Ast/decl_nodes.spl` has no struct layout attribute slot; `flat_ast_bridge/module_assembly.spl:522-530` emits `ParserStruct(attributes: [])`. The existing `compiler.common.attributes.parse_layout_attrs` can interpret an `Attribute` only after the parser/flat pool preserves one. Add struct attribute representation and bridge conversion with C argument validation; do not reuse asm placement. |
| `val REG: u32 @ 0x40000000 = 0` | `core/parser_decls_use.spl:447-493` parses name and optional type, then immediately requires `=`. There is no postfix `@ address` arm. The tree-sitter outline (`10.frontend/treesitter/outline_decls.spl`) describes this form, but it is not the native-build core parser. | `core/_Ast/decl_nodes.spl` has no fixed-address slot. `flat_ast_bridge/module_assembly.spl:945-959` hardcodes `ParserConst(has_fixed_address:false, fixed_address:0)`. Define syntax/value validation and flat representation before bridging; the current snippet should produce a parser diagnostic. |
| `static assert 4 == 4` | `core/_ParserDecls/enum_module_body.spl:1010-1043` routes `static` to `static fn`/`static me` or a module binding requiring `=` after its name. It has no static-assert declaration arm. | `core/_Ast/decl_nodes.spl` has no static-assert declaration tag; `flat_ast_bridge/module_assembly.spl:1198` emits `static_asserts: []`. The typed `StaticAssert` structure in `parser_types.spl:609+` is therefore unreachable from the core parser. Add a grammar node, flat encoding, bridge conversion, and compile-time evaluator/diagnostic. `@static_assert` intrinsic is a distinct syntax and does not satisfy this authored form. |

## Verification contract

Run the reviewed canonical SSpec with an admitted self-hosted compiler and record source commit, compiler commit, backend, mode, case count, failures, and log. A partial `ParserModule` is insufficient: each bridge parse must have zero `parser_has_errors()` first. The spec already asserts that. Only mark a gap fixed after its AST assertion passes and the relevant native compiler product is built and run. This report makes no claim that the four snippets have been executed in this triage.

## Scope note

`test/unit/compiler/native/baremetal_syntax_spec.spl` is a legacy mirror outside the canonical `test/01_unit` product root. Its old tautologies remain a separate migration task; they must not be imported as product evidence.
