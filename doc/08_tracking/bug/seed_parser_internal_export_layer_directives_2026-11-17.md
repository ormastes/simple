# Rust seed parses `internal_export` / `layer` module directives as calls

Status: verification-pending

Follow-up to `seed_parser_friend_module_directive_2026-11-17.md`. After `friend`
was accepted, the same 21 caret specs still died with
`E1002 function 'internal_export' not found`: lib files such as
`linux_protected_root_reader_v1.spl` carry module-level `internal_export NAME`.

Census of module-level soft-keyword directives in the pure-Simple parser
(`src/compiler/10.frontend/core/_ParserDecls/enum_module_body.spl`) vs the seed
(`parser_impl/core.rs`, `items.rs`):

| directive | pure-Simple | seed |
|---|---|---|
| `friend PKG` | yes | yes (#9846) |
| `internal_export NAME` | yes | missing -> fixed here |
| `layer NAME [uses A, B]` | yes | missing -> fixed here |
| `resource`, `cli`, `unit`, `on`, `macro` | yes | already handled |

Fix: the seed's no-op directive arm now covers `friend`, `internal_export` and
`layer` (the seed has no visibility/layer graph; access control only). The word
stays an ordinary identifier unless an identifier follows.
Tests: `src/compiler_rust/parser/src/friend_module_decl_test.rs`
(`module_access_directives`; RED 2 failed, GREEN parser lib 469 passed).
