# Rust seed parses `friend <pkg>` as a call, 21 interpreted caret specs ERROR

Status: verification-pending

`8157ad736a0` added module-level `friend lib.x.y` directives to four lib files
(`distributed_operation_journal_v2.spl`, `distributed_operation_owner_health_v2.spl`,
`linux_protected_root_reader_v1.spl`, `linux_protected_storage_v1.spl`). The pure-Simple
frontend handles them; the Rust seed parsed the line as `friend(lib.x.y)` and the
interpreter aborted with `E1002 function friend not found`, so 21 of 48 caret specs
ended `outcome=ERROR executed=0` under the seed.

Fix: seed parser consumes `friend <ident>...` as a no-op (`parser_impl/core.rs`).
Test: `src/compiler_rust/parser/src/friend_module_decl_test.rs` (RED: dump contained
the `friend` call; GREEN: 3 passed). Needs a seed rebuild to re-run the 21 specs.
