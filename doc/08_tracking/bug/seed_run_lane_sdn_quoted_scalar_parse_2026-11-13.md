# Seed `run` lane: SDN parser rejects a file that parses under `test` (2026-11-13)

**Binary:** `/home/yoon/dev/simple/src/compiler_rust/target/bootstrap/simple` (Rust seed, 119570696 bytes, 2026-11-05 18:12), worktree `simple-nodestore-20261113` at `4376da2db83`.

**Symptom.** `simple run src/app/compiler_schema/main.spl node_views` fails with
`node_views: schema: SDN parse error: unterminated quoted scalar at sdn:config/data_policy/compiler_ast_binary_expr.sdn:0`,
and `std.common.sdn.parser.parse` on the same text (file-read or inline literal) returns
`Err("unterminated quoted scalar")`. The identical call inside a spec run with `simple test`
(`ast_node_pool_pilot_spec`, `node_view_generate_text(file_read(NODE_VIEW_SCHEMA_PATH))`) succeeds.
The pre-change schema (`git show 4376da2db83:config/data_policy/compiler_ast_binary_expr.sdn`) fails
the same way, so this is not caused by the storage-rule rows.

**Narrowing (all under `run`):** the first failing prefix of the non-comment text is five lines
(`data_policy:` / `schema: "simple.data-policy/v1"` / `declarations:` / `binary_expr:` /
`tree: "compiler.ast"`) with `trailing content after quoted scalar`; the same five lines with the
root key renamed to `a:` parse; each of `data_policy:` + one quoted child, a depth-4 quoted scalar,
and quoted values up to 26 bytes parse on their own; no single-line removal from the full
document makes it parse. Every `run` invocation prints
`[engine-demotion] reason=hybrid-interp-splice detail=rt_text_...`, so the suspect is a natively
spliced text runtime function used by the parser's quoted-scalar scan, not the parser source.

**Impact.** `scripts/check/check-node-view-gen-fresh.shs` (advisory row `push-node-view-gen-fresh`)
cannot regenerate on this seed. Workaround used: a scratch spec calling
`node_view_generate_into(".")` under `simple test` (byte-identical output is then pinned by the
pilot spec's determinism example).

**Repro:** `simple run <probe>.spl` where the probe parses the committed schema text; compare with
the pilot spec. Not fixed here (outside the node-storage lane).
