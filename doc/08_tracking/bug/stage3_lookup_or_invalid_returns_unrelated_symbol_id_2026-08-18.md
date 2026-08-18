# Stage 3: `lookup_or_invalid(name)` returns the id of an UNRELATED symbol (2026-08-18)

Status: OPEN (P1) — root cause of the Stage 3 `enum payload dependency` fatal
flood. Containment landed separately; this defect is NOT fixed.

## Symptom

Stage 3 self-host (`native-build` of `src/app/cli/bootstrap_main.spl`) emits
fatal HIR lowering errors of the form

```
enum payload dependency `TokenKind` resolved to non-type binding `asm_arm_backend`
  (kind `const`) in `compiler.frontend.core._AstExpr.nodes`;
  expected the type `compiler.frontend.lexer_types::TokenKind::enum`
```

and produces **no binary**. Loci in
`/mnt/data/worktrees/simple-boot-snap/build/bootstrap/logs/x86_64-unknown-linux-gnu/stage3-native-build.log`
(630,109 bytes, mtime 2026-08-17 13:42): `source_idx=252 io_passes.spl count=27`,
`source_idx=256 outline_lexer.spl count=8`,
`source_idx=257 outline_types.spl count=7`.

## Root cause, isolated to the resolver (not the fetch)

`claim_materialized_payload_binding`
(`src/compiler/20.hir/hir_lowering/_Items/module_lowering.spl`) calls
`self.symbols.lookup_or_invalid(local_name)` with a bare payload TYPE spelling,
then reads `self.symbols.symbols[id]`. The record that comes back describes a
completely different, real symbol.

A long-standing comment there offered two candidate layers — (a) a resolver
defect returning an id for a different name, or (b) a native-codegen
`Dict<i64, HirSymbol>` bracket-read returning a foreign record — and added the
`SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1` probe to discriminate them. **The log
discriminates them on its own, and the answer is (a).**

Every symbol Stage 3 named is a real declaration, and the `defining_module` it
reported is the module that actually declares it:

| payload claimed | reported binding | kind | reported owner | actual declaration |
|---|---|---|---|---|
| `TokenKind` | `asm_arm_backend` | const | `compiler.frontend.core._AstExpr.nodes` | exported, `src/compiler/10.frontend/core/__init__.spl:208` |
| `TypeOutlineKind` | `stmt_tag` | const | `compiler.10.frontend.core.ast_stmt` | `var`, `src/compiler/10.frontend/core/ast_stmt.spl:44` — exact |
| `VariantPayload` | `STMT_CONTRACT_DECREASES` | const | `compiler.10.frontend.core.ast_stmt` | `const`, `src/compiler/10.frontend/core/ast_stmt.spl:40` — exact |
| `Visibility` (idx 256) | `ast_module_decl_count_slot` | const | `compiler.frontend.core._Ast.decl_nodes` | `var`, `src/compiler/10.frontend/core/_Ast/decl_nodes.spl:77` — exact |
| `Visibility` (idx 257) | `...outline.toplevelitem_Impl` | callable | `compiler.frontend.treesitter.outline` | `fn`, `src/compiler/10.frontend/treesitter/outline.spl:41` — exact |

A corrupt bracket read does not produce five records whose name, kind, AND
defining_module each independently agree with a real declaration in exactly that
file. **The fetch is faithful; the id is wrong.**

## Two signals about the shape of the defect

- **The same payload name resolves to different symbols as the build
  progresses.** `Visibility` hits `ast_module_decl_count_slot` at source_idx 256
  and `toplevelitem_Impl` at 257. A name collision would be stable across
  sources; a drifting id is not. This points at the id space, not at naming.
- **Every wrong binding is a bootstrap-globals-family symbol** — a module-level
  `var`, a module-level `const`, or a free `fn`, all under
  `src/compiler/10.frontend/core/**` or `src/compiler/10.frontend/treesitter/**`.
  Nothing in the sample is a type, a method, or a class member.

Together these suggest an id-assignment / id-space defect in the flat bootstrap
symbol namespace (`SIMPLE_BOOTSTRAP=1`, `--entry-closure`), where module-level
globals are accumulated across modules. That is a hypothesis, **not measured**.

## What is NOT the cause

The `register_imported_type_methods` re-entrancy breaker
(`stage3_register_imported_type_methods_infinite_recursion_2026-08-17.md`) was
suspected of trading the SIGSEGV for wrong bindings. **Refuted.** That method's
inner body defines exactly one kind of symbol,
`"{owner_module}.{Type}::{method}"`. None of the five wrong bindings is such a
symbol — three are module-level `var`/`const`, one is a free `fn`. No decision
the breaker makes in either direction can make `TokenKind` resolve to a `const`
in `ast_stmt.spl`.

## Containment already landed (does not fix this)

`hir_payload_binding_names_agree` gates both ownership contests in
`claim_materialized_payload_binding` on positive name agreement, so a wrong id
no longer becomes a hard fatal that fails the module. The mismatch stays visible
under `SIMPLE_HIR_PAYLOAD_LOOKUP_TRACE=1`. Guard:
`scripts/check/check-hir-payload-binding-contest-guarded.shs`. Spec:
`test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl`.

Containment is not a fix: any other consumer of `lookup_or_invalid` in the
bootstrap symbol table is still exposed to the same wrong id, silently.

## Unblock condition

Locate why `lookup_or_invalid` returns a foreign id under the flat bootstrap
namespace. Cheapest reproduction target identified so far is
`src/compiler/10.frontend/treesitter/outline_types.spl` (source_idx 257, 7
fatals) rather than a full ~25-minute Stage 3 run — this has NOT yet been
attempted in isolation.

## Unproven

- That removing these fatals is sufficient for Stage 3 to admit. No bootstrap
  was run in the session that filed this.
- The id-space hypothesis above.
- Whether the same wrong-id defect affects non-bootstrap compiles.

## Landing record — pre-existing test-tree divergence stepped over

`check-test-tree-divergence-delta.shs` on the exact landed range
(`62f7ad741d8..a04448f02e8`):

```
base verdict: FAIL — 875 diverged vs 812 baselined (64 new, 1 fixed-but-still-baselined);
              8 mirror-only (6 unallowlisted, 0 stale-allowlist)
PASS — 71 pre-existing offender(s), 0 introduced by this range      (rc 0)
"pre-existing red is identical at BASE and NEW; this range introduces nothing"
```

The pre-existing red is another lane's and is NOT this change's to fix; it is
recorded here because landing on a delta-PASS requires it. Full offender list as
saved by the helper: `/mnt/data/tmp/test_tree_divergence_preexisting.txt`
(875 lines; first entries `integration:app/app_mcp_intensive_spec.spl`,
`integration:app/check_log_modes_spec.spl`,
`integration:app/cli_log_modes_spec.spl`).

Independently of the measurement, this range's delta is zero **by construction**:
`check-test-tree-divergence.shs` enumerates the SHADOW tree only
(`shadow_files.txt`, lines 242/268) and classifies each shadow file. This
range's sole test-tree change is an ADD in the CANONICAL tree
(`test/01_unit/compiler/hir/payload_binding_contest_names_agree_source_spec.spl`)
with no shadow counterpart, so it is never enumerated and cannot enter
`mirror_only`, `current_diverged`, or `total_common`.

## Verification status of the edited compiler file — UNVERIFIED, with a control

`bin/simple check` on `module_lowering.spl` returned rc 255 with **no error
text**; the log's last content line is `[TIMEOUT: Process killed after 300s]`.
Per the repo convention a timeout with no result line is UNVERIFIED — neither a
pass nor a fail.

Control: `bin/simple check` on origin's UNMODIFIED copy of the same file
(`git show <origin>:<path>`) timed out identically — 300s, rc 255. So the
timeout is a pre-existing property of `check` on this ~3,000-line file on this
host (load average 80-95 during the run), **not** an effect of this change. The
two arms are indistinguishable, so the edit is not implicated; it also means
compile-level verification of this file was not achieved either way.
