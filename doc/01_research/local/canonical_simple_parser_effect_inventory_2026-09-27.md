# Canonical Simple parser effect inventory: checkpoint and lexer control

**Status:** source inventory for the grammar/action provider designed in
`doc/05_design/compiler/canonical_scalar_simple_grammar_action_provider_2026-09-27.md`
(draft PR #1706). This records one required part of task 2 in that design. It
does not qualify a canonical scalar provider or assign program opcodes.

**Source baseline:** `origin/main` at `15d989519be3d4b9b9aeaa3eb627b6bff874110b`.
The source paths below are relative to `src/compiler/10.frontend/core/`.

## Checkpoint state that must be preserved

`lexer.spl:775-880` defines `LexSnapshot`. Its numeric state contains source
byte position, line and column, pending dedents, line-start flag, parenthesis
depth, current token start, direct current token kind/line/column, core lexer
kind, and pending generic-close flag. It separately copies current token text,
suffix, and the indentation stack. Rollback transfers the saved indentation
stack into the live lexer and releases the replaced stack; commit releases the
saved stack. Both paths release the snapshot metadata. Token offsets are also
restored for span consumers.

`parser.spl:1190-1203` separately saves current parser token kind, text, line,
and column. Every site below pairs `lex_snapshot_save` with `parser_tok_save`;
rollback calls both lexer rollback and parser token restore. A candidate
checkpoint that saves only a token index, or only the lexer, is therefore not
semantically equivalent. It also needs explicit ownership of the saved
indentation stack so repeated speculation does not leak or double free it.

## All direct lexer checkpoint sites

The 18 `val ... = lex_snapshot_save()` calls in this baseline occur at these
locations. Each row names the containing function and the decision being
speculated on; line numbers are anchors for extraction, not stable rule IDs.

| File and line | Function | Speculative decision |
|---|---|---|
| `parser_expr.spl:349` | `parse_comparison` | textual `not` followed by `in` versus a separate expression token |
| `parser_expr.spl:609` | `parse_binary_from` | a second textual `not in` recognition path |
| `parser_expr.spl:722` | `parse_call_arg_raw` | named argument label versus positional expression |
| `parser_expr.spl:775` | `try_skip_ident_generic_args` | `ident <...>` generic argument list versus comparison `<` |
| `parser_stmts.spl:231` | `try_parse_bare_ident_string_call` | bare identifier followed by string-call sugar |
| `parser_stmts.spl:462` | `try_parse_contract_stmt` | contract statement recognition and recovery |
| `parser_stmts.spl:536` | `parse_unsafe_block_expr_if_present` | unsafe expression/block form |
| `parser_stmts.spl:697` | `parse_statement` | loop statement prefix |
| `parser_stmts.spl:902` | `parse_statement` | `with` statement prefix |
| `parser_stmts.spl:970` | `parse_statement` | `me` statement prefix |
| `parser_stmts.spl:1021` | `parse_statement` | walrus statement prefix |
| `parser_stmts.spl:1474` | `parse_for_binding_name` | contextual `mut` modifier versus a binding named `mut` |
| `_ParserDecls/fn_struct_decls.spl:106` | `parser_skip_mut_if_present` | optional `mut` parameter marker |
| `_ParserDecls/fn_struct_decls.spl:152` | `current_ident_followed_by_lbrace` | identifier followed by struct-literal brace |
| `_ParserDecls/fn_struct_decls.spl:463` | `parser_class_member_followed_by_colon` | class member colon lookahead |
| `_ParserDecls/fn_struct_decls.spl:477` | `parser_newline_starts_indented_block` | newline and indent lookahead |
| `_ParserDecls/fn_struct_decls.spl:491` | `parser_try_skip_signature_layout_before_colon` | signature layout before colon |
| `_ParserDecls/fn_struct_decls.spl:936` | `parse_struct_or_trait_decl` | `@layer_field` member attribute versus another decorator |

The four `parse_statement` sites are one function with four independent
checkpoints. In total, 15 functions own 18 direct saves. The count excludes
the `lex_snapshot_save` definition and imports. A future extraction needs an
explicit commit or rollback edge for each save, including early returns and
diagnostic recovery branches.

## Other lexer and parser effects that the program must express

| Effect | Source evidence | Required semantic contract |
|---|---|---|
| Parser-controlled indentation | `parser_stmts.spl:1705,1750,1768,1967`; `_ParserPrimary/primary_expr.spl:154-186,886-930` | Enable/disable forced indentation and pop indentation during block/match recovery, including exceptional exits. |
| Raw source repositioning | `_ParserDecls/fn_struct_decls.spl:226-240`; `_ParserPrimary/asm_raw_parsing.spl:109`; `lexer.spl:686` | Resume lexing at a chosen byte, line, and column after raw body parsing. A pretokenized immutable cursor alone cannot reproduce this. |
| Non-consuming diagnostic | `parser.spl:372-410` | `parser_expect` can record an error without consuming the unexpected token; recovery must retain this ordering. |
| Multiple block forms | `parser_stmts.spl:264-351` | Distinguish INDENT/DEDENT bodies, one-statement bodies, and same-column next-line bodies. |
| AST mutation | `parser_expr.spl:182-200` | Pipe/composition actions can update call arguments and synthesize lambda nodes, so action effects cannot be modelled as append-only emissions. |
| Interpolation subparse | `string_interpolation_expand.spl:101-125,161-213,274-295` | Temporarily replace lexer input and diagnostic/transform state, then restore outer state and preserve source mapping. |
| Placeholder transform | `../desugar/placeholder_lambda.spl:381-434` | Rewrite existing expression/arm-pattern nodes and arguments after parse. Include resulting AST in parity. |
| Declaration side effects | `_ParserDecls/enum_module_body.spl:1418-1600` | Decorators/attributes can mutate pending pools and synthesize declarations; rollback must not publish abandoned effects. |

## Extraction constraints and next gate

Before assigning bytecode opcodes, classify every grammar rule and semantic
action, not just the checkpoint sites above. In particular, identify token-kind
and spelling predicates, recovery loops, AST construction/update, declaration
insertion, source span conversion, diagnostics, and post-parse transforms. Give
each a stable table entry or an explicit unsupported reason. The validator must
reject unbounded loops and any rollback path that has already exposed an
unundoable effect. A private action/diagnostic journal per checkpoint is one
possible implementation; its semantics must be proven by differential tests
before candidate admission. The independent legacy oracle remains the parity
reference and the production provider remains unavailable until then.

## 2026-09-28 addendum — rollback edge versus AST publication

**Source baseline:** `origin/main` at `7ab226395c5cb637901f77350d9d32de395d4ba6`. This addendum preserves the earlier inventory rather than replacing it. The current parser still has 18 direct `lex_snapshot_save()` sites, but `parser_stmts.spl:105` now adds `parser_stmt_with_header_ahead`, and line anchors elsewhere have moved. This is a direct-site control-flow review; it does not prove effects in every indirect callee.

| Snapshot sites in current source | Decision and effect boundary |
|---|---|
| `_ParserDecls/fn_struct_decls.spl:106,152,463,477,491`; `parser_expr.spl:722,775`; `parser_stmts.spl:105,736,1526` | Ten token-shape probes. Rejected alternatives restore lexer and parser-token state before any direct AST construction, existing-node update, module insertion, or parser diagnostic. `try_skip_ident_generic_args` at `parser_expr.spl:775` only walks tokens; it reports the unsupported const-generic diagnostic after committing the recognized shape. |
| `parser_expr.spl:349,609`; `_ParserDecls/fn_struct_decls.spl:936` | Three successful alternatives parse expressions or emit `parser_expect`/`parser_error` while the snapshot is live. Each rejected branch rolls back **before** those effects; once effectful parsing starts, the branch commits without a later rollback. The `@layer_field` branch can report malformed syntax and still commit its recognized shape. |
| `parser_stmts.spl:270,501,575,1022,1073` | Five successful alternatives call `parse_expr`, `parse_block`, `parse_contract_clause_body`, or `parse_fn_lambda_after_kw` while the snapshot is live. The negative shape exits roll back first; the effectful path commits and does not backtrack afterward. `try_parse_contract_stmt` has multiple negative exits before body parsing. |

This commit-before-effects ordering is a property of these 18 handwritten probes, not a general grammar rule. A declarative `Choice` may enter an alternative that emits actions or diagnostics before it learns the branch fails. The canonical executor must keep those effects private until commit, or carry a bounded undo record that restores expression/statement/declaration arenas, module publication, spans, warnings, errors, and first-error state. Merely restoring the lexical cursor would leak abandoned syntax into the candidate result.

Independent direct mutation surfaces already visible outside the local probes include `expr_call_args_set` in `parser_expr.spl:663`, `expr_set_span` in `parser_expr.spl:245,257,267,279` and `parser_stmts.spl:479`, declaration metadata setters in `_ParserDecls/enum_module_body.spl:951-990`, and `module_add_decl` in the same module at `:959,978,992` plus its synthesized-declaration branches near `:1394-1505`. The action inventory must distinguish node allocation, existing-node rewrite, declaration metadata update, and module publication. A count of constructor calls alone would miss the latter three classes.

**Next implementation gate:** bind each direct and indirect AST write to a typed candidate action with a source span and a rollback/publication policy; then compare isolated semantic snapshots against the retained legacy oracle. This addendum assigns no opcode numbers and does not admit a canonical Simple provider.
