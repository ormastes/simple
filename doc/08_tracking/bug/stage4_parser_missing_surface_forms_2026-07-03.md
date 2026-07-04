# Stage4 parser/CoreLexer: missing grammar surface forms (stage4 parse blockers)

- **Status:** fixed
- **Date:** 2026-07-03
- **Components:** `src/compiler/10.frontend/core/` — `lexer_struct.spl`,
  `tokens.spl`, `parser_stmts.spl`, `parser_expr.spl`, `parser_decls_use.spl`,
  `_ParserDecls/enum_module_body.spl`, `_ParserPrimary/primary_expr.spl`

Each item below is a distinct root cause found while driving the 245-file
stage4 parse surface to zero `[parser_error]` lines. All are fixed; minimal
repro inline per item.

## 1. `for _ in xs:` rejected (parser_stmts.spl `parse_for_stmt`)

```simple
for _ in values:
    n = n + 1
```
`expected Ident, got _`. The tuple-destructure branch accepted `_` (169) but
the plain-binding branch only accepted Ident (6). Fixed by accepting 169.

## 2. Trailing `=` line continuation missing (lexer_struct.spl G27 lists)

```simple
val body =
    "a=" + x + "\n"
```
`unexpected token in expression: Newline`. The G27 trailing-binop
newline/indent suppression lists lacked `=` (kind 100). Added.

## 3. `impl Trait for Type:` unsupported (parser_decls_use.spl)

```simple
impl Backend for SdnBackendImpl:
    fn name() -> text: "sdn"
```
`expected :, got for`. `parse_impl_decl` now accepts the `for` (45) form and
attaches methods to the concrete type (trait conformance unchecked at stage4).

## 4. Keyword method names rejected (parser_decls_use.spl `parse_class_body_method`)

```simple
impl C:
    me bind(name: text): pass
    static fn var(id: i64): pass
```
`expected Ident, got bind`. Method-name position now accepts any keyword via
the `use_kw_segment_text` round-trip (G25 parity), not just `new`.

## 5. `not in` unsupported + kind-57 collision (parser_expr.spl)

```simple
if dir_path not in dir_files:
```
Kind 57 is shared by postfix `!` force-unwrap and textual `not`; the postfix
loop consumed `not` as `!`. Postfix 57 handlers now require text `"!"`, and
`parse_comparison` handles `a in b` → `b.contains(a)` and `a not in b` →
`not b.contains(a)`. (Also fixed the pre-existing `in` arm in
`parse_binary_from`, which dropped the left operand: `contains` got no args.)

## 6. `extern fn` inside a function body (parser_stmts.spl)

```simple
fn f(p: text) -> i64:
    extern fn rt_file_size(path: text) -> i64
    rt_file_size(p)
```
`expected :, got Newline`. Statement-level `extern fn` now registers the
signature via `decl_extern_fn` and emits a no-op statement
(`parse_extern_fn_stmt_inline`, mirroring `parse_use_stmt_inline` to avoid a
module cycle).

## 7. Leading `.` / `|` continuation lines (lexer_struct.spl)

```simple
val item = X.new(a)
    .with_visibility(v).with_signature(s)

case IntLit(_, _) | StringLit(_, _)
   | BoolLit(_) | NilLit:
```
`unexpected token in expression: Indent`. A line whose first non-blank char
is `.` or `|` is now a continuation: the newline and Indent/Dedent are
suppressed (both in the newline branch lookahead and in
`handle_indentation`).

## 8. Module-level `me` declarations (enum_module_body.spl)

```simple
me outline_parse(self: TreeSitter) -> [Item]:
    ...
```
`unexpected token in expression: ->`. Top-level `me` now routes to
`parse_fn_decl` (parity with the Rust parser, which routes top-level
`TokenKind::Me` to parse_function).

## 9. `asm` as a plain identifier (primary_expr.spl)

```simple
for constraint in asm.constraints:
```
`expected string literal, ':' block, or '{...}' after 'asm'`. `asm` followed
by `.` (164) is now parsed as `expr_ident("asm")` so the postfix layer takes
the field access.

## 10. `xor` keyword unmapped (tokens.spl `keyword_lookup`)

```simple
result = l xor r
```
`xor` lexed as a plain Ident and derailed the statement. Mapped to
`TOK_CARET` (122), matching the Rust lexer (`"xor" => TokenKind::Xor`).

## 11. Brace-form if expression (parser_stmts.spl `parse_if_expr`)

```simple
val n = if s.starts_with("import ") { 7 } else { 4 }
```
`expected :, got {`. `parse_if_expr` now accepts `if cond { X } else { Y }`
(and `else if` chaining) in expression position.

## 12. `not in` misfired without lookahead (parser_expr.spl)

```simple
assert not pure_eff.is_async()
```
`expected in, got Ident 'pure_eff'` (src/compiler/common/effects.spl:342).
The first `a not in b` implementation treated ANY textual `not` after an
operand as the start of `not in` — but `assert` parses as a plain ident in
this parser, so `assert not x` hit the branch. Both `not in` sites
(parse_comparison, parse_binary_from) now snapshot
(lex_snapshot_save/parser_tok_save), advance past `not`, and backtrack +
break unless the next token is `in` (kind 50).

## 13. `&:method` sigil never lexed (lexer_struct.spl)

```simple
val parts = elems.map(&:to_text)
```
`unexpected token in expression: & '&'` (semantics/const_eval.spl:60). The
parser already had the AmpColon (210) method-reference handler, but the
CoreLexer only emitted `&&` (55) or `&` (120). `&` + `:` now emits 210.

## 14. Suffixed hex literal rejected (lexer_struct.spl + primary_expr.spl)

```simple
0x10000000u64
```
First `expected ), got Ident 'u64'` (hex lexer didn't consume suffixes),
then `malformed integer literal token text '0x10000000'` (the suffixed-int
kind-7 branch only parsed decimal). Hex lexing now mirrors the decimal
suffix path, and the 0x/0b/0o + decimal text->value logic is extracted to
`parse_int_literal_text`, shared by kind 1 and kind 7.

## 15. Sized array type `[T; N]` (parser.spl `parser_parse_type`)

```simple
bytes: [u8; 4096]
```
`expected ], got ; ';'` (os/kernel/arch/arch_context.spl:352). The array
type branch now accepts `; N` (size expression skipped — stage4 arrays are
dynamic).

## 16. `assert cond, "msg"` message tail (parser_stmts.spl)

```simple
case _: assert false, "Expected Int type"
```
`expected :, got ,` (types/bidirectional_checking.spl:23, 120-error
cascade). `assert` lexes as a plain Ident; parse_statement now consumes
`assert <expr> [, <expr>]`, keeping the condition as an expression
statement and dropping the message.

## 17. `me` method at statement position (parser_stmts.spl)

```simple
fn create_method_resolver(...) -> MethodResolver:
    MethodResolver(...)

    me resolve_module(module: HirModule) -> HirModule:
```
semantics/resolve.spl writes methods at fn-body indent after a top-level
constructor fn; under pure-indentation parsing they land in statement
position. `me NAME(...)` there now desugars like the named nested fn:
`val NAME = fn(...): body`.

### 17a. Refinement: `me` self-alias expressions

The first version of item 17 consumed ANY statement-leading `me` (kind 34),
breaking `me.backend.move_cursor(...)`-style self-alias expressions
(office/undo.spl, office/file_ops.spl, editor/unified/vscode_adapter.spl —
regression caught by the pristine-HEAD baseline diff). The handler now
snapshots (lex_snapshot_save/parser_tok_save), takes the method-decl path
only when an identifier follows `me`, and otherwise backtracks so the
expression path parses the self-alias.
