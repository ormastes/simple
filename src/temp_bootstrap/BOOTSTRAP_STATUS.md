# Temporary Rust Bootstrap — Status Report

**Date:** 2026-02-24
**Goal:** Build a temporary Rust interpreter from `simple-effect` that can parse and interpret the Simple compiler source (646 `.spl` files), enabling self-hosted compilation.

## Bootstrap Chain

```
simple-effect Rust source
  → copied to src/temp_bootstrap/
  → cargo build --release  (16MB binary, ~44s)
  → temp bootstrap binary (interprets .spl)
  → interprets src/compiler/** (full compiler pipeline)
  → MIR C backend generates C++20
  → clang++ compiles C++20 + src/runtime/*.c
  → NEW native bin/release/simple
  → can compile itself (self-hosting achieved)
```

## Progress Summary

| Step | Status | Detail |
|------|--------|--------|
| 1. Copy & trim workspace | **DONE** | Removed gpu/simd/embedded/stub/tests; builds in ~44s |
| 2. Fix parser for Simple syntax | **IN PROGRESS** | 149/646 files parse (23%) |
| 3. Fix module resolution | Pending | Numbered directory prefix stripping |
| 4. Add rt_* FFI bridge | Pending | ~15 extern functions needed |
| 5. Fix interpreter patterns | Pending | Named constructors, optional chaining, etc. |
| 6. Test full pipeline | Pending | Interpret compiler, generate C++20 |
| 7. Compile & self-host | Pending | clang++ generated C++, verify self-hosting |

## Step 2: Parser Fix Detail

### Parse Success Rate: 149 / 646 (23%)

Starting from the `simple-effect` parser (which used different syntax conventions), we've already fixed many gaps. The parser now handles:

### Already Fixed (previous sessions)
- `val`/`var` declarations (mapped to Let/Var tokens)
- `me` mutable method keyword
- `pass_do_nothing`, `pass_dn`, `pass_todo`, `pass` keywords
- `:=` walrus operator
- `bitfield`, `alias`, `def` keywords
- Triple-quoted docstrings `"""..."""`
- `export NAME1, NAME2, ...` standalone exports
- `export path.*` wildcard re-exports
- `from X import {Y, Z}` / `from X import {*}` syntax
- Keywords as identifiers (~30+ keywords allowed in identifier positions)
- `static fn`, `me`, doc comments in class/struct/trait/impl bodies
- Named enum variant fields: `Custom(config: LexerConfig)`
- `<>` angle bracket generics: `Dict<text, SymbolEntry>`, `Result<T, E>`
- `?` optional type suffix: `i64?`, `Span?`, `Result<T, E>?`
- Range expressions: `0..10`, `0..=10`
- Inline `if`/`for`/`while` bodies: `if cond: return true`
- Empty block tolerance: `if cond:\n` (no indent = empty block)

### Remaining Errors (497 files failing)

| Count | Error | Root Cause | Fix Approach |
|-------|-------|------------|--------------|
| 72 | `expected Indent, found Newline` | Empty enum/struct/class/trait/impl bodies | `expect_block_start` returns bool; callers handle false. **Partially done** — `expect_block_start` modified but not all callers updated yet |
| 62 | `expected identifier, found Newline` | Multi-line expressions, trailing commas, continuation | Need to skip newlines in more identifier-expecting positions |
| 30 | `expected identifier, found Question` | `?` in wrong parse context (e.g., `self.field?` parsed wrongly) | Fix postfix `?` operator in expression parser |
| 22 | `expected identifier, found LBrace` | `from X import {Y}` still failing in some contexts; dict literals `{}` in type positions | Some `from` imports already fixed; need empty dict literal support |
| 18 | `expected identifier, found Dot` | Dotted paths in export/import contexts not fully handled | Extend path parsing |
| 16 | `expected expression, found Newline` | Multi-line expressions without continuation `\` | Need implicit line continuation inside brackets/parens |
| 15 | `expected expression, found RBrace` | Empty closures/dicts `{}` | Add empty dict/block support in primary expression |
| 12 | `expected Comma, found Colon` | Named arguments `Foo(name: value)` in call expressions | Parse `ident: expr` as named argument in call arg list |
| 12 | `expected identifier, found DoubleDot` | Range in for-loop `0..n` sometimes parsed incorrectly | Range parsing added but may not cover all positions |
| 12 | semantic: `ConstructCapsule` undefined | Correct parse, semantic resolution missing | Not a parser issue — needs interpreter/module support |
| 10 | `expected expression, found Else` | Inline ternary `if cond: a else: b` | Parse inline else after inline if body |
| 9 | `expected identifier, found Bool(true)` | `true`/`false` as identifiers | Add Bool to expect_identifier |
| 9 | `expected identifier, found Assign` | Default parameter values `fn foo(x = 5)` | Add default value parsing in parameters |
| 9 | `expected Comma, found As` | `as` type cast in argument lists | Add `as` infix cast operator |
| 7 | `expected pattern, found Case` | `case` keyword before match patterns | Skip `case` keyword in match arm parser |
| 4 | `Unterminated triple-quoted string` | Multi-line docstrings spanning many lines | Possible lexer bug with line counting in triple-quotes |
| 3 | `expected FatArrow, found Colon` | Match arms using `:` instead of `=>` | Already partially handled; need consistency |
| 3 | `expected Colon, found LParen` | Method calls where type annotation expected | Ambiguous parse context |
| Other | ~40 errors | Various: `Loop` in patterns, `Symbol("self")` in brackets, numbers as idents | Assorted edge cases |

### Files Modified (Step 2)

| File | Changes |
|------|---------|
| `src/parser/src/token.rs` | Added Var, Me, PassDoNothing, PassDn, PassTodo, Pass, Bitfield, Alias, Def, WalrusAssign tokens |
| `src/parser/src/lexer/identifiers.rs` | Added keyword mappings: val→Let, var→Var, me→Me, def→Fn, pass_*, bitfield, alias |
| `src/parser/src/lexer/mod.rs` | Added `:=` walrus, triple-quote `"""..."""` detection |
| `src/parser/src/lexer/strings.rs` | Added `scan_triple_quoted_string()` for docstrings |
| `src/parser/src/parser.rs` | Added `parse_block_or_inline()`, `from` import dispatch, function body uses inline blocks |
| `src/parser/src/parser_types.rs` | Added `<>` generic args alongside `[]`, `?` optional on all type forms |
| `src/parser/src/statements/mod.rs` | Added `parse_from_import()`, `parse_var()`, `parse_me_method()`, `parse_bitfield()`, `parse_alias()`, updated export/match/if/for/while to use inline blocks |
| `src/parser/src/expressions/mod.rs` | Added range `..`/`..=` parsing, walrus `:=` handling |
| `src/parser/src/expressions/primary.rs` | Added keyword-as-expression for many tokens |
| `src/parser/src/types_def/mod.rs` | Updated `expect_block_start` to return bool (partial), body parsers handle empty blocks (partial), named enum fields, keyword handling in bodies |
| `src/driver/src/main.rs` | Fixed `-c` mode to detect `val`/`var` |

### Recommended Fix Order (for next session)

**Priority 1 — High impact (covers ~200 errors):**
1. Complete `expect_block_start` callers update in types_def/mod.rs (72 errors)
2. Fix `expected identifier, found Newline` — skip newlines in identifier positions (62 errors)
3. Fix `?` postfix operator in expressions (30 errors)

**Priority 2 — Medium impact (covers ~100 errors):**
4. Named arguments `Foo(name: value)` in call argument parsing (12 errors)
5. `as` type cast operator (9+2 = 11 errors)
6. `case` keyword before match patterns (7 errors)
7. Empty dict/block `{}` in expression context (15 errors)
8. Inline else `if cond: a else: b` (10 errors)

**Priority 3 — Low impact (covers ~80 errors):**
9. Default parameter values (9 errors)
10. `true`/`false` as identifiers (9 errors)
11. Various edge cases (~40 errors)
12. Semantic errors are not parser issues (16 errors — skip)

### Agent Strategy Note

Parallel agents editing different parser files caused conflicts because the parser files are highly interrelated (e.g., `types_def/mod.rs` calls methods from `parser.rs`, `statements/mod.rs` shares patterns with `expressions/mod.rs`).

**Recommended approach:** Use a single agent (or sequential agents) that can build and test after each change. Alternatively, use worktree isolation per agent, then merge results manually.

## Build & Test Commands

```bash
# Build bootstrap binary
cd src/temp_bootstrap && cargo build --release -p simple-driver

# Test single file parsing
src/temp_bootstrap/target/release/simple src/compiler/00.common/di.spl

# Run comprehensive parse test
SUCCESS=0; FAIL=0
for f in $(find src/compiler -name "*.spl" | sort); do
  result=$(src/temp_bootstrap/target/release/simple "$f" 2>&1)
  if [ $? -eq 0 ]; then SUCCESS=$((SUCCESS+1))
  else FAIL=$((FAIL+1)); fi
done
echo "Success: $SUCCESS / 646"

# Error breakdown
# (save errors to file, then sort | uniq -c | sort -rn)
```

## Critical Files Reference

| File | Role |
|------|------|
| `src/temp_bootstrap/src/parser/src/lexer/identifiers.rs` | Keyword recognition |
| `src/temp_bootstrap/src/parser/src/parser.rs` | Main parser, block parsing, item dispatch |
| `src/temp_bootstrap/src/parser/src/parser_types.rs` | Type parsing (generics, optional, function types) |
| `src/temp_bootstrap/src/parser/src/types_def/mod.rs` | Struct/class/enum/trait/impl body parsing |
| `src/temp_bootstrap/src/parser/src/statements/mod.rs` | Statement parsing (if/for/while/match/export/import) |
| `src/temp_bootstrap/src/parser/src/expressions/mod.rs` | Expression precedence chain, operators |
| `src/temp_bootstrap/src/parser/src/expressions/primary.rs` | Literal/identifier/keyword primary expressions |
| `src/temp_bootstrap/src/parser/src/ast/nodes.rs` | AST node definitions |
| `src/temp_bootstrap/src/driver/src/main.rs` | CLI entry point |
