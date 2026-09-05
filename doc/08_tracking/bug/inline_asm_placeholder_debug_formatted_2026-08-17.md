# Inline-asm template placeholder was Debug-formatted into emitted assembly

- **Status:** FIXED (2026-08-17)
- **Severity:** blocking (bootstrap planner build emitted a hard assembler error)
- **Area:** compiler / parser / inline asm

## Symptom

The bootstrap planner build emitted exactly one error in ~90 KB of output:

```
error: <inline asm>:1:10: unknown token in expression
        ldr r0, =Identifier("stack_top")
                ^
```

Source template, `src/lib/nogc_async_mut_noalloc/baremetal/arm/startup.spl:70`:

```
"ldr r0, ={stack_top}"
```

Expected `ldr r0, =stack_top`. Non-placeholder lines (`=_sidata`, `=0xE000ED88`)
were fine, so the defect was specific to the `{name}` placeholder path.

## Root cause

`src/compiler_rust/parser/src/stmt_parsing/asm.rs`, in
`Parser::extract_asm_block_strings`. An `asm:` block line containing `{...}` is
parsed as an `Expr::FString`; each interpolated part was flattened with Rust's
`Debug` formatter:

```rust
FStringPart::Expr(e) => text.push_str(&format!("{:?}", e)),
FStringPart::ExprWithFormat(e, spec) => text.push_str(&format!("{:?}:{}", e, spec)),
```

So `Expr::Identifier("stack_top")` rendered as `Identifier("stack_top")`. Because
the whole `Expr` enum was Debug-formatted, EVERY variant was affected — integer
literals leaked as `Integer(0)` too (already observed in the riscv startup blocks;
`pipeline/native_project/inline_asm_emit.rs` carries a downstream *skip* workaround
that greps for the literal strings `Identifier(` / `Integer(`, which is why some
targets silently dropped instructions instead of erroring).

## Fix

New `render_asm_placeholder(&Expr) -> Option<String>` renders the operand shapes
that have an unambiguous assembler spelling — `Identifier` (bare name), `Path`
(`::`-joined), `Integer` / `TypedInteger`, `String`, `Bool` (`1`/`0`) — and
returns `None` for everything else. `extract_asm_block_strings` now returns
`Result<(), ParseError>` and raises a clear parse error naming the unsupported
operand instead of emitting an unparseable token. Failing loudly is acceptable;
emitting nonsense into the assembler is not.

## Regression tests

`parser/src/stmt_parsing/asm.rs` `mod tests`:
- `test_asm_template_placeholder_renders_bare_identifier` — asserts the emitted
  instruction contains `=stack_top` and does NOT contain `Identifier(`.
- `test_asm_template_placeholder_renders_integer_literal`
- `test_asm_template_placeholder_rejects_unsupported_operand` — a non-literal
  expression is a parse error, not silent garbage.

Negative control: with the `format!("{:?}", e)` restored, the first test fails on
the `Identifier(` assertion.

## Follow-up (not done here)

The `has_unresolved_simple_operand` skip-list in
`src/compiler_rust/compiler/src/pipeline/native_project/inline_asm_emit.rs` was
built around this defect. Now that placeholders render correctly, the
`Identifier(` / `Integer(` clauses there should be re-evaluated and probably
removed, so a future leak fails loudly rather than being silently skipped.
