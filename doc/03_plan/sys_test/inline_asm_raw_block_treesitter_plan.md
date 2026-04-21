# Inline Asm Raw Block Tree-sitter Plan

Date: 2026-04-21

## Goal

Make `asm { ... }` a true raw embedded assembly block across parser, Tree-sitter
tooling, tests, and docs. Raw asm payload must not require string quotes.

## Current Contract

- Canonical raw syntax: `asm { nop }`
- Volatile raw syntax: `asm volatile { wfi }`
- Compatibility syntax: `asm: "nop"` and `asm("...", operands...)`
- Parenthesized asm remains valid without warning while operand constraints use it.

## Implementation Tasks

1. Rust parser
   - Keep source-slice based braced asm parsing.
   - Preserve `#`, `%`, `$`, `{placeholder}`, commas, semicolons, and quoted compatibility lines.
   - Keep old `asm(...)` routed to asm parsing.

2. Pure Simple parser
   - Replace token-reconstructed `asm {}` parsing with source-slice raw capture.
   - Move lexer state directly after the matching closing brace.
   - Preserve line/column state for the token after the asm block.
   - Keep `asm:` and parenthesized compatibility behavior unchanged.

3. Tree-sitter outline
   - Add a dedicated `AsmOutline` or reuse `BlockOutline(kind: "asm")` with explicit
     `node_kind: "asm_block"` metadata.
   - Capture `asm_content` as raw text between braces.
   - Ensure `asm volatile { ... }` records volatility.
   - Add query coverage so `asm_content` injects `asm`.

4. Tests
   - Rust parser unit tests for x86, ARM, RISC-V, immediates, placeholders,
     comments, semicolon/comma terminators, empty blocks, and quoted compatibility.
   - Pure Simple parser unit tests for raw payload preservation.
   - Tree-sitter tests for `asm_block`, `asm_content`, volatility, and injection query.
   - SSpec matrix across `x86_32`, `x86_64`, `arm32`, `arm64`, `riscv32`,
     `riscv64` and interpreter/loader/compiler modes.

5. Docs
   - Make `asm { nop }` the first documented form.
   - Mark quoted braced lines as compatibility only.
   - Keep operand examples parenthesized until operand-bearing braced lowering lands.

## Acceptance

- No docs or active tests describe quoted braced asm as canonical.
- Raw asm payload with `#0` survives parser and Tree-sitter capture.
- Old parenthesized asm compiles/parses without warning.
- Targeted parser, Tree-sitter, and SSpec tests pass.
