# Inline-assembly colon form drops operand contracts

## Status

Open compiler-language defect, found during the privileged CPU SFFI removal.

## Evidence

Both compiler parsers accept `asm volatile:` as a legacy instruction-string
block. Neither parser consumes following `in`, `out`, `inout`, `lateout`,
`clobber`, or `options` directives in that form. Several target modules use
exactly that spelling, so their operand contracts can be rejected or omitted
instead of reaching MIR/codegen.

The parenthesized form does parse named operands and clobbers, but both parsers
also diagnose that form as legacy while recommending braced syntax; braced
syntax currently carries only raw instruction text and cannot express operand
contracts. There is therefore no non-legacy documented spelling with the full
contract surface.

## Required fix

Define one canonical operand-bearing grammar, implement it identically in the
Rust seed and self-hosted parsers, retain names/kinds/register classes/clobbers/
options through AST, HIR, MIR, and every backend, then migrate the remaining
colon and parenthesized users. Add negative tests proving an unresolved
placeholder or discarded directive is a hard error, never a skipped/no-op asm
block.

## Performance and safety

The grammar fix must be compile-time only. It must not add runtime wrapper
calls, allocation, lookup, dispatch, or instruction count. Memory clobbers must
remain compiler barriers without emitting additional hardware instructions.
