# `text as bool` native lowering differs from the seed

- **Status:** open (pre-existing, not changed by the text-cast rework)

Seed interpreter (`interpreter/expr/casting.rs`, `bool_cast::from_str`):
`"a" as bool` is true, `"" as bool` is false. The LLVM lane lowers a text
operand cast to bool as a pointer null test (`icmp ne ptr, null`), so an
EMPTY text is true natively. The text->int/float forms were given
seed-parity lowering in `lower_cast_or_convert`
(`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl`); bool was left
because `from_str`'s full rule set has not been mirrored in a runtime entry.
