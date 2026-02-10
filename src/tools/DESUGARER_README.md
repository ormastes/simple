# Full Simple Desugarer - AST Transformer

This tool transforms Full Simple code into Core Simple compatible code.

## Quick Start

```bash
# Manual prototype already created:
cat src/compiler_core/lexer_desugared.spl

# To desugar all compiler files (TODO):
simple src/tools/desugarer.spl --input-dir src/compiler --output-dir src/compiler_core
```

## Transformation Passes

1. **impl Removal**: `impl Type:` → module functions
2. **Option Desugaring**: `T?` → `has_value: bool, value: T`
3. **Pattern Match**: `match` → if-else chains
4. **Closure Lifting**: `|x| x+1` → `fn closure_N(x)`
5. **Generic Mono**: `Option<T>` → `OptionI64`, `OptionText`
6. **Operator Desugar**: `?.`, `??` → explicit checks

## Status

- [x] Architecture designed
- [x] Manual prototype: `src/compiler_core/lexer_desugared.spl`
- [ ] Automated tool (TODO)

## See Also

- [DESUGARING_PLAN.md](../../DESUGARING_PLAN.md)
- [LEXER_DESUGARING_EXAMPLE.md](../../LEXER_DESUGARING_EXAMPLE.md)
- [CORE_FULL_COMPILATION_PLAN.md](../../CORE_FULL_COMPILATION_PLAN.md)
