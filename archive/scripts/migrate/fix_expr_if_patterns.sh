#!/bin/bash
# Fix all Expr::If pattern matches to include .. for let_pattern field

files=(
    "src/compiler/src/codegen/lean/expressions.rs"
    "src/compiler/src/compilability.rs"
    "src/compiler/src/hir/lower/expr/inference.rs"
    "src/compiler/src/hir/lower/expr/mod.rs"
    "src/compiler/src/interpreter/expr/control.rs"
    "src/compiler/src/macro/hygiene.rs"
    "src/compiler/src/macro/invocation.rs"
    "src/compiler/src/macro/substitution.rs"
    "src/compiler/src/monomorphize/analyzer.rs"
    "src/compiler/src/monomorphize/binding_specializer.rs"
    "src/compiler/src/monomorphize/engine.rs"
    "src/compiler/src/monomorphize/rewriter.rs"
    "src/compiler/src/symbol_analyzer.rs"
)

for file in "${files[@]}"; do
    echo "Fixing $file"
    # Use perl for multi-line replacement
    perl -i -0pe 's/(Expr::If \{[^\}]*?else_branch,?)(\s*\})/\1\n                ..\2/gs' "$file"
done

echo "Done!"
