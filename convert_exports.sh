#!/bin/bash
# Convert "export use module.*" to "export module.*"
# Note: This may cause parse errors - test before committing

echo "Converting export statements in tree-sitter files..."

find src/lib/std/src/parser/treesitter -name "*.spl" -exec sed -i \
  's/^export use /export /g' {} \;

echo "Done. Files modified:"
git diff --name-only src/lib/std/src/parser/treesitter/

echo ""
echo "Test with: ./target/debug/simple test_ts_runtime.spl"
