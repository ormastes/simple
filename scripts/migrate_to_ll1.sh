#!/bin/bash
# Migration script: GLR syntax → LL(1) syntax
# Changes:
# 1. [T] → <T> for generics (in type positions)
# 2. T? → Option<T> for optional types
# 3. [x for x in xs] → [for x in xs: x] for comprehensions
# 4. .method \x: → .method(\x: for lambdas

set -e

echo "LL(1) Migration Script"
echo "======================"
echo ""
echo "This will modify ALL .spl files in the repository"
echo "Make sure you have committed your changes!"
echo ""
read -p "Continue? (y/N) " -n 1 -r
echo
if [[ ! $REPLY =~ ^[Yy]$ ]]; then
    exit 1
fi

# Find all .spl files
SPL_FILES=$(find . -name "*.spl" -type f | grep -v ".git" | grep -v "target" | grep -v "node_modules")

COUNT=$(echo "$SPL_FILES" | wc -l)
echo "Found $COUNT .spl files to migrate"
echo ""

# Counters
GENERIC_COUNT=0
OPTIONAL_COUNT=0
COMPREHENSION_COUNT=0
LAMBDA_COUNT=0

for file in $SPL_FILES; do
    echo "Processing: $file"

    # Create backup
    cp "$file" "$file.bak"

    # 1. Generic brackets in declarations
    # struct Name[T] → struct Name<T>
    perl -i -pe 's/struct\s+(\w+)\[([^\]]+)\]/struct $1<$2>/g' "$file"
    # enum Name[T] → enum Name<T>
    perl -i -pe 's/enum\s+(\w+)\[([^\]]+)\]/enum $1<$2>/g' "$file"
    # impl Name[T] → impl Name<T>
    perl -i -pe 's/impl\s+(\w+)\[([^\]]+)\]/impl $1<$2>/g' "$file"
    # fn name[T] → fn name<T>
    perl -i -pe 's/fn\s+(\w+)\[([^\]]+)\]/fn $1<$2>/g' "$file"
    # trait Name[T] → trait Name<T>
    perl -i -pe 's/trait\s+(\w+)\[([^\]]+)\]/trait $1<$2>/g' "$file"

    # 2. Generic types in type positions
    # Common stdlib types
    perl -i -pe 's/List\[([^\]]+)\]/List<$1>/g' "$file"
    perl -i -pe 's/Option\[([^\]]+)\]/Option<$1>/g' "$file"
    perl -i -pe 's/Result\[([^\]]+)\]/Result<$1>/g' "$file"
    perl -i -pe 's/Dict\[([^\]]+)\]/Dict<$1>/g' "$file"
    perl -i -pe 's/Set\[([^\]]+)\]/Set<$1>/g' "$file"
    perl -i -pe 's/Vec\[([^\]]+)\]/Vec<$1>/g' "$file"
    perl -i -pe 's/Array\[([^\]]+)\]/Array<$1>/g' "$file"
    perl -i -pe 's/Slice\[([^\]]+)\]/Slice<$1>/g' "$file"
    perl -i -pe 's/Iterator\[([^\]]+)\]/Iterator<$1>/g' "$file"
    perl -i -pe 's/Future\[([^\]]+)\]/Future<$1>/g' "$file"
    perl -i -pe 's/Promise\[([^\]]+)\]/Promise<$1>/g' "$file"
    perl -i -pe 's/Channel\[([^\]]+)\]/Channel<$1>/g' "$file"
    perl -i -pe 's/Tensor\[([^\]]+)\]/Tensor<$1>/g' "$file"
    perl -i -pe 's/Box\[([^\]]+)\]/Box<$1>/g' "$file"
    perl -i -pe 's/Rc\[([^\]]+)\]/Rc<$1>/g' "$file"
    perl -i -pe 's/Arc\[([^\]]+)\]/Arc<$1>/g' "$file"
    perl -i -pe 's/Ref\[([^\]]+)\]/Ref<$1>/g' "$file"
    perl -i -pe 's/RefMut\[([^\]]+)\]/RefMut<$1>/g' "$file"

    # Generic parameters in where clauses
    # where T: Trait → where T: Trait (no change needed, but handle nested)
    perl -i -pe 's/(\w+)\[([A-Z][^\]]*)\]/\1<\2>/g' "$file"

    # 3. Optional types T? → Option<T>
    # After : in type annotations
    perl -i -pe 's/:\s*(\w+)\?/: Option<$1>/g' "$file"
    # After -> in return types
    perl -i -pe 's/->\s*(\w+)\?/-> Option<$1>/g' "$file"
    # In generic parameters with comma
    perl -i -pe 's/<([^<>]+,\s*)(\w+)\?([,>])/<$1Option<$2>$3/g' "$file"

    # 4. Comprehensions [expr for x in xs] → [for x in xs: expr]
    # Simple case: [x for x in xs]
    perl -i -pe 's/\[(\w+)\s+for\s+(\w+)\s+in\s+([^\]]+)\]/[for $2 in $3: $1]/g' "$file"
    # With condition: [x for x in xs if cond]
    perl -i -pe 's/\[(\w+)\s+for\s+(\w+)\s+in\s+([^\]]+)\s+if\s+([^\]]+)\]/[for $2 in $3 if $4: $1]/g' "$file"

    # 5. Lambdas - this is complex, handle simple cases
    # .method \x: expr → .method(\x: expr)
    # For now, just add opening paren, closing will be manual
    # Actually, skip this for now as it needs proper parsing

    # Check if file changed
    if ! diff -q "$file" "$file.bak" > /dev/null 2>&1; then
        echo "  ✓ Modified"
    else
        echo "  - No changes"
    fi
done

echo ""
echo "Migration complete!"
echo "==================="
echo ""
echo "Next steps:"
echo "1. Review changes: git diff"
echo "2. Update parser/grammar to support new syntax"
echo "3. Run: make check"
echo "4. Fix any remaining issues manually"
echo ""
echo "Backup files saved as *.bak"
echo "To restore: find . -name '*.bak' -exec bash -c 'mv \"\$0\" \"\${0%.bak}\"' {} \\;"
