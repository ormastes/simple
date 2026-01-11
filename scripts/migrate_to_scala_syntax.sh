#!/bin/bash
# Migration script: Explicit self -> Implicit self (Scala-style)
# Option 2a: var fn / val var syntax
#
# Transformations:
# 1. let -> val
# 2. let mut -> var
# 3. fn method(self, ...) -> fn method(...)
# 4. fn method(mut self, ...) -> var fn method(...)
# 5. fn constructor() -> static fn constructor() (when no self)

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}=== Simple Language Syntax Migration ===${NC}"
echo -e "${YELLOW}Migrating to Scala-style (val/var) syntax${NC}"
echo ""

# Find all .spl files
SPL_FILES=$(find . -name "*.spl" -type f ! -path "*/target/*" ! -path "*/.git/*")

if [ -z "$SPL_FILES" ]; then
    echo -e "${RED}No .spl files found${NC}"
    exit 1
fi

FILE_COUNT=$(echo "$SPL_FILES" | wc -l)
echo -e "${GREEN}Found $FILE_COUNT .spl files to migrate${NC}"
echo ""

# Create backup directory
BACKUP_DIR=".migration_backup_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$BACKUP_DIR"
echo -e "${GREEN}Created backup directory: $BACKUP_DIR${NC}"

# Counter for changes
TOTAL_CHANGES=0

# Process each file
for file in $SPL_FILES; do
    # Create backup
    backup_file="$BACKUP_DIR/${file#./}"
    mkdir -p "$(dirname "$backup_file")"
    cp "$file" "$backup_file"

    # Apply transformations using sed
    # Use a temporary file for atomic updates
    tmp_file="${file}.tmp"

    # Create sed script
    sed_script=$(cat <<'EOF'
# 1. Transform: let mut -> var (MUST come before let -> val)
s/\blet mut\b/var/g

# 2. Transform: let -> val
s/\blet\b/val/g

# 3. Transform method signatures (mut self -> var fn)
#    Match: fn method(mut self) -> ReturnType:
#    Replace: var fn method() -> ReturnType:
s/^\([[:space:]]*\)fn \([^(]*\)(mut self)$/\1var fn \2()/
s/^\([[:space:]]*\)fn \([^(]*\)(mut self,/\1var fn \2(/
s/^\([[:space:]]*\)fn \([^(]*\)(mut self, \([^)]*\))$/\1var fn \2(\3)/

# 4. Transform method signatures (self -> fn, remove self param)
#    Match: fn method(self) -> ReturnType:
#    Replace: fn method() -> ReturnType:
s/^\([[:space:]]*\)fn \([^(]*\)(self)$/\1fn \2()/
s/^\([[:space:]]*\)fn \([^(]*\)(self,/\1fn \2(/
s/^\([[:space:]]*\)fn \([^(]*\)(self, \([^)]*\))$/\1fn \2(\3)/

# 5. Add static to constructors/factory methods in impl blocks
#    This is tricky - we'll mark functions that DON'T have self
#    and are likely constructors (new, from_*, create_*, etc.)
#    This requires context awareness which sed can't do perfectly
#    So we'll do a simpler heuristic: if in impl and fn with no self/var
#    We'll handle this in a second pass or manually
EOF
)

    # Apply sed transformations
    sed "$sed_script" "$file" > "$tmp_file"

    # Count changes
    changes=$(diff -u "$file" "$tmp_file" | grep -c "^[-+]" || true)

    if [ "$changes" -gt 0 ]; then
        echo -e "${YELLOW}Migrating: $file${NC} (${changes} lines changed)"
        mv "$tmp_file" "$file"
        TOTAL_CHANGES=$((TOTAL_CHANGES + 1))
    else
        rm "$tmp_file"
    fi
done

echo ""
echo -e "${GREEN}=== Migration Complete ===${NC}"
echo -e "${GREEN}Files modified: $TOTAL_CHANGES / $FILE_COUNT${NC}"
echo -e "${GREEN}Backups saved to: $BACKUP_DIR${NC}"
echo ""
echo -e "${YELLOW}⚠️  Manual steps required:${NC}"
echo "1. Add 'static' keyword to constructor methods (new, from_*, etc.) in impl blocks"
echo "2. Review all changes carefully"
echo "3. Run tests: cargo test && make check"
echo "4. If tests pass, commit with: jj commit -m 'Migrate to Scala-style syntax (val/var)'"
echo ""
