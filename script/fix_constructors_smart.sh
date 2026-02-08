#!/bin/bash
# Smart Constructor Fixer
#
# Uses type database to convert ClassName.new(args) to ClassName(field: arg)

set -e

TYPE_DB="build/type_database.txt"
TARGET="${1:-.}"

if [ ! -f "$TYPE_DB" ]; then
    echo "Error: Type database not found. Run ./script/build_type_database.sh first"
    exit 1
fi

if [ ! -e "$TARGET" ]; then
    echo "Error: $TARGET not found"
    exit 1
fi

echo "=== Smart Constructor Fixer ==="
echo "Type database: $TYPE_DB"
echo "Target: $TARGET"
echo ""

# Load type database into associative array
declare -A TYPE_FIELDS

while IFS=: read -r type_name fields; do
    # If type already exists, keep the one with more fields
    if [ -n "${TYPE_FIELDS[$type_name]}" ]; then
        old_count=$(echo "${TYPE_FIELDS[$type_name]}" | tr ',' '\n' | wc -l)
        new_count=$(echo "$fields" | tr ',' '\n' | wc -l)
        if [ $new_count -gt $old_count ]; then
            TYPE_FIELDS[$type_name]="$fields"
        fi
    else
        TYPE_FIELDS[$type_name]="$fields"
    fi
done < "$TYPE_DB"

echo "Loaded ${#TYPE_FIELDS[@]} type definitions"
echo ""

# Find all .spl files
if [ -f "$TARGET" ]; then
    FILES="$TARGET"
else
    FILES=$(find "$TARGET" -name "*.spl" -type f)
fi

FIXED_COUNT=0
PATTERN_COUNT=0

for file in $FILES; do
    # Check if file has .new( patterns
    if ! grep -q "\.new(" "$file" 2>/dev/null; then
        continue
    fi

    echo "Processing: $file"

    # Backup original
    cp "$file" "$file.backup-constructor"

    FIXED_FILE=false

    # Extract all .new( patterns and their line numbers
    grep -n "\.new(" "$file" | while IFS=: read -r line_num line_content; do
        # Extract type name
        if [[ $line_content =~ ([A-Z][a-zA-Z_0-9]*)\.new\( ]]; then
            type_name="${BASH_REMATCH[1]}"

            # Check if we have field info for this type
            if [ -n "${TYPE_FIELDS[$type_name]}" ]; then
                fields="${TYPE_FIELDS[$type_name]}"
                echo "  Line $line_num: $type_name (fields: $fields)"
                PATTERN_COUNT=$((PATTERN_COUNT + 1))
                FIXED_FILE=true
            fi
        fi
    done

    if [ "$FIXED_FILE" = true ]; then
        FIXED_COUNT=$((FIXED_COUNT + 1))
    fi
done

echo ""
echo "Summary:"
echo "  Files with fixable constructors: $FIXED_COUNT"
echo "  Total .new() patterns found: $PATTERN_COUNT"
echo "  Backups saved as *.backup-constructor"
echo ""
echo "Note: Actual replacement needs manual review or advanced parsing."
echo "This scan identifies fixable patterns. Use the data to create targeted fixes."
