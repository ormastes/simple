#!/bin/bash
# Build Type Database
#
# Scans source code for struct/class definitions and extracts field names.
# Output: build/type_database.txt (format: TypeName:field1,field2,field3)

set -e

OUTPUT_FILE="build/type_database.txt"
mkdir -p build

echo "=== Building Type Database ==="
echo "Scanning src/ and test/lib for type definitions..."
echo ""

> "$OUTPUT_FILE"

# Find all .spl files
find src test/lib -name "*.spl" -type f 2>/dev/null | while read file; do
    # Extract struct/class definitions with their fields
    # Pattern: struct TypeName: or class TypeName:
    awk '
    /^(struct|class) [A-Z][a-zA-Z_0-9]*:/ {
        # Extract type name
        match($0, /^(struct|class) ([A-Z][a-zA-Z_0-9]*)/, arr)
        type_name = arr[2]
        in_type = 1
        fields = ""
        next
    }

    in_type && /^[[:space:]]+[a-z_][a-zA-Z_0-9]*:/ {
        # Extract field name
        match($0, /^[[:space:]]+([a-z_][a-zA-Z_0-9]*):/, arr)
        field_name = arr[1]
        if (fields == "") {
            fields = field_name
        } else {
            fields = fields "," field_name
        }
    }

    in_type && /^[[:space:]]*$/ {
        # Empty line, end of type definition
        if (type_name != "" && fields != "") {
            print type_name ":" fields
            type_name = ""
            fields = ""
        }
        in_type = 0
    }

    in_type && /^[a-zA-Z]/ {
        # Non-indented line, end of type definition
        if (type_name != "" && fields != "") {
            print type_name ":" fields
            type_name = ""
            fields = ""
        }
        in_type = 0
    }
    ' "$file" >> "$OUTPUT_FILE"
done

# Remove duplicates and sort
sort -u "$OUTPUT_FILE" -o "$OUTPUT_FILE"

TOTAL=$(wc -l < "$OUTPUT_FILE")
echo "Found $TOTAL type definitions"
echo "Output: $OUTPUT_FILE"
echo ""
echo "Sample entries:"
head -20 "$OUTPUT_FILE"
