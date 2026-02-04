#!/bin/bash
# Import Fixer - Correct Order
# Fixes: ./ then ../ then /

echo "Fixing import paths..."

find src test -name "*.spl" -type f | while read file; do
    if grep -qE "use .*(\/|\.\.|\.\/)" "$file"; then
        echo "Fixing: $file"

        # Apply fixes in correct order using multiple sed passes:
        # Pass 1: Fix "use ./" -> "use ."
        # Pass 2: Fix "use ../" -> "use .."
        # Pass 3: Fix remaining "/" -> "."
        sed -i.bak1 's/use \.\//use ./g' "$file"
        sed -i.bak2 's/use \.\.\//use ../g' "$file"
        sed -i.bak3 's/\(use [^ ]*\)\/\([^ ]*\)/\1.\2/g' "$file"

        # Repeat pass 3 to catch multiple slashes
        sed -i.bak4 's/\(use [^ ]*\)\/\([^ ]*\)/\1.\2/g' "$file"

        # Show changes
        if ! cmp -s "$file" "$file.bak1"; then
            diff -u "$file.bak1" "$file" | grep "^[-+]use" | head -3
        fi

        rm -f "$file".bak*
    fi
done

echo "Done"
