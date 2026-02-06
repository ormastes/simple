#!/usr/bin/env bash
# Fix all Cargo.toml paths after moving crates to src/rust/

set -e

echo "Fixing paths in src/rust/ crates..."

# List of all crates in src/rust/
RUST_CRATES=(
    "common" "parser" "compiler" "type" "loader"
    "runtime" "wasm-runtime" "driver" "native_loader"
    "pkg" "dependency_tracker" "diagnostics" "lsp" "dap"
    "simd" "gpu" "embedded" "stub" "ui" "db" "sqp" "sdn" "bin"
)

# Fix paths within src/rust/* crates
for crate_dir in src/rust/*/; do
    if [ -f "${crate_dir}Cargo.toml" ]; then
        echo "  Processing ${crate_dir}Cargo.toml"

        # Fix sibling rust crate references (should be ../crate_name)
        for crate in "${RUST_CRATES[@]}"; do
            sed -i "s|path = \"../rust/${crate}\"|path = \"../${crate}\"|g" "${crate_dir}Cargo.toml"
            sed -i "s|path = \"../../src/rust/${crate}\"|path = \"../${crate}\"|g" "${crate_dir}Cargo.toml"
        done

        # Fix i18n path (should be ../../i18n from src/rust/*)
        sed -i 's|path = "../i18n"|path = "../../i18n"|g' "${crate_dir}Cargo.toml"

        # Fix log path (should be ../../log from src/rust/*)
        sed -i 's|path = "../log"|path = "../../log"|g' "${crate_dir}Cargo.toml"

        # Fix util paths (should be ../util/whatever from src/rust/*)
        sed -i 's|path = "../rust/util/|path = "../util/|g' "${crate_dir}Cargo.toml"
        sed -i 's|path = "../../src/util/|path = "../util/|g' "${crate_dir}Cargo.toml"
    fi
done

echo "Fixing paths in test crates..."

# Fix test/rust/Cargo.toml
if [ -f "test/rust/Cargo.toml" ]; then
    echo "  Processing test/rust/Cargo.toml"

    for crate in "${RUST_CRATES[@]}"; do
        sed -i "s|path = \"../../src/${crate}\"|path = \"../../src/rust/${crate}\"|g" test/rust/Cargo.toml
    done

    # Fix util paths
    sed -i 's|path = "../../src/util/|path = "../../src/rust/util/|g' test/rust/Cargo.toml
fi

# Fix tests/Cargo.toml (old location)
if [ -f "tests/Cargo.toml" ]; then
    echo "  Processing tests/Cargo.toml"

    for crate in "${RUST_CRATES[@]}"; do
        sed -i "s|path = \"../src/${crate}\"|path = \"../src/rust/${crate}\"|g" tests/Cargo.toml
    done

    # Fix util paths
    sed -i 's|path = "../src/util/|path = "../src/rust/util/|g' tests/Cargo.toml
fi

echo "✅ Path fixing complete"
