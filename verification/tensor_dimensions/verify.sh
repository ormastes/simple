#!/bin/bash
# Verification script for Tensor Dimensions Lean proofs

set -e

echo "============================================================"
echo "  Tensor Dimension Inference - Lean 4 Verification"
echo "============================================================"
echo ""

# Check if Lake is installed
if ! command -v lake &> /dev/null; then
    echo "❌ Error: Lake (Lean build tool) is not installed"
    echo "   Install Lean 4 from: https://leanprover.github.io/lean4/doc/setup.html"
    exit 1
fi

echo "✓ Lake found: $(lake --version)"
echo ""

# Update dependencies (first time only)
echo "Updating Lake dependencies..."
lake update

echo ""
echo "Building Lean verification project..."
lake build

if [ $? -eq 0 ]; then
    echo ""
    echo "============================================================"
    echo "  ✅ VERIFICATION SUCCESSFUL"
    echo "============================================================"
    echo ""
    echo "All theorems verified:"
    echo "  • shapesCompatible_refl"
    echo "  • unifyDim_success_eq"
    echo "  • matmulShape_deterministic"
    echo "  • min_le_max_elements"
    echo "  • training_fits_if_max_fits"
    echo "  • components_fit_implies_total_fits"
    echo "  • training_memory_bounds_consistent"
    echo "  • tensor_memory_bounds_valid"
    echo ""
else
    echo ""
    echo "============================================================"
    echo "  ❌ VERIFICATION FAILED"
    echo "============================================================"
    echo ""
    echo "Check the output above for errors in the Lean proofs."
    exit 1
fi
