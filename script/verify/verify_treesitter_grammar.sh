#!/bin/bash
# Tree-sitter Grammar Verification Script
# Verifies all expected tokens and grammar rules are defined

set -e

GRAMMAR_DIR="src/lib/std/src/parser/treesitter/grammar"
QUERY_DIR="src/lib/std/src/parser/treesitter/queries"

echo "═══════════════════════════════════════════════════════════"
echo "Tree-Sitter Grammar Verification"
echo "═══════════════════════════════════════════════════════════"
echo ""

# Token verification
echo "Verifying Tokens..."
echo "─────────────────────────────────────────────────────────────"

EXPECTED_TOKENS=(
    "Val" "Var" "Me" "Fn"
    "Mod" "Use" "Export" "Common"
    "On" "Bind" "Forbid" "Allow" "Mock"
    "Out" "Requires" "Ensures" "Invariant" "Forall" "Exists" "Calc"
    "Feature" "Scenario" "Given" "When" "Then"
    "Union" "Mixin" "Actor" "Unit"
    "Iso" "Ref" "Mut"
    "PlusAssign" "MinusAssign" "StarAssign" "SlashAssign"
    "TildeAssign" "TildePlusAssign"
    "DoubleDot" "DoubleDotEq"
)

MISSING_TOKENS=0
for token in "${EXPECTED_TOKENS[@]}"; do
    if grep -q "$token" "$GRAMMAR_DIR/tokens.spl"; then
        echo "✓ $token"
    else
        echo "✗ $token - MISSING"
        MISSING_TOKENS=$((MISSING_TOKENS + 1))
    fi
done

echo ""
echo "Token Summary: $((${#EXPECTED_TOKENS[@]} - MISSING_TOKENS))/${#EXPECTED_TOKENS[@]} found"
echo ""

# Grammar rule verification
echo "Verifying Grammar Rules..."
echo "─────────────────────────────────────────────────────────────"

EXPECTED_RULES=(
    "val_stmt"
    "var_stmt"
    "fn_lambda"
    "backslash_lambda"
    "pipe_lambda"
    "mod_def"
    "on_stmt"
    "bind_stmt"
    "forbid_stmt"
    "allow_stmt"
    "mock_def"
    "out_stmt"
    "out_err_stmt"
    "requires_stmt"
    "ensures_stmt"
    "invariant_stmt"
    "forall_stmt"
    "exists_stmt"
    "calc_block"
    "feature_def"
    "scenario_def"
    "given_step"
    "when_step"
    "then_step"
    "union_def"
    "mixin_def"
    "actor_def"
    "unit_def"
    "handle_pool_def"
    "capability_type"
)

MISSING_RULES=0
for rule in "${EXPECTED_RULES[@]}"; do
    if grep -rq "\"$rule\"" "$GRAMMAR_DIR/"; then
        echo "✓ $rule"
    else
        echo "✗ $rule - MISSING"
        MISSING_RULES=$((MISSING_RULES + 1))
    fi
done

echo ""
echo "Rule Summary: $((${#EXPECTED_RULES[@]} - MISSING_RULES))/${#EXPECTED_RULES[@]} found"
echo ""

# LSP query file verification
echo "Verifying LSP Query Files..."
echo "─────────────────────────────────────────────────────────────"

QUERY_FILES=(
    "highlights.scm"
    "locals.scm"
    "folds.scm"
    "textobjects.scm"
    "injections.scm"
    "indents.scm"
)

MISSING_QUERIES=0
for file in "${QUERY_FILES[@]}"; do
    if [ -f "$QUERY_DIR/$file" ]; then
        LINES=$(wc -l < "$QUERY_DIR/$file")
        echo "✓ $file ($LINES lines)"
    else
        echo "✗ $file - MISSING"
        MISSING_QUERIES=$((MISSING_QUERIES + 1))
    fi
done

echo ""
echo "Query File Summary: $((${#QUERY_FILES[@]} - MISSING_QUERIES))/${#QUERY_FILES[@]} found"
echo ""

# Error recovery verification
echo "Verifying Error Recovery..."
echo "─────────────────────────────────────────────────────────────"

if [ -f "src/lib/std/src/parser/treesitter/error_recovery.spl" ]; then
    STRATEGIES=$(grep -c "RecoveryStrategy\." "src/lib/std/src/parser/treesitter/error_recovery.spl" || echo "0")
    echo "✓ error_recovery.spl exists"
    echo "  Found $STRATEGIES recovery strategy references"
else
    echo "✗ error_recovery.spl - MISSING"
fi

echo ""

# Final summary
echo "═══════════════════════════════════════════════════════════"
echo "Verification Summary"
echo "═══════════════════════════════════════════════════════════"
echo ""
echo "Tokens:      $((${#EXPECTED_TOKENS[@]} - MISSING_TOKENS))/${#EXPECTED_TOKENS[@]} ✓"
echo "Rules:       $((${#EXPECTED_RULES[@]} - MISSING_RULES))/${#EXPECTED_RULES[@]} ✓"
echo "Query Files: $((${#QUERY_FILES[@]} - MISSING_QUERIES))/${#QUERY_FILES[@]} ✓"
echo ""

TOTAL_EXPECTED=$((${#EXPECTED_TOKENS[@]} + ${#EXPECTED_RULES[@]} + ${#QUERY_FILES[@]}))
TOTAL_MISSING=$((MISSING_TOKENS + MISSING_RULES + MISSING_QUERIES))
TOTAL_FOUND=$((TOTAL_EXPECTED - TOTAL_MISSING))

echo "Overall: $TOTAL_FOUND/$TOTAL_EXPECTED components verified"
echo ""

if [ $TOTAL_MISSING -eq 0 ]; then
    echo "✅ ALL VERIFICATIONS PASSED"
    exit 0
else
    echo "❌ $TOTAL_MISSING COMPONENTS MISSING"
    exit 1
fi
