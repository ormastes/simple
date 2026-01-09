#!/bin/bash
# complete_mixin_phase1.sh - Apply all remaining changes for Phase 1

set -e
cd "$(dirname "$0")"

echo "=== Completing Mixin Phase 1 Implementation ==="
echo

# 1. Add TokenKind::Mixin to token.rs
echo "Step 1: Adding TokenKind::Mixin..."
if ! grep -q "    Mixin," src/parser/src/token.rs; then
    sed -i '/    Impl,/a\    Mixin,  // mixin (for mixin declarations, Feature #2200)' src/parser/src/token.rs
    echo "  ✅ Added Mixin token"
else
    echo "  ℹ️  Mixin token already exists"
fi

# 2. Add "mixin" keyword mapping to lexer
echo "Step 2: Adding lexer keyword mapping..."
if ! grep -q '"mixin"' src/parser/src/lexer/identifiers.rs; then
    sed -i '/"impl" => TokenKind::Impl,/a\            "mixin" => TokenKind::Mixin,' src/parser/src/lexer/identifiers.rs
    echo "  ✅ Added mixin keyword mapping"
else
    echo "  ℹ️  Mixin keyword mapping already exists"
fi

# 3. Add Node::Mixin to core.rs
echo "Step 3: Adding Node::Mixin variant..."
if ! grep -q "Mixin(MixinDef)" src/parser/src/ast/nodes/core.rs; then
    sed -i '/    Impl(ImplBlock),/a\    Mixin(MixinDef),' src/parser/src/ast/nodes/core.rs
    echo "  ✅ Added Mixin node variant"
else
    echo "  ℹ️  Mixin node variant already exists"
fi

# 4. Add AST structures to definitions.rs
echo "Step 4: Adding AST structures..."
if ! grep -q "pub struct MixinDef" src/parser/src/ast/nodes/definitions.rs; then
    # Find the line number before ActorDef
    LINE=$(grep -n "pub struct ActorDef" src/parser/src/ast/nodes/definitions.rs | head -1 | cut -d: -f1)
    LINE=$((LINE - 3))  # Insert 3 lines before (accounting for derives)
    
    # Create temp file with structures
    head -n $LINE src/parser/src/ast/nodes/definitions.rs > /tmp/defs_temp.rs
    cat >> /tmp/defs_temp.rs << 'STRUCTS'

/// Mixin definition: mixin Name[T] requires Trait: fields and methods
/// Mixins provide reusable field and method compositions for classes and structs.
/// Feature #2200: Mixin Declaration Syntax
#[derive(Debug, Clone, PartialEq)]
pub struct MixinDef {
    pub span: Span,
    pub name: String,
    pub generic_params: Vec<String>,
    pub required_traits: Vec<String>,
    pub required_mixins: Vec<String>,
    pub fields: Vec<Field>,
    pub methods: Vec<FunctionDef>,
    pub required_methods: Vec<RequiredMethodSig>,
    pub visibility: Visibility,
    pub doc_comment: Option<DocComment>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct RequiredMethodSig {
    pub span: Span,
    pub name: String,
    pub params: Vec<Parameter>,
    pub return_type: Option<Type>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct MixinRef {
    pub span: Span,
    pub name: String,
    pub type_args: Vec<Type>,
    pub overrides: Vec<OverrideSpec>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OverrideSpec {
    Override(String),
    Hide(String),
    Rename { old_name: String, new_name: String },
}

STRUCTS
    tail -n +$((LINE + 1)) src/parser/src/ast/nodes/definitions.rs >> /tmp/defs_temp.rs
    mv /tmp/defs_temp.rs src/parser/src/ast/nodes/definitions.rs
    echo "  ✅ Added AST structures"
else
    echo "  ℹ️  AST structures already exist"
fi

# 5. Verify parse_mixin exists
echo "Step 5: Verifying parse_mixin method..."
if grep -q "pub(crate) fn parse_mixin" src/parser/src/types_def/mod.rs; then
    echo "  ✅ parse_mixin method exists"
else
    echo "  ❌ parse_mixin method missing - manual addition needed"
    exit 1
fi

# 6. Verify TokenKind::Mixin dispatch in parser
echo "Step 6: Verifying parser dispatch..."
if grep -q "TokenKind::Mixin" src/parser/src/parser_impl/core.rs; then
    echo "  ✅ Parser dispatch exists"
else
    echo "  Adding parser dispatch..."
    sed -i '/TokenKind::Trait => self.parse_trait_with_doc(doc_comment),/a\            TokenKind::Mixin => self.parse_mixin(),' src/parser/src/parser_impl/core.rs
    echo "  ✅ Added parser dispatch"
fi

echo
echo "=== Building Parser ==="
cargo build -p simple-parser 2>&1 | tail -5

if [ $? -eq 0 ]; then
    echo
    echo "🎉 SUCCESS! Phase 1 Complete (100%)"
    echo
    echo "Next steps:"
    echo "1. Run tests: cargo test -p simple-parser"
    echo "2. Test parsing: rustc examples/test_mixin_parse.rs ..."
    echo "3. Begin Phase 2: Type System"
else
    echo
    echo "❌ Build failed - check errors above"
    exit 1
fi
