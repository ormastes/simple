# Static Polymorphism Implementation Plan

**Date:** 2026-01-08
**Status:** Planning
**Research Doc:** [static_polymorphism.md](../research/static_polymorphism.md)

## Overview

This document provides a step-by-step implementation plan for static polymorphism (bindable interfaces) in the Simple language compiler. The implementation is divided into 6 phases, each building on the previous.

## Phase Summary

| Phase | Component | Files | Priority |
|-------|-----------|-------|----------|
| 1 | Parser + AST | parser/ | High |
| 2 | Lean4 Generator | compiler/lean_gen/ | High |
| 3 | Type Checker | type/ | High |
| 4 | Interpreter | compiler/interpreter*.rs | Medium |
| 5 | HIR/MIR/Codegen | compiler/hir/, mir/, codegen/ | Medium |
| 6 | Build System | driver/ | Low |

---

## Phase 1: Parser + AST

**Goal:** Parse `bind` statements and represent them in the AST.

### Step 1.1: Add Token

**File:** `src/parser/src/token.rs`

```rust
// Add to TokenKind enum
pub enum TokenKind {
    // ... existing tokens ...
    Bind,       // 'bind' keyword
    Static,     // 'static' modifier (may already exist)
    Dyn,        // 'dyn' modifier
    // ... rest ...
}
```

### Step 1.2: Update Lexer

**File:** `src/parser/src/lexer/identifiers.rs`

```rust
// Add to keyword matching
fn keyword_or_ident(&mut self, text: &str) -> TokenKind {
    match text {
        // ... existing keywords ...
        "bind" => TokenKind::Bind,
        "dyn" => TokenKind::Dyn,
        // "static" may already exist
        _ => TokenKind::Ident(text.to_string()),
    }
}
```

### Step 1.3: Add AST Nodes

**File:** `src/parser/src/ast/nodes/modules.rs` (new or extend)

```rust
/// Dispatch mode for interface types
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DispatchMode {
    /// Always use static dispatch (CRTP-like)
    Static,
    /// Always use dynamic dispatch (vtable)
    Dynamic,
    /// Let compiler decide based on bindings and optimization
    Auto,
}

impl Default for DispatchMode {
    fn default() -> Self {
        DispatchMode::Auto
    }
}

/// Interface binding statement: bind I = T
#[derive(Debug, Clone)]
pub struct BindStmt {
    /// Visibility: pub, common, or private
    pub visibility: Visibility,
    /// Dispatch mode: static, dyn, or auto
    pub mode: DispatchMode,
    /// The interface/trait being bound
    pub interface_path: ModulePath,
    /// The implementing type
    pub impl_path: ModulePath,
    /// Source location
    pub span: Span,
}

/// Interface type with dispatch qualifier
#[derive(Debug, Clone)]
pub enum InterfaceType {
    /// dyn I - always dynamic
    Dyn(String),
    /// static I - always static (requires binding)
    Static(String),
    /// I - dispatchable (compiler chooses)
    Dispatchable(String),
}
```

### Step 1.4: Add Node Variant

**File:** `src/parser/src/ast/nodes/core.rs`

```rust
pub enum Node {
    // ... existing variants ...
    BindStmt(BindStmt),
}
```

### Step 1.5: Parse Bind Statement

**File:** `src/parser/src/parser_impl/core.rs`

**Current Implementation (Simplified):**
```rust
impl Parser<'_> {
    /// Parse: bind Interface = Type
    /// Note: No static/dyn/auto modifiers in current implementation
    fn parse_bind_stmt(&mut self) -> Result<BindStmt, ParseError> {
        let start = self.current_span();

        // 'bind' keyword
        self.expect(TokenKind::Bind)?;
            self.advance();
            DispatchMode::Dynamic
        } else {
            DispatchMode::Auto
        };

        // Interface path
        let interface_path = self.parse_module_path()?;

        // '=' separator
        self.expect(TokenKind::Eq)?;

        // Implementation type path
        let impl_path = self.parse_module_path()?;

        let span = start.merge(self.previous_span());

        Ok(BindStmt {
            visibility,
            mode,
            interface_path,
            impl_path,
            span,
        })
    }
}
```

### Step 1.6: Integrate into Module Parsing

**File:** `src/parser/src/parser_impl/core.rs`

```rust
fn parse_module_item(&mut self) -> Result<Node, ParseError> {
    match self.current_kind() {
        TokenKind::Bind => Ok(Node::BindStmt(self.parse_bind_stmt()?)),
        // ... existing cases ...
    }
}
```

### Step 1.7: Update DirectoryManifest

**File:** `src/compiler/src/module_resolver/types.rs`

```rust
pub struct DirectoryManifest {
    pub name: String,
    pub attributes: Vec<Attribute>,
    pub child_modules: Vec<ChildModule>,
    pub common_uses: Vec<CommonUseStmt>,
    pub exports: Vec<ExportUseStmt>,
    pub auto_imports: Vec<AutoImportStmt>,
    pub capabilities: Vec<Capability>,
    pub bindings: Vec<BindingDecl>,  // NEW
}

pub struct BindingDecl {
    pub visibility: Visibility,
    pub mode: DispatchMode,
    pub interface_name: String,
    pub impl_type: String,
}
```

### Step 1.8: Extract Bindings from Manifest

**File:** `src/compiler/src/module_resolver/manifest.rs`

```rust
fn extract_manifest(module: &Module) -> DirectoryManifest {
    // ... existing extraction ...

    let bindings = module.nodes.iter()
        .filter_map(|node| match node {
            Node::BindStmt(bind) => Some(BindingDecl {
                visibility: bind.visibility.clone(),
                mode: bind.mode.clone(),
                interface_name: bind.interface_path.to_string(),
                impl_type: bind.impl_path.to_string(),
            }),
            _ => None,
        })
        .collect();

    DirectoryManifest {
        // ... existing fields ...
        bindings,
    }
}
```

### Phase 1 Tests

```rust
#[test]
fn test_parse_bind_stmt() {
    let code = "bind Logger = ConsoleLogger";
    let ast = parse(code).unwrap();
    assert!(matches!(ast.nodes[0], Node::BindStmt(_)));
}

#[test]
fn test_parse_bind_with_mode() {
    let code = "bind static Cache = RedisCache";
    let ast = parse(code).unwrap();
    if let Node::BindStmt(bind) = &ast.nodes[0] {
        assert_eq!(bind.mode, DispatchMode::Static);
    }
}

#[test]
fn test_parse_pub_bind() {
    let code = "pub bind Crypto = RingCrypto";
    let ast = parse(code).unwrap();
    if let Node::BindStmt(bind) = &ast.nodes[0] {
        assert_eq!(bind.visibility, Visibility::Public);
    }
}
```

---

## Phase 2: Lean4 Generator

**Goal:** Generate Lean4 code from Simple source for verification.

### Step 2.1: Create Module Structure

```
src/compiler/src/lean_gen/
├── mod.rs           # Main generator
├── types.rs         # Type translation
├── traits.rs        # Trait/class generation
├── bindings.rs      # Binding statement generation
├── proofs.rs        # Proof obligation generation
└── writer.rs        # Lean4 code writer
```

### Step 2.2: Core Generator

**File:** `src/compiler/src/lean_gen/mod.rs`

```rust
use std::path::PathBuf;
use std::fs;
use simple_parser::ast::*;

pub mod types;
pub mod traits;
pub mod bindings;
pub mod proofs;
pub mod writer;

use types::LeanType;
use writer::LeanWriter;

#[derive(Debug)]
pub struct LeanGenError {
    pub message: String,
    pub span: Option<Span>,
}

/// Context for Lean generation
pub struct LeanGenContext {
    pub traits: Vec<TraitDef>,
    pub classes: Vec<ClassDef>,
    pub impls: Vec<ImplBlock>,
    pub bindings: Vec<BindStmt>,
    pub module_path: String,
}

pub struct LeanGenerator {
    output_dir: PathBuf,
    project_name: String,
}

impl LeanGenerator {
    pub fn new(output_dir: PathBuf, project_name: String) -> Self {
        Self { output_dir, project_name }
    }

    /// Generate Lean4 code from Simple modules
    pub fn generate(&self, modules: &[Module]) -> Result<(), LeanGenError> {
        fs::create_dir_all(&self.output_dir)?;

        let context = self.collect_definitions(modules)?;

        // Generate main module file
        self.generate_module(&context)?;

        // Generate lakefile.lean
        self.generate_lakefile()?;

        Ok(())
    }

    fn collect_definitions(&self, modules: &[Module]) -> Result<LeanGenContext, LeanGenError> {
        let mut traits = Vec::new();
        let mut classes = Vec::new();
        let mut impls = Vec::new();
        let mut bindings = Vec::new();

        for module in modules {
            for node in &module.nodes {
                match node {
                    Node::TraitDef(t) => traits.push(t.clone()),
                    Node::ClassDef(c) => classes.push(c.clone()),
                    Node::ImplBlock(i) => impls.push(i.clone()),
                    Node::BindStmt(b) => bindings.push(b.clone()),
                    _ => {}
                }
            }
        }

        Ok(LeanGenContext {
            traits,
            classes,
            impls,
            bindings,
            module_path: String::new(),
        })
    }

    fn generate_module(&self, ctx: &LeanGenContext) -> Result<(), LeanGenError> {
        let mut writer = LeanWriter::new();

        // Header
        writer.write_header(&self.project_name);

        // Generate types (classes as structures)
        for class in &ctx.classes {
            types::generate_structure(&mut writer, class)?;
        }

        // Generate trait classes
        for trait_def in &ctx.traits {
            traits::generate_trait_class(&mut writer, trait_def)?;
        }

        // Generate instances (implementations)
        for impl_block in &ctx.impls {
            traits::generate_instance(&mut writer, impl_block, &ctx.classes)?;
        }

        // Generate bindings
        for binding in &ctx.bindings {
            bindings::generate_binding(&mut writer, binding)?;
        }

        // Generate proof obligations
        proofs::generate_proofs(&mut writer, ctx)?;

        // Write to file
        let output_path = self.output_dir.join(format!("{}.lean", self.project_name));
        fs::write(&output_path, writer.finish())?;

        Ok(())
    }

    fn generate_lakefile(&self) -> Result<(), LeanGenError> {
        let content = format!(r#"
import Lake
open Lake DSL

package «{}» where

@[default_target]
lean_lib «{}» where
"#, self.project_name, self.project_name);

        let path = self.output_dir.join("lakefile.lean");
        fs::write(&path, content)?;

        // Write lean-toolchain
        let toolchain = "leanprover/lean4:v4.3.0";
        fs::write(self.output_dir.join("lean-toolchain"), toolchain)?;

        Ok(())
    }
}
```

### Step 2.3: Type Translation

**File:** `src/compiler/src/lean_gen/types.rs`

```rust
use super::writer::LeanWriter;
use simple_parser::ast::{ClassDef, Type as AstType};

/// Translate Simple type to Lean type string
pub fn translate_type(ty: &AstType) -> String {
    match ty {
        AstType::Int => "Int".to_string(),
        AstType::Bool => "Bool".to_string(),
        AstType::Str => "String".to_string(),
        AstType::Float => "Float".to_string(),
        AstType::Named(name) => name.clone(),
        AstType::Generic { name, args } => {
            let args_str: Vec<String> = args.iter()
                .map(|a| translate_type(a))
                .collect();
            if args_str.is_empty() {
                name.clone()
            } else {
                format!("{} {}", name, args_str.join(" "))
            }
        }
        AstType::Array(inner) => format!("List {}", translate_type(inner)),
        AstType::Option(inner) => format!("Option {}", translate_type(inner)),
        AstType::Function { params, ret } => {
            let params_str: Vec<String> = params.iter()
                .map(|p| translate_type(p))
                .collect();
            let ret_str = translate_type(ret);
            format!("{} → {}", params_str.join(" → "), ret_str)
        }
        _ => "Unit".to_string(), // Fallback
    }
}

/// Generate Lean structure from Simple class
pub fn generate_structure(writer: &mut LeanWriter, class: &ClassDef) -> Result<(), super::LeanGenError> {
    writer.writeln(&format!("structure {} where", class.name));
    writer.indent();

    for field in &class.fields {
        let ty = translate_type(&field.ty);
        writer.writeln(&format!("{} : {}", field.name, ty));
    }

    writer.dedent();
    writer.writeln("  deriving Repr");
    writer.newline();

    Ok(())
}
```

### Step 2.4: Trait Generation

**File:** `src/compiler/src/lean_gen/traits.rs`

```rust
use super::writer::LeanWriter;
use super::types::translate_type;
use simple_parser::ast::{TraitDef, ImplBlock, ClassDef};

/// Generate Lean class from Simple trait
pub fn generate_trait_class(writer: &mut LeanWriter, trait_def: &TraitDef) -> Result<(), super::LeanGenError> {
    // class TraitName (α : Type) where
    writer.writeln(&format!("class {} (α : Type) where", trait_def.name));
    writer.indent();

    for method in &trait_def.methods {
        // method_name : α → Param1 → Param2 → RetType
        let mut sig_parts = vec!["α".to_string()];
        for param in &method.params {
            sig_parts.push(translate_type(&param.ty));
        }
        let ret = translate_type(&method.return_type);
        writer.writeln(&format!("{} : {} → {}", method.name, sig_parts.join(" → "), ret));
    }

    writer.dedent();
    writer.newline();

    Ok(())
}

/// Generate Lean instance from Simple impl block
pub fn generate_instance(
    writer: &mut LeanWriter,
    impl_block: &ImplBlock,
    classes: &[ClassDef],
) -> Result<(), super::LeanGenError> {
    let trait_name = &impl_block.trait_name;
    let for_type = &impl_block.for_type;

    writer.writeln(&format!("instance : {} {} where", trait_name, for_type));
    writer.indent();

    for method in &impl_block.methods {
        // Generate method implementation
        // For now, use sorry as placeholder
        writer.writeln(&format!("{} := sorry", method.name));
    }

    writer.dedent();
    writer.newline();

    Ok(())
}
```

### Step 2.5: Binding Generation

**File:** `src/compiler/src/lean_gen/bindings.rs`

```rust
use super::writer::LeanWriter;
use simple_parser::ast::BindStmt;

/// Generate Lean abbreviation and instance for binding
pub fn generate_binding(writer: &mut LeanWriter, bind: &BindStmt) -> Result<(), super::LeanGenError> {
    let iface = &bind.interface_path.to_string();
    let impl_ty = &bind.impl_path.to_string();

    // abbrev TraitName.Bound := ImplType
    writer.writeln(&format!("abbrev {}.Bound := {}", iface, impl_ty));

    // instance TraitName.BoundInstance : TraitName TraitName.Bound := inferInstance
    writer.writeln(&format!(
        "instance {}.BoundInstance : {} {}.Bound := inferInstance",
        iface, iface, iface
    ));

    writer.newline();

    Ok(())
}
```

### Step 2.6: Proof Generation

**File:** `src/compiler/src/lean_gen/proofs.rs`

```rust
use super::writer::LeanWriter;
use super::LeanGenContext;

/// Generate proof obligations for the module
pub fn generate_proofs(writer: &mut LeanWriter, ctx: &LeanGenContext) -> Result<(), super::LeanGenError> {
    writer.writeln("-- Proof obligations");
    writer.newline();

    // For each binding, prove it's valid
    for bind in &ctx.bindings {
        let iface = &bind.interface_path.to_string();
        let impl_ty = &bind.impl_path.to_string();

        writer.writeln(&format!(
            "theorem {}_binding_valid : {} {} := inferInstance",
            iface.to_lowercase(), iface, impl_ty
        ));
    }

    // For each impl, prove completeness
    for impl_block in &ctx.impls {
        let trait_name = &impl_block.trait_name;
        let for_type = &impl_block.for_type;

        writer.writeln(&format!(
            "theorem {}_{}_complete : {} {} := inferInstance",
            for_type.to_lowercase(), trait_name.to_lowercase(),
            trait_name, for_type
        ));
    }

    Ok(())
}
```

### Step 2.7: Writer Utility

**File:** `src/compiler/src/lean_gen/writer.rs`

```rust
pub struct LeanWriter {
    buffer: String,
    indent_level: usize,
}

impl LeanWriter {
    pub fn new() -> Self {
        Self {
            buffer: String::new(),
            indent_level: 0,
        }
    }

    pub fn write_header(&mut self, module_name: &str) {
        self.writeln(&format!("/-"));
        self.writeln(&format!("  Auto-generated from Simple source"));
        self.writeln(&format!("  Module: {}", module_name));
        self.writeln(&format!("  DO NOT EDIT - regenerate with: simple --gen-lean"));
        self.writeln(&format!("-/"));
        self.newline();
    }

    pub fn indent(&mut self) {
        self.indent_level += 1;
    }

    pub fn dedent(&mut self) {
        if self.indent_level > 0 {
            self.indent_level -= 1;
        }
    }

    pub fn writeln(&mut self, line: &str) {
        let indent = "  ".repeat(self.indent_level);
        self.buffer.push_str(&indent);
        self.buffer.push_str(line);
        self.buffer.push('\n');
    }

    pub fn newline(&mut self) {
        self.buffer.push('\n');
    }

    pub fn finish(self) -> String {
        self.buffer
    }
}
```

### Phase 2 Tests

```rust
#[test]
fn test_lean_gen_simple_trait() {
    let code = r#"
        trait Logger:
            fn log(msg: Str)
    "#;
    let modules = vec![parse(code).unwrap()];
    let gen = LeanGenerator::new(temp_dir(), "TestModule".into());
    gen.generate(&modules).unwrap();

    let output = fs::read_to_string(temp_dir().join("TestModule.lean")).unwrap();
    assert!(output.contains("class Logger"));
}

#[test]
fn test_lean_gen_binding() {
    let code = "bind Logger = ConsoleLogger";
    let modules = vec![parse(code).unwrap()];
    let gen = LeanGenerator::new(temp_dir(), "TestBindings".into());
    gen.generate(&modules).unwrap();

    let output = fs::read_to_string(temp_dir().join("TestBindings.lean")).unwrap();
    assert!(output.contains("abbrev Logger.Bound := ConsoleLogger"));
}
```

---

## Phase 3: Type Checker

**Goal:** Enforce binding constraints during type checking.

### Step 3.1: Create Binding Environment

**File:** `src/type/src/bindings.rs` (new)

```rust
use std::collections::HashMap;
use crate::Type;

#[derive(Debug, Clone, PartialEq)]
pub enum DispatchMode {
    Static,
    Dynamic,
    Auto,
}

#[derive(Debug, Clone)]
pub struct InterfaceBinding {
    pub interface_name: String,
    pub impl_type: Type,
    pub mode: DispatchMode,
}

#[derive(Debug, Default)]
pub struct BindingEnv {
    bindings: HashMap<String, InterfaceBinding>,
}

impl BindingEnv {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_binding(&mut self, binding: InterfaceBinding) {
        self.bindings.insert(binding.interface_name.clone(), binding);
    }

    pub fn lookup(&self, interface: &str) -> Option<&InterfaceBinding> {
        self.bindings.get(interface)
    }

    pub fn has_binding(&self, interface: &str) -> bool {
        self.bindings.contains_key(interface)
    }

    /// Check if a concrete type is valid for an interface type
    pub fn check_iface_type(
        &self,
        iface_name: &str,
        concrete_type: &Type,
        dispatch: DispatchMode,
    ) -> Result<(), BindingError> {
        match dispatch {
            DispatchMode::Dynamic => {
                // Any implementation is valid for dyn I
                Ok(())
            }
            DispatchMode::Static => {
                // Must match the binding
                match self.lookup(iface_name) {
                    Some(binding) if binding.impl_type == *concrete_type => Ok(()),
                    Some(binding) => Err(BindingError::WrongType {
                        interface: iface_name.to_string(),
                        expected: binding.impl_type.clone(),
                        found: concrete_type.clone(),
                    }),
                    None => Err(BindingError::NoBinding {
                        interface: iface_name.to_string(),
                    }),
                }
            }
            DispatchMode::Auto => {
                // If binding exists, must match; otherwise any impl is ok
                if let Some(binding) = self.lookup(iface_name) {
                    if binding.impl_type == *concrete_type {
                        Ok(())
                    } else {
                        Err(BindingError::WrongType {
                            interface: iface_name.to_string(),
                            expected: binding.impl_type.clone(),
                            found: concrete_type.clone(),
                        })
                    }
                } else {
                    Ok(())
                }
            }
        }
    }
}

#[derive(Debug)]
pub enum BindingError {
    NoBinding { interface: String },
    WrongType {
        interface: String,
        expected: Type,
        found: Type,
    },
}
```

### Step 3.2: Integrate into Type Checker

**File:** `src/type/src/checker_check.rs`

```rust
use crate::bindings::{BindingEnv, DispatchMode};

pub struct TypeChecker {
    // ... existing fields ...
    pub binding_env: BindingEnv,
}

impl TypeChecker {
    /// Check type assignment with interface binding awareness
    pub fn check_assignment(
        &self,
        target_type: &Type,
        value_type: &Type,
    ) -> Result<(), TypeError> {
        // If target is an interface type, check binding constraints
        if let Type::Named(name) = target_type {
            if self.is_interface(name) {
                let dispatch = self.get_dispatch_mode(target_type);
                self.binding_env.check_iface_type(name, value_type, dispatch)?;
            }
        }

        // ... existing type checking ...
        Ok(())
    }

    fn get_dispatch_mode(&self, ty: &Type) -> DispatchMode {
        // Check for dyn/static qualifiers on the type
        // Default to Auto
        DispatchMode::Auto
    }

    fn is_interface(&self, name: &str) -> bool {
        // Check if name refers to a trait/interface
        self.trait_registry.contains(name)
    }
}
```

### Phase 3 Tests

```rust
#[test]
fn test_binding_enforced() {
    let mut env = BindingEnv::new();
    env.add_binding(InterfaceBinding {
        interface_name: "Logger".into(),
        impl_type: Type::Named("ConsoleLogger".into()),
        mode: DispatchMode::Auto,
    });

    // Correct type should pass
    assert!(env.check_iface_type(
        "Logger",
        &Type::Named("ConsoleLogger".into()),
        DispatchMode::Auto
    ).is_ok());

    // Wrong type should fail
    assert!(env.check_iface_type(
        "Logger",
        &Type::Named("FileLogger".into()),
        DispatchMode::Auto
    ).is_err());
}

#[test]
fn test_dyn_bypasses_binding() {
    let mut env = BindingEnv::new();
    env.add_binding(InterfaceBinding {
        interface_name: "Logger".into(),
        impl_type: Type::Named("ConsoleLogger".into()),
        mode: DispatchMode::Auto,
    });

    // dyn allows any implementation
    assert!(env.check_iface_type(
        "Logger",
        &Type::Named("FileLogger".into()),
        DispatchMode::Dynamic
    ).is_ok());
}
```

---

## Phase 4: Interpreter

**Goal:** Support static/dynamic dispatch in the interpreter.

### Step 4.1: Update Method Dispatch

**File:** `src/compiler/src/interpreter_helpers/method_dispatch.rs`

```rust
use crate::bindings::{BindingEnv, DispatchMode};

/// Dispatch a trait method call
pub fn dispatch_trait_method(
    receiver: Value,
    trait_name: &str,
    method_name: &str,
    args: &[Value],
    bindings: &BindingEnv,
    impl_methods: &ImplMethods,
    dispatch_mode: DispatchMode,
) -> Result<Value, CompileError> {
    match dispatch_mode {
        DispatchMode::Static => {
            let binding = bindings.lookup(trait_name).ok_or_else(|| {
                CompileError::Semantic(format!(
                    "static dispatch requires binding for trait '{}'",
                    trait_name
                ))
            })?;

            // Dispatch to the bound implementation
            let impl_type = &binding.impl_type.to_string();
            dispatch_to_impl(receiver, impl_type, method_name, args, impl_methods)
        }
        DispatchMode::Dynamic => {
            // Runtime lookup based on receiver's actual type
            let actual_type = receiver.type_name();
            dispatch_to_impl(receiver, &actual_type, method_name, args, impl_methods)
        }
        DispatchMode::Auto => {
            // Check for binding, fall back to dynamic
            if let Some(binding) = bindings.lookup(trait_name) {
                let impl_type = &binding.impl_type.to_string();
                dispatch_to_impl(receiver, impl_type, method_name, args, impl_methods)
            } else {
                let actual_type = receiver.type_name();
                dispatch_to_impl(receiver, &actual_type, method_name, args, impl_methods)
            }
        }
    }
}

fn dispatch_to_impl(
    receiver: Value,
    impl_type: &str,
    method_name: &str,
    args: &[Value],
    impl_methods: &ImplMethods,
) -> Result<Value, CompileError> {
    if let Some(methods) = impl_methods.get(impl_type) {
        if let Some(method) = methods.iter().find(|m| m.name == method_name) {
            // Execute the method
            // ... method execution logic ...
            todo!()
        }
    }
    Err(CompileError::Semantic(format!(
        "method '{}' not found on type '{}'",
        method_name, impl_type
    )))
}
```

### Step 4.2: Thread Bindings Through Interpreter

**File:** `src/compiler/src/interpreter.rs`

```rust
pub struct Interpreter {
    // ... existing fields ...
    pub binding_env: BindingEnv,
}

impl Interpreter {
    pub fn load_bindings(&mut self, manifest: &DirectoryManifest) {
        for binding in &manifest.bindings {
            self.binding_env.add_binding(InterfaceBinding {
                interface_name: binding.interface_name.clone(),
                impl_type: Type::Named(binding.impl_type.clone()),
                mode: binding.mode.clone().into(),
            });
        }
    }
}
```

---

## Phase 5: HIR/MIR/Codegen

**Goal:** Generate optimized code for static dispatch.

### Step 5.1: HIR Dispatch Annotation

**File:** `src/compiler/src/hir/mod.rs`

```rust
#[derive(Debug, Clone)]
pub struct HirMethodCall {
    pub receiver: Box<HirExpr>,
    pub method: String,
    pub args: Vec<HirExpr>,
    pub dispatch: DispatchInfo,  // NEW
}

#[derive(Debug, Clone)]
pub enum DispatchInfo {
    /// Direct call to known implementation
    Static { impl_type: String },
    /// Virtual call through vtable
    Dynamic { trait_name: String },
    /// Resolved at MIR lowering based on bindings
    Unresolved { trait_name: String },
}
```

### Step 5.2: MIR Dispatch Resolution

**File:** `src/compiler/src/mir/lower.rs`

```rust
impl MirLowerer {
    fn lower_method_call(&mut self, call: &HirMethodCall) -> MirInstruction {
        match &call.dispatch {
            DispatchInfo::Static { impl_type } => {
                // Direct call
                MirInstruction::DirectCall {
                    func: format!("{}::{}", impl_type, call.method),
                    args: self.lower_args(&call.args),
                }
            }
            DispatchInfo::Dynamic { trait_name } => {
                // Vtable call
                MirInstruction::VirtualCall {
                    receiver: self.lower_expr(&call.receiver),
                    trait_name: trait_name.clone(),
                    method: call.method.clone(),
                    args: self.lower_args(&call.args),
                }
            }
            DispatchInfo::Unresolved { trait_name } => {
                // Resolve based on bindings
                if let Some(binding) = self.bindings.lookup(trait_name) {
                    MirInstruction::DirectCall {
                        func: format!("{}::{}", binding.impl_type, call.method),
                        args: self.lower_args(&call.args),
                    }
                } else {
                    MirInstruction::VirtualCall {
                        receiver: self.lower_expr(&call.receiver),
                        trait_name: trait_name.clone(),
                        method: call.method.clone(),
                        args: self.lower_args(&call.args),
                    }
                }
            }
        }
    }
}
```

### Step 5.3: Codegen for Both Dispatch Modes

**File:** `src/compiler/src/codegen/instr/methods.rs`

```rust
impl CodeGenerator {
    fn emit_direct_call(&mut self, func: &str, args: &[Value]) -> Value {
        // Look up function in symbol table
        let func_ptr = self.get_function(func);
        // Emit call instruction
        self.builder.call(func_ptr, args)
    }

    fn emit_virtual_call(
        &mut self,
        receiver: Value,
        trait_name: &str,
        method: &str,
        args: &[Value],
    ) -> Value {
        // Load vtable from receiver
        let vtable_ptr = self.emit_load_vtable(receiver);
        // Look up method offset
        let method_offset = self.get_vtable_offset(trait_name, method);
        // Load method pointer from vtable
        let method_ptr = self.builder.load(
            self.builder.gep(vtable_ptr, &[method_offset])
        );
        // Emit indirect call
        let all_args: Vec<_> = std::iter::once(receiver).chain(args.iter().cloned()).collect();
        self.builder.call_indirect(method_ptr, &all_args)
    }
}
```

---

## Phase 6: Build System Integration

**Goal:** Add CLI flags and integrate with build pipeline.

### Step 6.1: CLI Flags

**File:** `src/driver/src/main.rs`

```rust
#[derive(Parser)]
struct Cli {
    // ... existing args ...

    /// Interface dispatch mode: auto, dyn, static
    #[arg(long, default_value = "auto")]
    iface_dispatch: String,

    /// Generate Lean4 verification code
    #[arg(long)]
    gen_lean: bool,

    /// Output directory for generated Lean code
    #[arg(long, default_value = "verification/generated")]
    lean_output: PathBuf,

    /// Verify generated Lean code (requires Lean4)
    #[arg(long)]
    verify: bool,
}
```

### Step 6.2: Integration

**File:** `src/driver/src/runner.rs`

```rust
pub fn run_with_options(options: &RunOptions) -> Result<(), Error> {
    // Parse source
    let modules = parse_project(&options.source)?;

    // Generate Lean if requested
    if options.gen_lean {
        let generator = LeanGenerator::new(
            options.lean_output.clone(),
            project_name(&options.source),
        );
        generator.generate(&modules)?;
    }

    // Verify if requested
    if options.verify {
        verify_lean(&options.lean_output)?;
    }

    // Set dispatch mode
    let dispatch_mode = match options.iface_dispatch.as_str() {
        "static" => DispatchMode::Static,
        "dyn" => DispatchMode::Dynamic,
        _ => DispatchMode::Auto,
    };

    // Compile with dispatch mode
    compile_with_dispatch(&modules, dispatch_mode)?;

    Ok(())
}

fn verify_lean(output_dir: &Path) -> Result<(), Error> {
    use std::process::Command;

    let status = Command::new("lake")
        .current_dir(output_dir)
        .arg("build")
        .status()?;

    if !status.success() {
        return Err(Error::VerificationFailed);
    }

    Ok(())
}
```

---

## Testing Strategy

### Unit Tests (per phase)

| Phase | Test Focus | Location |
|-------|-----------|----------|
| 1 | Parsing bind statements | `src/parser/tests/` |
| 2 | Lean code generation | `src/compiler/src/lean_gen/tests/` |
| 3 | Binding type checking | `src/type/tests/` |
| 4 | Interpreter dispatch | `src/driver/tests/interpreter_*.rs` |
| 5 | Codegen correctness | `src/driver/tests/runner_*.rs` |
| 6 | CLI integration | `src/driver/tests/` |

### Integration Tests

**File:** `tests/static_polymorphism_tests.rs`

```rust
#[test]
fn test_static_dispatch_correctness() {
    // Create test project with binding
    // Verify correct implementation is called
}

#[test]
fn test_dynamic_dispatch_fallback() {
    // Create test without binding
    // Verify dynamic dispatch works
}

#[test]
fn test_binding_error_on_wrong_type() {
    // Attempt to use wrong implementation
    // Verify compile error
}

#[test]
fn test_lean_generation_and_verification() {
    // Generate Lean from test Simple code
    // Run lake build
    // Verify success
}
```

---

## Dependencies

### Required

- Lean 4 (for verification, optional at runtime)
- Existing Simple compiler infrastructure

### New Crates

None required - uses existing dependencies.

---

## Risk Assessment

| Risk | Mitigation |
|------|------------|
| Breaking existing code | Extensive test coverage, feature flag |
| Performance regression | Benchmark static vs dynamic dispatch |
| Lean4 toolchain issues | Make verification optional |
| Complex edge cases | Start with simple trait scenarios |

---

## Success Criteria

1. **Parser**: `bind` statements parse correctly
2. **Lean Gen**: Valid Lean4 code generated from Simple
3. **Type Checker**: Binding violations caught at compile time
4. **Interpreter**: Static/dynamic dispatch works correctly
5. **Codegen**: Generated code has correct dispatch semantics
6. **Verification**: Generated Lean proofs compile with `lake build`
