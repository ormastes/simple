//! Lean code emitter.
//!
//! Handles the final emission of Lean 4 code, including:
//! - Module header with imports
//! - Type definitions
//! - Function definitions
//! - Theorem statements
//! - Pretty printing with proper indentation

use super::contracts::{LeanClassInvariant, LeanTheorem};
use super::functions::LeanFunction;
use super::traits::{LeanBinding, LeanClass, LeanInstance};
use super::types::LeanType;

/// User-provided Lean 4 block (from lean{} syntax in Simple source)
#[derive(Debug, Clone)]
pub struct LeanUserBlock {
    /// Optional import path for external Lean file
    pub import_path: Option<String>,
    /// Inline Lean 4 code
    pub code: String,
    /// Context where the block was defined (e.g., "module", "fn:factorial")
    pub context: String,
}

/// A complete Lean module
#[derive(Debug, Clone)]
pub struct LeanModule {
    /// Module name
    pub name: String,
    /// Import statements
    pub imports: Vec<String>,
    /// Type definitions (structures and inductives)
    pub types: Vec<LeanType>,
    /// Function definitions
    pub functions: Vec<LeanFunction>,
    /// Theorems
    pub theorems: Vec<LeanTheorem>,
    /// Class invariants
    pub invariants: Vec<LeanClassInvariant>,
    /// Type classes (from traits)
    pub classes: Vec<LeanClass>,
    /// Instances (from impl blocks)
    pub instances: Vec<LeanInstance>,
    /// Interface bindings (static dispatch)
    pub bindings: Vec<LeanBinding>,
    /// User-provided Lean blocks (from lean{} syntax)
    pub user_blocks: Vec<LeanUserBlock>,
}

/// Lean code emitter
pub struct LeanEmitter {
    /// Output buffer
    output: String,
    /// Current indentation level
    indent: usize,
    /// Indentation string (spaces per level)
    indent_str: String,
}

impl LeanEmitter {
    /// Create a new emitter
    pub fn new() -> Self {
        Self {
            output: String::new(),
            indent: 0,
            indent_str: "  ".to_string(),
        }
    }

    /// Create an emitter with custom indentation
    pub fn with_indent(indent_str: &str) -> Self {
        Self {
            output: String::new(),
            indent: 0,
            indent_str: indent_str.to_string(),
        }
    }

    /// Emit module header with imports
    pub fn emit_header(&mut self, module_name: &str) {
        self.output.push_str(&format!(
            "/-\n  Generated from Simple language\n  Module: {}\n-/\n\n",
            module_name
        ));

        // Standard imports for verified code
        self.output.push_str("import Mathlib.Tactic\n");
        self.output.push_str("import Mathlib.Data.Int.Basic\n");
        self.output.push_str("import Mathlib.Data.Nat.Basic\n");
        self.output.push_str("\n");

        self.output.push_str(&format!("namespace {}\n\n", module_name));
    }

    /// Emit a type definition
    pub fn emit_type(&mut self, ty: &LeanType) {
        match ty {
            LeanType::Structure { .. } => {
                if let Some(def) = ty.emit_structure() {
                    self.output.push_str(&def);
                    self.output.push('\n');
                }
            }
            LeanType::Inductive { .. } => {
                if let Some(def) = ty.emit_inductive() {
                    self.output.push_str(&def);
                    self.output.push('\n');
                }
            }
            LeanType::Mixin { .. } => {
                if let Some(def) = ty.emit_mixin() {
                    self.output.push_str(&def);
                    self.output.push('\n');
                }
            }
            LeanType::Subtype { .. } => {
                if let Some(def) = ty.emit_subtype() {
                    self.output.push_str(&def);
                    self.output.push('\n');
                }
            }
            _ => {
                // Primitive and named types don't need definitions
            }
        }
    }

    /// Emit a function definition
    pub fn emit_function(&mut self, func: &LeanFunction) {
        self.output.push_str(&func.to_lean());
        self.output.push('\n');
    }

    /// Emit a function as an axiom
    pub fn emit_axiom(&mut self, func: &LeanFunction) {
        self.output.push_str(&func.to_axiom());
        self.output.push('\n');
    }

    /// Emit a theorem
    pub fn emit_theorem(&mut self, theorem: &LeanTheorem, use_sorry: bool) {
        self.output.push_str(&theorem.to_lean(use_sorry));
        self.output.push('\n');
    }

    /// Emit a theorem as an axiom
    pub fn emit_theorem_axiom(&mut self, theorem: &LeanTheorem) {
        self.output.push_str(&theorem.to_axiom());
        self.output.push('\n');
    }

    /// Emit a class invariant
    pub fn emit_invariant(&mut self, inv: &LeanClassInvariant) {
        self.output.push_str(&inv.to_lean());
        self.output.push('\n');
    }

    /// Emit a Lean type class (from Simple trait)
    pub fn emit_class(&mut self, class: &LeanClass) {
        self.output.push_str(&class.to_lean());
        self.output.push('\n');
    }

    /// Emit a Lean instance (from Simple impl block)
    pub fn emit_instance(&mut self, instance: &LeanInstance, use_sorry: bool) {
        if use_sorry {
            self.output.push_str(&instance.to_lean_with_sorry());
        } else {
            self.output.push_str(&instance.to_lean());
        }
        self.output.push('\n');
    }

    /// Emit an interface binding (static dispatch)
    pub fn emit_binding(&mut self, binding: &LeanBinding) {
        self.output.push_str(&binding.to_lean());
        self.output.push('\n');
    }

    /// Emit a binding validity theorem
    pub fn emit_binding_theorem(&mut self, binding: &LeanBinding) {
        self.output.push_str(&binding.to_validity_theorem());
        self.output.push('\n');
    }

    /// Emit a user-provided Lean block
    pub fn emit_user_block(&mut self, block: &LeanUserBlock) {
        // Emit context as a comment
        self.emit_comment(&format!("User-provided Lean code (context: {})", block.context));

        // Emit import if present
        if let Some(ref import_path) = block.import_path {
            // Convert path to Lean import format
            let lean_import = import_path.trim_end_matches(".lean").replace('/', ".");
            self.emit_line(&format!("-- import «{}»", lean_import));
        }

        // Emit inline code if present
        if !block.code.is_empty() {
            // Emit code with proper indentation
            for line in block.code.lines() {
                self.emit_line(line);
            }
        }
        self.emit_blank();
    }

    /// Emit a raw string
    pub fn emit_raw(&mut self, s: &str) {
        self.output.push_str(s);
    }

    /// Emit an indented line
    pub fn emit_line(&mut self, s: &str) {
        for _ in 0..self.indent {
            self.output.push_str(&self.indent_str);
        }
        self.output.push_str(s);
        self.output.push('\n');
    }

    /// Emit a blank line
    pub fn emit_blank(&mut self) {
        self.output.push('\n');
    }

    /// Emit a comment
    pub fn emit_comment(&mut self, comment: &str) {
        self.emit_line(&format!("-- {}", comment));
    }

    /// Emit a documentation comment
    pub fn emit_doc(&mut self, doc: &str) {
        for line in doc.lines() {
            self.emit_line(&format!("/-- {} -/", line));
        }
    }

    /// Emit a section header
    pub fn emit_section(&mut self, name: &str) {
        self.emit_blank();
        self.emit_line(&format!("section {}", name));
        self.indent += 1;
    }

    /// End a section
    pub fn end_section(&mut self, name: &str) {
        self.indent = self.indent.saturating_sub(1);
        self.emit_line(&format!("end {}", name));
        self.emit_blank();
    }

    /// Emit namespace footer
    pub fn emit_footer(&mut self, module_name: &str) {
        self.output.push_str(&format!("\nend {}\n", module_name));
    }

    /// Finish and return the generated code
    pub fn finish(self) -> String {
        self.output
    }

    /// Finish with namespace footer
    pub fn finish_with_footer(mut self, module_name: &str) -> String {
        self.emit_footer(module_name);
        self.output
    }

    /// Emit a complete module
    pub fn emit_module(&mut self, module: &LeanModule, use_sorry: bool) {
        self.emit_header(&module.name);

        // Emit imports
        for import in &module.imports {
            self.emit_line(&format!("import {}", import));
        }
        if !module.imports.is_empty() {
            self.emit_blank();
        }

        // Emit types
        if !module.types.is_empty() {
            self.emit_comment("Type definitions");
            for ty in &module.types {
                self.emit_type(ty);
            }
            self.emit_blank();
        }

        // Emit type classes (from traits)
        if !module.classes.is_empty() {
            self.emit_comment("Type classes");
            for class in &module.classes {
                self.emit_class(class);
            }
            self.emit_blank();
        }

        // Emit instances (from impl blocks)
        if !module.instances.is_empty() {
            self.emit_comment("Instances");
            for instance in &module.instances {
                self.emit_instance(instance, use_sorry);
            }
            self.emit_blank();
        }

        // Emit interface bindings (static dispatch)
        if !module.bindings.is_empty() {
            self.emit_comment("Interface bindings");
            for binding in &module.bindings {
                self.emit_binding(binding);
                self.emit_binding_theorem(binding);
            }
            self.emit_blank();
        }

        // Emit class invariants
        if !module.invariants.is_empty() {
            self.emit_comment("Class invariants");
            for inv in &module.invariants {
                self.emit_invariant(inv);
            }
            self.emit_blank();
        }

        // Emit functions
        if !module.functions.is_empty() {
            self.emit_comment("Function definitions");
            for func in &module.functions {
                self.emit_function(func);
            }
            self.emit_blank();
        }

        // Emit theorems
        if !module.theorems.is_empty() {
            self.emit_comment("Theorems");
            for theorem in &module.theorems {
                self.emit_theorem(theorem, use_sorry);
            }
            self.emit_blank();
        }

        // Emit user-provided Lean blocks (from lean{} syntax)
        if !module.user_blocks.is_empty() {
            self.emit_comment("User-provided Lean code");
            for block in &module.user_blocks {
                self.emit_user_block(block);
            }
        }

        self.emit_footer(&module.name);
    }
}

impl Default for LeanEmitter {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::super::expressions::{LeanExpr, LeanLit};
    use super::super::types::LeanType;
    use super::*;

    #[test]
    fn test_emit_header() {
        let mut emitter = LeanEmitter::new();
        emitter.emit_header("TestModule");

        let output = emitter.finish();
        assert!(output.contains("Generated from Simple language"));
        assert!(output.contains("Module: TestModule"));
        assert!(output.contains("namespace TestModule"));
    }

    #[test]
    fn test_emit_structure() {
        let mut emitter = LeanEmitter::new();

        let ty = LeanType::Structure {
            name: "Point".to_string(),
            fields: vec![
                ("x".to_string(), LeanType::Primitive("Int".to_string())),
                ("y".to_string(), LeanType::Primitive("Int".to_string())),
            ],
            deriving: vec!["Repr".to_string()],
        };

        emitter.emit_type(&ty);

        let output = emitter.finish();
        assert!(output.contains("structure Point where"));
        assert!(output.contains("x : Int"));
        assert!(output.contains("y : Int"));
        assert!(output.contains("deriving Repr"));
    }

    #[test]
    fn test_emit_inductive() {
        let mut emitter = LeanEmitter::new();

        let ty = LeanType::Inductive {
            name: "Color".to_string(),
            variants: vec![
                ("Red".to_string(), vec![]),
                ("Green".to_string(), vec![]),
                ("Blue".to_string(), vec![]),
                (
                    "Rgb".to_string(),
                    vec![
                        LeanType::Primitive("Nat".to_string()),
                        LeanType::Primitive("Nat".to_string()),
                        LeanType::Primitive("Nat".to_string()),
                    ],
                ),
            ],
            deriving: vec!["Repr".to_string(), "DecidableEq".to_string()],
        };

        emitter.emit_type(&ty);

        let output = emitter.finish();
        assert!(output.contains("inductive Color where"));
        assert!(output.contains("| Red : Color"));
        assert!(output.contains("| Rgb : Nat → Nat → Nat → Color"));
    }

    #[test]
    fn test_emit_function() {
        let mut emitter = LeanEmitter::new();

        let func = LeanFunction {
            name: "add".to_string(),
            type_params: vec![],
            params: vec![
                ("x".to_string(), LeanType::Primitive("Int".to_string())),
                ("y".to_string(), LeanType::Primitive("Int".to_string())),
            ],
            return_type: LeanType::Primitive("Int".to_string()),
            body: Some(LeanExpr::BinOp {
                op: "+".to_string(),
                left: Box::new(LeanExpr::Var("x".to_string())),
                right: Box::new(LeanExpr::Var("y".to_string())),
            }),
            is_partial: false,
            doc: None,
            termination_by: None,
            is_ghost: false,
        };

        emitter.emit_function(&func);

        let output = emitter.finish();
        assert!(output.contains("def add (x : Int) (y : Int) : Int :="));
        assert!(output.contains("(x + y)"));
    }

    #[test]
    fn test_emit_complete_module() {
        let module = LeanModule {
            name: "Math".to_string(),
            imports: vec![],
            types: vec![LeanType::Structure {
                name: "Vector2".to_string(),
                fields: vec![
                    ("x".to_string(), LeanType::Primitive("Float".to_string())),
                    ("y".to_string(), LeanType::Primitive("Float".to_string())),
                ],
                deriving: vec!["Repr".to_string()],
            }],
            functions: vec![LeanFunction {
                name: "magnitude".to_string(),
                type_params: vec![],
                params: vec![("v".to_string(), LeanType::Named("Vector2".to_string()))],
                return_type: LeanType::Primitive("Float".to_string()),
                body: Some(LeanExpr::Sorry),
                is_partial: false,
                doc: Some("Calculate vector magnitude".to_string()),
                termination_by: None,
                is_ghost: false,
            }],
            theorems: vec![],
            invariants: vec![],
            classes: vec![],
            instances: vec![],
            bindings: vec![],
            user_blocks: vec![],
        };

        let mut emitter = LeanEmitter::new();
        emitter.emit_module(&module, true);

        let output = emitter.finish();
        assert!(output.contains("namespace Math"));
        assert!(output.contains("structure Vector2 where"));
        assert!(output.contains("def magnitude"));
        assert!(output.contains("end Math"));
    }
}
