//! Lean function translation.
//!
//! Translates Simple functions to Lean 4 definitions:
//! - Verified functions → Lean `def` with explicit types
//! - Pure functions → `def` without IO monad
//! - Effectful functions → wrapped in appropriate monad

use super::expressions::{ExprTranslator, LeanExpr};
use super::types::{LeanType, TypeTranslator};
use crate::hir::HirFunction;
use crate::CompileError;

/// A Lean function definition
#[derive(Debug, Clone)]
pub struct LeanFunction {
    /// Function name
    pub name: String,
    /// Type parameters (generics)
    pub type_params: Vec<String>,
    /// Parameters with types
    pub params: Vec<(String, LeanType)>,
    /// Return type
    pub return_type: LeanType,
    /// Function body (None for axioms)
    pub body: Option<LeanExpr>,
    /// Whether this is a partial function
    pub is_partial: bool,
    /// Documentation comment
    pub doc: Option<String>,
    /// Termination measure for recursive functions (from decreases: clause)
    /// Generates `termination_by` clause in Lean output
    pub termination_by: Option<LeanExpr>,
}

impl LeanFunction {
    /// Emit as Lean definition
    pub fn to_lean(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            for line in doc.lines() {
                out.push_str(&format!("/-- {} -/\n", line));
            }
        }

        // Partial annotation if needed
        if self.is_partial {
            out.push_str("partial ");
        }

        // Function signature
        out.push_str("def ");
        out.push_str(&self.name);

        // Type parameters
        if !self.type_params.is_empty() {
            out.push_str(" {");
            out.push_str(&self.type_params.join(" "));
            out.push_str("}");
        }

        // Parameters
        for (param_name, param_type) in &self.params {
            out.push_str(&format!(" ({} : {})", param_name, param_type.to_lean()));
        }

        // Return type
        out.push_str(&format!(" : {} :=\n", self.return_type.to_lean()));

        // Body
        if let Some(ref body) = self.body {
            out.push_str(&format!("  {}\n", body.to_lean()));
        } else {
            out.push_str("  sorry\n");
        }

        // Termination measure (from decreases: clause)
        if let Some(ref term_expr) = self.termination_by {
            out.push_str(&format!("termination_by {}\n", term_expr.to_lean()));
        }

        out
    }

    /// Emit as axiom (for external/native functions)
    pub fn to_axiom(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            for line in doc.lines() {
                out.push_str(&format!("/-- {} -/\n", line));
            }
        }

        out.push_str("axiom ");
        out.push_str(&self.name);

        // Type parameters
        if !self.type_params.is_empty() {
            out.push_str(" {");
            out.push_str(&self.type_params.join(" "));
            out.push_str("}");
        }

        // Parameters as function type
        for (_, param_type) in &self.params {
            out.push_str(&format!(" : {} →", param_type.to_lean()));
        }

        // Return type
        out.push_str(&format!(" {}\n", self.return_type.to_lean()));

        out
    }
}

/// Function translator for Simple → Lean conversion
pub struct FunctionTranslator<'a> {
    type_translator: &'a TypeTranslator<'a>,
}

impl<'a> FunctionTranslator<'a> {
    /// Create a new function translator
    pub fn new(type_translator: &'a TypeTranslator<'a>) -> Self {
        Self { type_translator }
    }

    /// Translate a Simple function to Lean
    pub fn translate_function(&self, func: &HirFunction) -> Result<LeanFunction, CompileError> {
        // Translate parameters (filter out ghost)
        let params: Result<Vec<(String, LeanType)>, CompileError> = func
            .params
            .iter()
            .filter(|p| !p.is_ghost)
            .map(|p| {
                let lean_type = self.type_translator.translate(p.ty)?;
                Ok((self.to_lean_name(&p.name), lean_type))
            })
            .collect();

        // Translate return type
        let return_type = self.type_translator.translate(func.return_type)?;

        // Combine params and locals for expression translation
        let all_locals: Vec<_> = func.params.iter().chain(func.locals.iter()).cloned().collect();

        // Translate body
        let expr_translator = ExprTranslator::with_locals(self.type_translator, &all_locals);
        let body = if !func.body.is_empty() {
            Some(expr_translator.translate_stmts(&func.body, &all_locals)?)
        } else {
            None
        };

        // Check if function is potentially non-terminating
        let is_partial = self.is_potentially_non_terminating(func);

        // Translate termination measure from decreases: clause
        let termination_by = if let Some(ref contract) = func.contract {
            if let Some(ref decreases) = contract.decreases {
                Some(expr_translator.translate(&decreases.condition)?)
            } else {
                None
            }
        } else {
            None
        };

        Ok(LeanFunction {
            name: self.to_lean_name(&func.name),
            type_params: vec![], // No generic support yet
            params: params?,
            return_type,
            body,
            is_partial,
            doc: None, // No doc extraction yet
            termination_by,
        })
    }

    /// Check if a function might be non-terminating
    fn is_potentially_non_terminating(&self, _func: &HirFunction) -> bool {
        // Simple heuristic: check for recursive calls
        // For now, assume all functions terminate
        false
    }

    /// Convert a Simple name to Lean naming convention (camelCase for functions)
    fn to_lean_name(&self, name: &str) -> String {
        // Convert snake_case to camelCase
        let mut result = String::new();
        let mut capitalize_next = false;

        for (i, c) in name.chars().enumerate() {
            if c == '_' {
                capitalize_next = true;
            } else if capitalize_next {
                result.push(c.to_ascii_uppercase());
                capitalize_next = false;
            } else if i == 0 {
                result.push(c.to_ascii_lowercase());
            } else {
                result.push(c);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_name_conversion() {
        let registry = crate::hir::TypeRegistry::new();
        let type_translator = TypeTranslator::new(&registry);
        let func_translator = FunctionTranslator::new(&type_translator);

        assert_eq!(func_translator.to_lean_name("my_function"), "myFunction");
        assert_eq!(func_translator.to_lean_name("get_value"), "getValue");
        assert_eq!(func_translator.to_lean_name("simple"), "simple");
    }

    #[test]
    fn test_lean_function_output() {
        use super::super::expressions::LeanLit;

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
            doc: Some("Add two integers".to_string()),
            termination_by: None,
        };

        let output = func.to_lean();
        assert!(output.contains("def add"));
        assert!(output.contains("(x : Int)"));
        assert!(output.contains(": Int :="));
    }
}
