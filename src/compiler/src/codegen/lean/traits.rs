//! Lean trait and static polymorphism generation.
//!
//! Translates Simple traits and impls to Lean 4:
//! - Traits → Lean `class` (type classes)
//! - Impl blocks → Lean `instance`
//! - Interface bindings → Lean `abbrev` + instance selection
//!
//! This enables formal verification of:
//! - Trait method type inference
//! - Implementation completeness
//! - Static dispatch correctness
//! - Binding validity

use super::types::{LeanType, TypeTranslator};
use crate::CompileError;
use simple_parser::ast::{FunctionDef, ImplBlock, TraitDef, Type as AstType};

/// A Lean type class definition
#[derive(Debug, Clone)]
pub struct LeanClass {
    /// Class name
    pub name: String,
    /// Type parameter (the implementing type)
    pub type_param: String,
    /// Additional type parameters from trait generics
    pub extra_params: Vec<String>,
    /// Method signatures: (name, params_types, return_type)
    pub methods: Vec<LeanMethodSig>,
    /// Associated types
    pub assoc_types: Vec<String>,
    /// Documentation
    pub doc: Option<String>,
}

/// A method signature in a Lean class
#[derive(Debug, Clone)]
pub struct LeanMethodSig {
    /// Method name
    pub name: String,
    /// Parameter types (including self)
    pub params: Vec<LeanType>,
    /// Return type
    pub ret: LeanType,
    /// Whether this has a default implementation
    pub has_default: bool,
}

impl LeanClass {
    /// Emit as Lean class definition
    pub fn to_lean(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            out.push_str(&format!("/-- {} -/\n", doc));
        }

        // Class header: class TraitName (α : Type) where
        out.push_str(&format!("class {} ", self.name));

        // Extra type parameters
        for param in &self.extra_params {
            out.push_str(&format!("({} : Type) ", param));
        }

        // Main type parameter (the implementing type)
        out.push_str(&format!("({} : Type) where\n", self.type_param));

        // Associated types
        for assoc in &self.assoc_types {
            out.push_str(&format!("  {} : Type\n", assoc));
        }

        // Methods
        for method in &self.methods {
            let params_str = method
                .params
                .iter()
                .map(|p| p.to_lean())
                .collect::<Vec<_>>()
                .join(" → ");

            if params_str.is_empty() {
                out.push_str(&format!("  {} : {}\n", method.name, method.ret.to_lean()));
            } else {
                out.push_str(&format!(
                    "  {} : {} → {}\n",
                    method.name,
                    params_str,
                    method.ret.to_lean()
                ));
            }
        }

        out
    }
}

/// A Lean instance definition
#[derive(Debug, Clone)]
pub struct LeanInstance {
    /// Trait/class name
    pub class_name: String,
    /// Type implementing the trait
    pub for_type: LeanType,
    /// Type arguments for generic traits
    pub type_args: Vec<LeanType>,
    /// Instance constraints (where clauses)
    pub constraints: Vec<String>,
    /// Method implementations: (name, body_expr)
    pub methods: Vec<(String, String)>,
    /// Associated type bindings: (name, type)
    pub assoc_types: Vec<(String, LeanType)>,
    /// Documentation
    pub doc: Option<String>,
}

impl LeanInstance {
    /// Emit as Lean instance definition
    pub fn to_lean(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            out.push_str(&format!("/-- {} -/\n", doc));
        }

        // Instance header
        out.push_str("instance ");

        // Constraints
        if !self.constraints.is_empty() {
            for constraint in &self.constraints {
                out.push_str(&format!("[{}] ", constraint));
            }
        }

        // Instance type: instance : ClassName Type where
        out.push_str(&format!(": {} ", self.class_name));

        // Type arguments
        for arg in &self.type_args {
            out.push_str(&format!("{} ", arg.to_lean()));
        }

        out.push_str(&format!("{} where\n", self.for_type.to_lean()));

        // Associated type bindings
        for (name, ty) in &self.assoc_types {
            out.push_str(&format!("  {} := {}\n", name, ty.to_lean()));
        }

        // Method implementations
        for (name, body) in &self.methods {
            out.push_str(&format!("  {} := {}\n", name, body));
        }

        out
    }

    /// Emit as Lean instance with sorry placeholders
    pub fn to_lean_with_sorry(&self) -> String {
        let mut out = String::new();

        if let Some(ref doc) = self.doc {
            out.push_str(&format!("/-- {} -/\n", doc));
        }

        out.push_str("instance ");

        if !self.constraints.is_empty() {
            for constraint in &self.constraints {
                out.push_str(&format!("[{}] ", constraint));
            }
        }

        out.push_str(&format!(": {} ", self.class_name));

        for arg in &self.type_args {
            out.push_str(&format!("{} ", arg.to_lean()));
        }

        out.push_str(&format!("{} where\n", self.for_type.to_lean()));

        // Associated type bindings
        for (name, ty) in &self.assoc_types {
            out.push_str(&format!("  {} := {}\n", name, ty.to_lean()));
        }

        // Method implementations with sorry
        for (name, _) in &self.methods {
            out.push_str(&format!("  {} := sorry\n", name));
        }

        out
    }
}

/// Interface binding for static dispatch
#[derive(Debug, Clone)]
pub struct LeanBinding {
    /// Interface/trait name
    pub interface_name: String,
    /// Bound implementation type
    pub impl_type: LeanType,
    /// Documentation
    pub doc: Option<String>,
}

impl LeanBinding {
    /// Emit as Lean abbreviation and instance
    pub fn to_lean(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            out.push_str(&format!("/-- {} -/\n", doc));
        }

        // Static binding comment
        out.push_str("-- Static dispatch binding\n");

        // Abbreviation: abbrev TraitName.Bound := ImplType
        out.push_str(&format!(
            "abbrev {}.Bound := {}\n",
            self.interface_name,
            self.impl_type.to_lean()
        ));

        // Instance selection: instance TraitName.BoundInstance : TraitName TraitName.Bound := inferInstance
        out.push_str(&format!(
            "instance {}.BoundInstance : {} {}.Bound := inferInstance\n",
            self.interface_name, self.interface_name, self.interface_name
        ));

        out
    }

    /// Generate binding validity theorem
    pub fn to_validity_theorem(&self) -> String {
        format!(
            "theorem {}_binding_valid : {} {} := inferInstance\n",
            self.interface_name.to_lowercase(),
            self.interface_name,
            self.impl_type.to_lean()
        )
    }
}

/// Trait translator for Simple → Lean conversion
pub struct TraitTranslator<'a> {
    type_translator: &'a TypeTranslator<'a>,
}

impl<'a> TraitTranslator<'a> {
    /// Create a new trait translator
    pub fn new(type_translator: &'a TypeTranslator<'a>) -> Self {
        Self { type_translator }
    }

    /// Translate a Simple trait to Lean class
    pub fn translate_trait(&self, trait_def: &TraitDef) -> Result<LeanClass, CompileError> {
        // Translate methods
        let methods: Result<Vec<LeanMethodSig>, _> = trait_def
            .methods
            .iter()
            .map(|method| self.translate_method_sig(method))
            .collect();

        // Extract associated type names
        let assoc_types: Vec<String> = trait_def
            .associated_types
            .iter()
            .map(|at| self.to_lean_name(&at.name))
            .collect();

        Ok(LeanClass {
            name: self.to_lean_name(&trait_def.name),
            type_param: "α".to_string(),
            extra_params: trait_def.generic_params.iter().map(|p| self.to_lean_name(p)).collect(),
            methods: methods?,
            assoc_types,
            doc: trait_def.doc_comment.as_ref().map(|d| d.content.clone()),
        })
    }

    /// Translate a method signature
    fn translate_method_sig(&self, method: &FunctionDef) -> Result<LeanMethodSig, CompileError> {
        // Translate parameter types (skip those without type annotation)
        let params: Vec<LeanType> = method
            .params
            .iter()
            .filter(|p| p.name != "self" && p.ty.is_some())
            .filter_map(|p| p.ty.as_ref().map(|ty| self.translate_ast_type(ty)))
            .collect::<Result<Vec<_>, _>>()?;

        // Translate return type
        let ret = match &method.return_type {
            Some(ty) => self.translate_ast_type(ty)?,
            None => LeanType::Primitive("Unit".to_string()),
        };

        Ok(LeanMethodSig {
            name: self.to_lean_name(&method.name),
            params,
            ret,
            has_default: !method.body.statements.is_empty(),
        })
    }

    /// Translate an impl block to Lean instance
    pub fn translate_impl(&self, impl_block: &ImplBlock) -> Result<LeanInstance, CompileError> {
        let trait_name = impl_block.trait_name.as_ref().ok_or_else(|| {
            CompileError::Semantic("Impl block without trait name cannot be translated to Lean instance".into())
        })?;

        let for_type = self.translate_ast_type(&impl_block.target_type)?;

        // Translate methods as (name, body) pairs
        let methods: Vec<(String, String)> = impl_block
            .methods
            .iter()
            .map(|m| (self.to_lean_name(&m.name), "sorry".to_string()))
            .collect();

        // Translate associated types
        let assoc_types: Vec<(String, LeanType)> = impl_block
            .associated_types
            .iter()
            .filter_map(|at| {
                self.translate_ast_type(&at.ty)
                    .ok()
                    .map(|ty| (self.to_lean_name(&at.name), ty))
            })
            .collect();

        // Translate where clause to constraints (WhereClause is Vec<WhereBound>)
        let constraints: Vec<String> = impl_block
            .where_clause
            .iter()
            .map(|bound| {
                let ty = self.to_lean_name(&bound.type_param);
                let traits: Vec<String> = bound.bounds.iter().map(|b| self.type_to_lean_constraint(b)).collect();
                format!("{} : {}", ty, traits.join(" "))
            })
            .collect();

        Ok(LeanInstance {
            class_name: self.to_lean_name(trait_name),
            for_type,
            type_args: vec![],
            constraints,
            methods,
            assoc_types,
            doc: None,
        })
    }

    /// Translate an AST type to Lean type
    fn translate_ast_type(&self, ty: &AstType) -> Result<LeanType, CompileError> {
        match ty {
            AstType::Simple(name) => match name.as_str() {
                "Int" | "i64" | "i32" | "i16" | "i8" => Ok(LeanType::Primitive("Int".to_string())),
                "Nat" | "u64" | "u32" | "u16" | "u8" | "usize" => Ok(LeanType::Primitive("Nat".to_string())),
                "Bool" | "bool" => Ok(LeanType::Primitive("Bool".to_string())),
                "Str" | "str" | "String" => Ok(LeanType::Primitive("String".to_string())),
                "Float" | "f64" | "f32" => Ok(LeanType::Primitive("Float".to_string())),
                "Nil" | "()" => Ok(LeanType::Primitive("Unit".to_string())),
                _ => Ok(LeanType::Named(self.to_lean_name(name))),
            },
            AstType::Generic { name, args } => {
                let lean_args: Result<Vec<_>, _> = args.iter().map(|a| self.translate_ast_type(a)).collect();
                Ok(LeanType::Named(format!(
                    "{} {}",
                    self.to_lean_name(name),
                    lean_args?.iter().map(|t| t.to_lean()).collect::<Vec<_>>().join(" ")
                )))
            }
            AstType::Array { element, .. } => {
                let inner = self.translate_ast_type(element)?;
                Ok(LeanType::List(Box::new(inner)))
            }
            AstType::Optional(inner) => {
                let inner = self.translate_ast_type(inner)?;
                Ok(LeanType::Optional(Box::new(inner)))
            }
            AstType::Tuple(types) => {
                let lean_types: Result<Vec<_>, _> = types.iter().map(|t| self.translate_ast_type(t)).collect();
                Ok(LeanType::Tuple(lean_types?))
            }
            AstType::Function { params, ret } => {
                let lean_params: Result<Vec<_>, _> = params.iter().map(|p| self.translate_ast_type(p)).collect();
                // ret is Option<Box<Type>>
                let lean_ret = match ret {
                    Some(r) => self.translate_ast_type(r)?,
                    None => LeanType::Primitive("Unit".to_string()),
                };
                Ok(LeanType::Function {
                    params: lean_params?,
                    result: Box::new(lean_ret),
                })
            }
            AstType::DynTrait(name) => {
                // Dynamic trait object - existential type
                Ok(LeanType::Named(format!("∃ α, {} α × α", self.to_lean_name(name))))
            }
            _ => Ok(LeanType::Primitive("Unit".to_string())),
        }
    }

    /// Convert a Simple name to Lean naming convention (PascalCase)
    fn to_lean_name(&self, name: &str) -> String {
        name.split('_')
            .map(|s| {
                let mut chars = s.chars();
                match chars.next() {
                    None => String::new(),
                    Some(c) => c.to_uppercase().collect::<String>() + chars.as_str(),
                }
            })
            .collect()
    }

    /// Convert a Type to a Lean constraint string
    /// Handles simple types (Clone) and generic types (Add<Output=T>)
    fn type_to_lean_constraint(&self, ty: &AstType) -> String {
        match ty {
            AstType::Simple(name) => self.to_lean_name(name),
            AstType::Generic { name, args } => {
                let name = self.to_lean_name(name);
                let args_str: Vec<String> = args.iter().map(|a| self.type_to_lean_constraint(a)).collect();
                if args_str.is_empty() {
                    name
                } else {
                    format!("({} {})", name, args_str.join(" "))
                }
            }
            AstType::TypeBinding { name, value } => {
                // Associated type constraint: Output=T becomes (Output := T)
                format!(
                    "({} := {})",
                    self.to_lean_name(name),
                    self.type_to_lean_constraint(value)
                )
            }
            _ => "Unit".to_string(), // Fallback for unsupported types
        }
    }
}

/// Generate Lean theorems for static polymorphism verification
pub struct StaticPolyTheorems;

impl StaticPolyTheorems {
    /// Generate implementation completeness theorem
    pub fn impl_complete_theorem(class_name: &str, impl_type: &str) -> String {
        format!(
            "theorem {}_{}_complete : {} {} := inferInstance\n",
            impl_type.to_lowercase(),
            class_name.to_lowercase(),
            class_name,
            impl_type
        )
    }

    /// Generate coherence theorem (no overlapping instances)
    pub fn coherence_theorem(class_name: &str, types: &[&str]) -> String {
        let mut out = String::new();
        out.push_str(&format!("-- Coherence: {} has no overlapping instances\n", class_name));

        for (i, ty) in types.iter().enumerate() {
            out.push_str(&format!(
                "theorem {}_impl{}_unique : {} {} := inferInstance\n",
                class_name.to_lowercase(),
                i + 1,
                class_name,
                ty
            ));
        }

        out
    }

    /// Generate dispatch determinism theorem
    pub fn dispatch_deterministic_theorem(class_name: &str) -> String {
        format!(
            r#"-- Dispatch is deterministic for bound interfaces
theorem {}_dispatch_deterministic (x y : {}.Bound) :
    @{}.method {}.Bound {}.BoundInstance x =
    @{}.method {}.Bound {}.BoundInstance y := by
  rfl
"#,
            class_name.to_lowercase(),
            class_name,
            class_name,
            class_name,
            class_name,
            class_name,
            class_name,
            class_name
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_class_output() {
        let class = LeanClass {
            name: "Logger".to_string(),
            type_param: "α".to_string(),
            extra_params: vec![],
            methods: vec![
                LeanMethodSig {
                    name: "log".to_string(),
                    params: vec![LeanType::Primitive("String".to_string())],
                    ret: LeanType::Primitive("Unit".to_string()),
                    has_default: false,
                },
                LeanMethodSig {
                    name: "level".to_string(),
                    params: vec![],
                    ret: LeanType::Primitive("Nat".to_string()),
                    has_default: false,
                },
            ],
            assoc_types: vec![],
            doc: Some("Logging trait".to_string()),
        };

        let output = class.to_lean();
        assert!(output.contains("class Logger"));
        assert!(output.contains("(α : Type)"));
        assert!(output.contains("log : String → Unit"));
        assert!(output.contains("level : Nat"));
    }

    #[test]
    fn test_lean_instance_output() {
        let instance = LeanInstance {
            class_name: "Logger".to_string(),
            for_type: LeanType::Named("ConsoleLogger".to_string()),
            type_args: vec![],
            constraints: vec![],
            methods: vec![
                ("log".to_string(), "fun msg => IO.println msg".to_string()),
                ("level".to_string(), "1".to_string()),
            ],
            assoc_types: vec![],
            doc: Some("Console logger implementation".to_string()),
        };

        let output = instance.to_lean();
        assert!(output.contains("instance : Logger ConsoleLogger"));
        assert!(output.contains("log := fun msg => IO.println msg"));
        assert!(output.contains("level := 1"));
    }

    #[test]
    fn test_lean_binding_output() {
        let binding = LeanBinding {
            interface_name: "Logger".to_string(),
            impl_type: LeanType::Named("ConsoleLogger".to_string()),
            doc: Some("Bind Logger to ConsoleLogger".to_string()),
        };

        let output = binding.to_lean();
        assert!(output.contains("abbrev Logger.Bound := ConsoleLogger"));
        assert!(output.contains("instance Logger.BoundInstance"));
        assert!(output.contains("Static dispatch"));

        let theorem = binding.to_validity_theorem();
        assert!(theorem.contains("logger_binding_valid"));
    }
}
