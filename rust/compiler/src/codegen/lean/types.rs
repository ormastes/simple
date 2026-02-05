//! Lean type translation.
//!
//! Translates Simple types to Lean 4 types:
//! - Simple classes/structs → Lean `structure`
//! - Simple enums → Lean `inductive`
//! - Primitive types → Lean builtins (Int, Bool, String)

use crate::hir::{HirType, Signedness, TypeId, TypeRegistry};
use crate::CompileError;

/// A Lean type representation
#[derive(Debug, Clone)]
pub enum LeanType {
    /// Primitive Lean type (Int, Nat, Bool, String)
    Primitive(String),
    /// Named type reference
    Named(String),
    /// Structure definition
    Structure {
        name: String,
        fields: Vec<(String, LeanType)>,
        deriving: Vec<String>,
    },
    /// Inductive type definition (enum)
    Inductive {
        name: String,
        variants: Vec<(String, Vec<LeanType>)>,
        deriving: Vec<String>,
    },
    /// Function type (A → B)
    Function {
        params: Vec<LeanType>,
        result: Box<LeanType>,
    },
    /// Optional type (Option A)
    Optional(Box<LeanType>),
    /// List type (List A)
    List(Box<LeanType>),
    /// Tuple type (A × B)
    Tuple(Vec<LeanType>),
    /// Mixin definition (reusable structure extension)
    Mixin {
        name: String,
        fields: Vec<(String, LeanType)>,
        methods: Vec<(String, LeanType)>,
        type_params: Vec<String>,
    },
    /// Subtype/Refinement type (e.g., {x : Int // x > 0})
    /// Generated from Simple's `type Pos = i64 where self > 0`
    Subtype {
        name: String,
        base_type: Box<LeanType>,
        /// Predicate as a Lean proposition string
        predicate: String,
    },
}

impl LeanType {
    /// Convert to Lean syntax string
    pub fn to_lean(&self) -> String {
        match self {
            LeanType::Primitive(name) => name.clone(),
            LeanType::Named(name) => name.clone(),
            LeanType::Structure { name, .. } => name.clone(),
            LeanType::Inductive { name, .. } => name.clone(),
            LeanType::Mixin { name, .. } => name.clone(),
            LeanType::Subtype { name, .. } => name.clone(),
            LeanType::Function { params, result } => {
                let params_str = params.iter().map(|p| p.to_lean()).collect::<Vec<_>>().join(" → ");
                format!("{} → {}", params_str, result.to_lean())
            }
            LeanType::Optional(inner) => format!("Option {}", inner.to_lean()),
            LeanType::List(inner) => format!("List {}", inner.to_lean()),
            LeanType::Tuple(types) => {
                let types_str = types.iter().map(|t| t.to_lean()).collect::<Vec<_>>().join(" × ");
                format!("({})", types_str)
            }
        }
    }

    /// Emit subtype definition
    /// Generates: def TypeName : Type := {x : BaseType // predicate}
    pub fn emit_subtype(&self) -> Option<String> {
        match self {
            LeanType::Subtype {
                name,
                base_type,
                predicate,
            } => Some(format!(
                "/-- Refinement type: {} --/\ndef {} : Type := {{x : {} // {}}}\n",
                name,
                name,
                base_type.to_lean(),
                predicate
            )),
            _ => None,
        }
    }

    /// Emit structure definition
    pub fn emit_structure(&self) -> Option<String> {
        match self {
            LeanType::Structure { name, fields, deriving } => {
                let mut out = format!("structure {} where\n", name);
                for (field_name, field_type) in fields {
                    out.push_str(&format!("  {} : {}\n", field_name, field_type.to_lean()));
                }
                if !deriving.is_empty() {
                    out.push_str(&format!("deriving {}\n", deriving.join(", ")));
                }
                Some(out)
            }
            _ => None,
        }
    }

    /// Emit mixin definition
    pub fn emit_mixin(&self) -> Option<String> {
        match self {
            LeanType::Mixin {
                name,
                fields,
                methods,
                type_params,
            } => {
                let mut out = String::new();

                // Generate type parameter list
                let params = if type_params.is_empty() {
                    String::new()
                } else {
                    format!(
                        " {}",
                        type_params
                            .iter()
                            .map(|p| format!("({} : Type)", p))
                            .collect::<Vec<_>>()
                            .join(" ")
                    )
                };

                out.push_str(&format!("/-- Mixin: {} --/\n", name));
                out.push_str(&format!("structure {}{} where\n", name, params));

                // Emit fields
                for (field_name, field_type) in fields {
                    out.push_str(&format!("  {} : {}\n", field_name, field_type.to_lean()));
                }

                // Emit method signatures as function fields
                for (method_name, method_type) in methods {
                    out.push_str(&format!("  {} : {}\n", method_name, method_type.to_lean()));
                }

                out.push_str("deriving Repr\n");
                Some(out)
            }
            _ => None,
        }
    }

    /// Emit inductive definition
    pub fn emit_inductive(&self) -> Option<String> {
        match self {
            LeanType::Inductive {
                name,
                variants,
                deriving,
            } => {
                let mut out = format!("inductive {} where\n", name);
                for (variant_name, variant_types) in variants {
                    if variant_types.is_empty() {
                        out.push_str(&format!("  | {} : {}\n", variant_name, name));
                    } else {
                        let types_str = variant_types
                            .iter()
                            .map(|t| t.to_lean())
                            .collect::<Vec<_>>()
                            .join(" → ");
                        out.push_str(&format!("  | {} : {} → {}\n", variant_name, types_str, name));
                    }
                }
                if !deriving.is_empty() {
                    out.push_str(&format!("deriving {}\n", deriving.join(", ")));
                }
                Some(out)
            }
            _ => None,
        }
    }
}

/// Type translator for Simple → Lean conversion
pub struct TypeTranslator<'a> {
    registry: &'a TypeRegistry,
}

impl<'a> TypeTranslator<'a> {
    /// Create a new type translator
    pub fn new(registry: &'a TypeRegistry) -> Self {
        Self { registry }
    }

    /// Translate a Simple type to Lean
    pub fn translate(&self, type_id: TypeId) -> Result<LeanType, CompileError> {
        let ty = self
            .registry
            .get(type_id)
            .ok_or_else(|| crate::error::factory::unknown_type_id(&type_id))?;

        self.translate_hir_type(ty)
    }

    /// Translate a HIR type to Lean
    pub fn translate_hir_type(&self, ty: &HirType) -> Result<LeanType, CompileError> {
        match ty {
            HirType::Void => Ok(LeanType::Primitive("Unit".to_string())),
            HirType::Bool => Ok(LeanType::Primitive("Bool".to_string())),
            HirType::Int { signedness, .. } => {
                // Use Int for signed, Nat for unsigned
                if signedness.is_signed() {
                    Ok(LeanType::Primitive("Int".to_string()))
                } else {
                    Ok(LeanType::Primitive("Nat".to_string()))
                }
            }
            HirType::Float { .. } => Ok(LeanType::Primitive("Float".to_string())),
            HirType::String => Ok(LeanType::Primitive("String".to_string())),
            HirType::Nil => Ok(LeanType::Primitive("Unit".to_string())),
            HirType::Struct { name, fields, .. } => {
                let lean_fields: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|(n, tid)| self.translate(*tid).map(|t| (n.clone(), t)))
                    .collect();
                Ok(LeanType::Structure {
                    name: self.to_lean_name(name),
                    fields: lean_fields?,
                    deriving: vec!["Repr".to_string()],
                })
            }
            HirType::Enum { name, variants, .. } => {
                let lean_variants: Result<Vec<_>, _> = variants
                    .iter()
                    .map(|(n, types_opt)| {
                        if let Some(types) = types_opt {
                            let lean_types: Result<Vec<_>, _> = types.iter().map(|tid| self.translate(*tid)).collect();
                            lean_types.map(|t| (self.to_lean_name(n), t))
                        } else {
                            Ok((self.to_lean_name(n), vec![]))
                        }
                    })
                    .collect();
                Ok(LeanType::Inductive {
                    name: self.to_lean_name(name),
                    variants: lean_variants?,
                    deriving: vec!["Repr".to_string(), "DecidableEq".to_string()],
                })
            }
            HirType::Mixin {
                name,
                type_params,
                fields,
                methods,
                ..
            } => {
                let lean_fields: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|(n, tid)| self.translate(*tid).map(|t| (n.clone(), t)))
                    .collect();
                let lean_methods: Result<Vec<_>, _> = methods
                    .iter()
                    .map(|m| {
                        let params: Result<Vec<_>, _> = m.params.iter().map(|tid| self.translate(*tid)).collect();
                        let ret = self.translate(m.ret)?;
                        params.map(|p| {
                            (
                                self.to_lean_name(&m.name),
                                LeanType::Function {
                                    params: p,
                                    result: Box::new(ret),
                                },
                            )
                        })
                    })
                    .collect();
                Ok(LeanType::Mixin {
                    name: self.to_lean_name(name),
                    fields: lean_fields?,
                    methods: lean_methods?,
                    type_params: type_params.clone(),
                })
            }
            HirType::Array { element, .. } => {
                let inner = self.translate(*element)?;
                Ok(LeanType::List(Box::new(inner)))
            }
            HirType::Tuple(elements) => {
                let lean_elements: Result<Vec<_>, _> = elements.iter().map(|tid| self.translate(*tid)).collect();
                Ok(LeanType::Tuple(lean_elements?))
            }
            HirType::Function { params, ret } => {
                let lean_params: Result<Vec<_>, _> = params.iter().map(|tid| self.translate(*tid)).collect();
                let lean_ret = self.translate(*ret)?;
                Ok(LeanType::Function {
                    params: lean_params?,
                    result: Box::new(lean_ret),
                })
            }
            HirType::Pointer { inner, .. } => {
                // Pointers become the underlying type in verification
                self.translate(*inner)
            }
            HirType::Simd { element, .. } => {
                // SIMD vectors become lists in verification
                let inner = self.translate(*element)?;
                Ok(LeanType::List(Box::new(inner)))
            }
            HirType::UnitType { name, repr, .. } => {
                // Unit types become their representation type with a wrapper
                let inner = self.translate(*repr)?;
                Ok(LeanType::Named(self.to_lean_name(name)))
            }
            HirType::Union { variants } => {
                // Union types become a sum type
                if variants.len() == 2 {
                    // For binary unions, use Either
                    let left = self.translate(variants[0])?;
                    let right = self.translate(variants[1])?;
                    Ok(LeanType::Named(format!("Sum {} {}", left.to_lean(), right.to_lean())))
                } else {
                    // For n-ary unions, generate an inductive
                    Ok(LeanType::Primitive("Unit".to_string())) // Placeholder
                }
            }
            HirType::Promise { inner } => {
                // Promise types become IO monads in Lean
                let inner_type = self.translate(*inner)?;
                Ok(LeanType::Named(format!("IO ({})", inner_type.to_lean())))
            }
            HirType::ExternClass { name } => {
                // Extern classes are opaque types in Lean
                Ok(LeanType::Primitive(name.clone()))
            }
            HirType::Unknown => Ok(LeanType::Primitive("Unit".to_string())),
            HirType::Any => Ok(LeanType::Primitive("Unit".to_string())),
            HirType::Char => Ok(LeanType::Primitive("Char".to_string())),
        }
    }

    /// Translate a type definition
    pub fn translate_type_def(&self, name: &str, ty: &HirType) -> Result<LeanType, CompileError> {
        match ty {
            HirType::Struct { fields, .. } => {
                let lean_fields: Result<Vec<_>, _> = fields
                    .iter()
                    .map(|(n, tid)| self.translate(*tid).map(|t| (n.clone(), t)))
                    .collect();
                Ok(LeanType::Structure {
                    name: self.to_lean_name(name),
                    fields: lean_fields?,
                    deriving: vec!["Repr".to_string()],
                })
            }
            HirType::Enum { variants, .. } => {
                let lean_variants: Result<Vec<_>, _> = variants
                    .iter()
                    .map(|(n, types_opt)| {
                        if let Some(types) = types_opt {
                            let lean_types: Result<Vec<_>, _> = types.iter().map(|tid| self.translate(*tid)).collect();
                            lean_types.map(|t| (self.to_lean_name(n), t))
                        } else {
                            Ok((self.to_lean_name(n), vec![]))
                        }
                    })
                    .collect();
                Ok(LeanType::Inductive {
                    name: self.to_lean_name(name),
                    variants: lean_variants?,
                    deriving: vec!["Repr".to_string(), "DecidableEq".to_string()],
                })
            }
            _ => self.translate_hir_type(ty),
        }
    }

    /// Convert a Simple name to Lean naming convention (PascalCase for types)
    fn to_lean_name(&self, name: &str) -> String {
        super::naming::to_pascal_case(name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_primitive_types() {
        let registry = TypeRegistry::new();
        let translator = TypeTranslator::new(&registry);

        let lean_int = translator
            .translate_hir_type(&HirType::Int {
                bits: 64,
                signedness: Signedness::Signed,
            })
            .unwrap();
        assert_eq!(lean_int.to_lean(), "Int");

        let lean_nat = translator
            .translate_hir_type(&HirType::Int {
                bits: 64,
                signedness: Signedness::Unsigned,
            })
            .unwrap();
        assert_eq!(lean_nat.to_lean(), "Nat");

        let lean_bool = translator.translate_hir_type(&HirType::Bool).unwrap();
        assert_eq!(lean_bool.to_lean(), "Bool");

        let lean_string = translator.translate_hir_type(&HirType::String).unwrap();
        assert_eq!(lean_string.to_lean(), "String");
    }

    #[test]
    fn test_lean_name_conversion() {
        let registry = TypeRegistry::new();
        let translator = TypeTranslator::new(&registry);

        assert_eq!(translator.to_lean_name("my_type"), "MyType");
        assert_eq!(translator.to_lean_name("simple"), "Simple");
        assert_eq!(translator.to_lean_name("ref_capability"), "RefCapability");
    }
}
