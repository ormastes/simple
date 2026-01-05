use super::*;
use std::collections::HashMap;

/// HIR representation of an import statement.
#[derive(Debug, Clone)]
pub struct HirImport {
    /// The module path being imported from (e.g., ["crate", "core", "Option"])
    pub from_path: Vec<String>,
    /// The items being imported (name -> optional alias)
    pub items: Vec<(String, Option<String>)>,
    /// Whether this is a glob import (import *)
    pub is_glob: bool,
    /// Whether this is a type-only import (`use type`)
    /// Type-only imports don't create runtime dependencies and are excluded
    /// from circular dependency detection.
    pub is_type_only: bool,
}

/// HIR module
#[derive(Debug)]
pub struct HirModule {
    pub name: Option<String>,
    pub types: TypeRegistry,
    pub functions: Vec<HirFunction>,
    pub globals: Vec<(String, TypeId)>,
    /// Type invariants: maps type name to its invariant
    pub type_invariants: HashMap<String, HirTypeInvariant>,
    /// Refined types: maps refined type name to its definition (CTR-020)
    pub refined_types: HashMap<String, HirRefinedType>,
    /// AOP advice declarations (#1000-1050)
    pub aop_advices: Vec<HirAopAdvice>,
    /// DI bindings (#1009-1019)
    pub di_bindings: Vec<HirDiBinding>,
    /// Architecture rules (#1026-1035)
    pub arch_rules: Vec<HirArchRule>,
    /// Mock declarations (#1020-1025)
    pub mock_decls: Vec<HirMockDecl>,
    /// Import statements for dependency tracking
    pub imports: Vec<HirImport>,
}

impl HirModule {
    pub fn new() -> Self {
        Self {
            name: None,
            types: TypeRegistry::new(),
            functions: Vec::new(),
            globals: Vec::new(),
            type_invariants: HashMap::new(),
            refined_types: HashMap::new(),
            aop_advices: Vec::new(),
            di_bindings: Vec::new(),
            arch_rules: Vec::new(),
            mock_decls: Vec::new(),
            imports: Vec::new(),
        }
    }

    /// Get the type invariant for a type by name
    pub fn get_type_invariant(&self, type_name: &str) -> Option<&HirTypeInvariant> {
        self.type_invariants.get(type_name)
    }

    /// Get the refined type definition by name (CTR-020)
    pub fn get_refined_type(&self, type_name: &str) -> Option<&HirRefinedType> {
        self.refined_types.get(type_name)
    }

    /// CTR-021: Check subtype relationship between two types
    ///
    /// Returns the relationship between `from_type` and `to_type`:
    /// - `Same`: Types are identical
    /// - `Subtype`: from_type is a subtype of to_type (no check needed)
    /// - `NeedsCheck`: Narrowing from base to refined (runtime check needed)
    /// - `Incompatible`: Types are not related
    pub fn check_subtype(&self, from_type: TypeId, to_type: TypeId) -> SubtypeResult {
        if from_type == to_type {
            return SubtypeResult::Same;
        }

        // Check if either type is a refined type
        let from_type_name = self.types.get_type_name(from_type);
        let to_type_name = self.types.get_type_name(to_type);

        // Check refined type relationships
        if let Some(from_name) = from_type_name {
            if let Some(refined) = self.refined_types.get(from_name) {
                // from_type is refined, check if to_type is its base
                if refined.base_type == to_type {
                    // Widening: refined -> base (no check needed)
                    return SubtypeResult::Subtype;
                }
            }
        }

        if let Some(to_name) = to_type_name {
            if let Some(refined) = self.refined_types.get(to_name) {
                // to_type is refined, check if from_type is its base
                if refined.base_type == from_type {
                    // Narrowing: base -> refined (check needed)
                    return SubtypeResult::NeedsCheck;
                }
            }
        }

        // Check through type aliases
        if let Some(from_name) = from_type_name {
            if let Some(from_alias_id) = self.types.lookup(from_name) {
                if from_alias_id == to_type {
                    return SubtypeResult::Same;
                }
            }
        }

        SubtypeResult::Incompatible
    }

    /// CTR-022/CTR-023: Check if a value satisfies a refined type's predicate
    ///
    /// Returns:
    /// - `Ok(true)`: Predicate is provably satisfied at compile time
    /// - `Ok(false)`: Predicate is provably violated at compile time
    /// - `Err(predicate)`: Cannot prove at compile time, need runtime check
    pub fn check_refinement(
        &self,
        type_name: &str,
        value: &HirExpr,
    ) -> Result<bool, HirExpr> {
        if let Some(refined) = self.refined_types.get(type_name) {
            // CTR-022: Try compile-time evaluation
            if let Some(result) = refined.try_const_eval(value) {
                return Ok(result);
            }
            // CTR-023: Can't prove at compile time, return predicate for runtime check
            // Substitute self (local 0) with the actual value
            Err(refined.predicate.clone())
        } else {
            // Not a refined type, always satisfied
            Ok(true)
        }
    }
}

impl Default for HirModule {
    fn default() -> Self {
        Self::new()
    }
}
