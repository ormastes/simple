// Type registration for HIR lowering
//
// This module handles registration of various type definitions during
// the first pass of module lowering:
// - Structs
// - Classes (with inheritance and mixins)
// - Enums
// - Mixins
// - Type aliases (with refinement predicates)
// - Traits (with vtable slots)

use simple_parser::{self as ast};

use super::super::types::*;
use super::context::FunctionContext;
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;

impl Lowerer {
    /// Register a class type and its invariant
    ///
    /// Inherited invariants: If the class extends a parent class, the child class
    /// inherits all invariants from the parent. This ensures Liskov Substitution
    /// Principle - a child class must maintain all parent invariants.
    pub(crate) fn register_class(&mut self, c: &ast::ClassDef) -> LowerResult<TypeId> {
        // Collect class's own fields
        let mut fields: Vec<_> = c
            .fields
            .iter()
            .map(|f| {
                (
                    f.name.clone(),
                    self.resolve_type(&f.ty).unwrap_or(TypeId::VOID),
                )
            })
            .collect();

        // Apply mixins: add mixin fields to the class
        for mixin_ref in &c.mixins {
            if let Some(mixin_type_id) = self.module.types.lookup(&mixin_ref.name) {
                if let Some(HirType::Mixin {
                    fields: mixin_fields,
                    ..
                }) = self.module.types.get(mixin_type_id)
                {
                    // Add mixin fields to class fields
                    for (field_name, field_type) in mixin_fields.clone() {
                        // Check for field name conflicts
                        if fields.iter().any(|(existing, _)| existing == &field_name) {
                            // Field already exists - this is a conflict
                            // For now, skip the duplicate field (last-one-wins semantics)
                            // A future enhancement could emit a warning or error
                            continue;
                        }
                        fields.push((field_name, field_type));
                    }
                }
            }
        }

        let type_id = self.module.types.register_named(
            c.name.clone(),
            HirType::Struct {
                name: c.name.clone(),
                fields,
                has_snapshot: c.is_snapshot(),
            },
        );

        // Build combined invariant: parent invariants + child invariants
        let mut hir_invariant = HirTypeInvariant::default();
        let mut ctx = FunctionContext::new(TypeId::VOID);

        // Inherit parent invariants if class extends another class
        if let Some(ref parent_name) = c.parent {
            if let Some(parent_invariant) = self.module.type_invariants.get(parent_name) {
                // Clone parent invariant conditions into child
                for clause in &parent_invariant.conditions {
                    hir_invariant.conditions.push(clause.clone());
                }
            }
        }

        // Add child's own invariants
        if let Some(ref invariant) = c.invariant {
            for clause in &invariant.conditions {
                let condition = self.lower_expr(&clause.condition, &mut ctx)?;
                hir_invariant.conditions.push(HirContractClause {
                    condition,
                    message: clause.message.clone(),
                });
            }
        }

        // Register combined invariant if non-empty
        if !hir_invariant.conditions.is_empty() {
            self.module
                .type_invariants
                .insert(c.name.clone(), hir_invariant);
        }

        Ok(type_id)
    }

    pub(crate) fn register_struct(&mut self, s: &ast::StructDef) -> LowerResult<TypeId> {
        let mut fields = Vec::new();
        for field in &s.fields {
            let ty = self.resolve_type(&field.ty)?;
            fields.push((field.name.clone(), ty));
        }

        let hir_type = HirType::Struct {
            name: s.name.clone(),
            fields,
            has_snapshot: s.is_snapshot(),
        };

        let type_id = self.module.types.register_named(s.name.clone(), hir_type);

        // Register struct invariant if present
        if let Some(ref invariant) = s.invariant {
            let mut ctx = FunctionContext::new(TypeId::VOID);
            let mut hir_invariant = HirTypeInvariant::default();

            for clause in &invariant.conditions {
                let condition = self.lower_expr(&clause.condition, &mut ctx)?;
                hir_invariant.conditions.push(HirContractClause {
                    condition,
                    message: clause.message.clone(),
                });
            }

            self.module
                .type_invariants
                .insert(s.name.clone(), hir_invariant);
        }

        Ok(type_id)
    }

    pub(crate) fn register_mixin(&mut self, m: &ast::MixinDef) -> LowerResult<TypeId> {
        // Lower fields
        let mut fields = Vec::new();
        for field in &m.fields {
            let ty = self.resolve_type(&field.ty)?;
            fields.push((field.name.clone(), ty));
        }

        // Lower method signatures
        let mut methods = Vec::new();
        for method in &m.methods {
            let params: Vec<TypeId> = method
                .params
                .iter()
                .map(|p| self.resolve_type_opt(&p.ty))
                .collect::<LowerResult<Vec<_>>>()?;
            let ret = self.resolve_type_opt(&method.return_type)?;

            methods.push(HirMixinMethod {
                name: method.name.clone(),
                params,
                ret,
            });
        }

        // Extract type parameters (use generic_params from MixinDef)
        let type_params = m.generic_params.clone();

        // Extract trait bounds (use required_traits from MixinDef)
        let trait_bounds = m.required_traits.clone();

        // Extract required method names
        let required_methods: Vec<String> = m
            .required_methods
            .iter()
            .map(|rm| rm.name.clone())
            .collect();

        let hir_type = HirType::Mixin {
            name: m.name.clone(),
            type_params,
            fields,
            methods,
            trait_bounds,
            required_methods,
        };

        let type_id = self.module.types.register_named(m.name.clone(), hir_type);

        Ok(type_id)
    }

    /// Register a type alias, with optional refinement predicate (CTR-020)
    pub(crate) fn register_type_alias(&mut self, ta: &ast::TypeAliasDef) -> LowerResult<TypeId> {
        let base_type = self.resolve_type(&ta.ty)?;

        // Register the type alias name as an alias to the base type
        // For now, we just use the base type ID directly
        // The refinement predicate is stored separately for runtime checks

        if let Some(ref where_clause) = ta.where_clause {
            // This is a refined type: `type PosI64 = i64 where self > 0`
            // Lower the predicate with a synthetic 'self' binding
            let mut ctx = FunctionContext::new(base_type);
            // Add 'self' as a local variable for the predicate
            ctx.add_local(
                "self".to_string(),
                base_type,
                simple_parser::Mutability::Immutable,
            );

            let predicate = self.lower_expr(where_clause, &mut ctx)?;

            let refined_type = HirRefinedType {
                name: ta.name.clone(),
                base_type,
                predicate,
            };

            self.module
                .refined_types
                .insert(ta.name.clone(), refined_type);
        }

        // Register the type alias name to map to the base type
        self.module.types.register_alias(ta.name.clone(), base_type);

        Ok(base_type)
    }

    /// Register a trait and populate its vtable slot information
    ///
    /// This is used for static polymorphism support - when a trait method is
    /// called via dynamic dispatch, we need to know the vtable slot index.
    pub(crate) fn register_trait(&mut self, t: &ast::TraitDef) -> LowerResult<()> {
        let mut trait_info = HirTraitInfo::new(t.name.clone());
        trait_info.generic_params = t.generic_params.clone();

        // Add each method with its vtable slot
        // Methods are assigned slots in declaration order (0-indexed)
        for method in &t.methods {
            // Resolve parameter types (skip self)
            let param_types: Vec<TypeId> = method
                .params
                .iter()
                .filter(|p| p.name != "self")
                .map(|p| self.resolve_type_opt(&p.ty))
                .collect::<LowerResult<Vec<_>>>()?;

            // Resolve return type
            let return_type = self.resolve_type_opt(&method.return_type)?;

            trait_info.add_method(method.name.clone(), param_types, return_type);
        }

        // Store trait info in module
        self.module.trait_infos.insert(t.name.clone(), trait_info);

        Ok(())
    }
}
