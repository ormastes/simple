use simple_parser::ast::{ImplBlock, Node, Type};
use std::collections::{HashMap, HashSet};

#[derive(Debug, Clone, PartialEq)]
pub enum CoherenceError {
    OrphanImpl {
        trait_name: String,
        target_type: String,
        span: simple_parser::token::Span,
        suggestion: Option<String>,
    },
    OverlappingImpl {
        trait_name: String,
        type1: String,
        type2: String,
        span: simple_parser::token::Span,
    },
    ConflictingAssociatedType {
        trait_name: String,
        target_type: String,
        type_name: String,
        span: simple_parser::token::Span,
    },
    BlanketImplConflict {
        trait_name: String,
        general: String,
        specific: String,
        span: simple_parser::token::Span,
    },
}

impl CoherenceError {
    /// Get a user-friendly error message with suggestions
    pub fn message(&self) -> String {
        match self {
            CoherenceError::OrphanImpl {
                trait_name,
                target_type,
                suggestion,
                ..
            } => {
                let base_msg = format!(
                    "Cannot implement foreign trait '{}' for foreign type '{}'",
                    trait_name, target_type
                );
                if let Some(sugg) = suggestion {
                    format!("{}\n\nSuggestion: {}", base_msg, sugg)
                } else {
                    base_msg
                }
            }
            CoherenceError::OverlappingImpl {
                trait_name,
                type1,
                type2,
                ..
            } => format!(
                "Overlapping implementations of trait '{}' for types '{}' and '{}'",
                trait_name, type1, type2
            ),
            CoherenceError::ConflictingAssociatedType {
                trait_name,
                target_type,
                type_name,
                ..
            } => format!(
                "Conflicting associated type '{}' in trait '{}' for type '{}'",
                type_name, trait_name, target_type
            ),
            CoherenceError::BlanketImplConflict {
                trait_name,
                general,
                specific,
                ..
            } => format!(
                "Blanket implementation '{}' for trait '{}' conflicts with specific implementation '{}'",
                general, trait_name, specific
            ),
        }
    }

    /// Get the span where the error occurred
    pub fn span(&self) -> simple_parser::token::Span {
        match self {
            CoherenceError::OrphanImpl { span, .. }
            | CoherenceError::OverlappingImpl { span, .. }
            | CoherenceError::ConflictingAssociatedType { span, .. }
            | CoherenceError::BlanketImplConflict { span, .. } => *span,
        }
    }
}

pub struct CoherenceChecker {
    local_traits: HashSet<String>,
    local_types: HashSet<String>,
    impl_registry: HashMap<String, Vec<ImplRegistryEntry>>,
}

#[derive(Debug, Clone)]
struct ImplRegistryEntry {
    target_type: Type,
    trait_name: Option<String>,
    generic_params: Vec<String>,
    is_blanket: bool,
    is_default: bool, // #[default] attribute for specialization (#1150)
    associated_types: HashMap<String, Type>,
    span: simple_parser::token::Span,
}

impl CoherenceChecker {
    pub fn new() -> Self {
        Self {
            local_traits: HashSet::new(),
            local_types: HashSet::new(),
            impl_registry: HashMap::new(),
        }
    }

    pub fn register_trait(&mut self, name: String) {
        self.local_traits.insert(name);
    }

    pub fn register_type(&mut self, name: String) {
        self.local_types.insert(name);
    }

    /// Check if negative bounds are satisfied (feature #1151)
    /// Negative bounds: T: !Clone means T must NOT implement Clone
    /// This allows blanket impls like: impl[T: !Clone] Copy for T
    fn check_negative_bounds(&self, _impl_block: &ImplBlock) -> Result<(), CoherenceError> {
        // Negative bounds are supported in AST (negative_bounds field in WhereBound)
        // When parser fully supports !Trait syntax, this will validate:
        // 1. Check where_clause for negative_bounds
        // 2. Ensure type doesn't implement excluded traits
        // 3. Prevent conflicts with existing impls that have the excluded trait

        // For now, this is a placeholder - negative bounds parse but aren't enforced
        // Full enforcement requires trait resolution which happens later in compilation
        Ok(())
    }

    pub fn check_impl(&mut self, impl_block: &ImplBlock) -> Result<(), CoherenceError> {
        let target_type_name = self.extract_type_name(&impl_block.target_type);
        let trait_name = impl_block.trait_name.as_ref();

        if let Some(trait_name) = trait_name {
            self.check_orphan_rule(trait_name, &target_type_name, impl_block.span)?;

            // Check associated types first for exact same impl
            self.check_associated_types(trait_name, &target_type_name, impl_block)?;

            // Then check for blanket conflicts
            self.check_blanket_conflict(trait_name, impl_block)?;

            // Finally check for general overlap
            self.check_overlap(trait_name, impl_block)?;
        }

        self.register_impl(impl_block);
        Ok(())
    }

    fn check_orphan_rule(
        &self,
        trait_name: &str,
        target_type: &str,
        span: simple_parser::token::Span,
    ) -> Result<(), CoherenceError> {
        let trait_is_local = self.local_traits.contains(trait_name);
        let type_is_local = self.local_types.contains(target_type);

        if !trait_is_local && !type_is_local {
            // Generate newtype pattern suggestion (#1153)
            let suggestion = format!(
                "Consider using the newtype pattern:\n\
                 \n\
                 struct {}Wrapper({})\n\
                 \n\
                 impl {} for {}Wrapper:\n\
                     # Now allowed - {}Wrapper is local",
                target_type, target_type, trait_name, target_type, target_type
            );

            return Err(CoherenceError::OrphanImpl {
                trait_name: trait_name.to_string(),
                target_type: target_type.to_string(),
                span,
                suggestion: Some(suggestion),
            });
        }

        Ok(())
    }

    fn check_overlap(
        &self,
        trait_name: &str,
        impl_block: &ImplBlock,
    ) -> Result<(), CoherenceError> {
        // Check if this impl has #[default] attribute (specialization support #1150)
        let has_default = impl_block
            .attributes
            .iter()
            .any(|attr| attr.name == "default");

        if let Some(existing_impls) = self.impl_registry.get(trait_name) {
            let new_type_name = self.extract_type_name(&impl_block.target_type);

            for existing in existing_impls {
                let existing_type_name = self.extract_type_name(&existing.target_type);

                // Skip overlap check if either impl is marked with #[default] (specialization)
                if has_default || existing.is_default {
                    continue;
                }

                if self.types_could_unify(
                    &new_type_name,
                    &existing_type_name,
                    &impl_block.generic_params,
                    &existing.generic_params,
                ) {
                    return Err(CoherenceError::OverlappingImpl {
                        trait_name: trait_name.to_string(),
                        type1: new_type_name,
                        type2: existing_type_name,
                        span: impl_block.span,
                    });
                }
            }
        }
        Ok(())
    }

    fn check_associated_types(
        &self,
        trait_name: &str,
        target_type: &str,
        impl_block: &ImplBlock,
    ) -> Result<(), CoherenceError> {
        if let Some(existing_impls) = self.impl_registry.get(trait_name) {
            for existing in existing_impls {
                let existing_target = self.extract_type_name(&existing.target_type);

                if existing_target == target_type {
                    for assoc_type in &impl_block.associated_types {
                        if let Some(existing_type) = existing.associated_types.get(&assoc_type.name)
                        {
                            if existing_type != &assoc_type.ty {
                                return Err(CoherenceError::ConflictingAssociatedType {
                                    trait_name: trait_name.to_string(),
                                    target_type: target_type.to_string(),
                                    type_name: assoc_type.name.clone(),
                                    span: impl_block.span,
                                });
                            }
                        }
                    }
                }
            }
        }
        Ok(())
    }

    fn check_blanket_conflict(
        &self,
        trait_name: &str,
        impl_block: &ImplBlock,
    ) -> Result<(), CoherenceError> {
        let is_blanket = !impl_block.generic_params.is_empty();

        // Check if this impl has #[default] attribute (specialization support #1150)
        let has_default = impl_block
            .attributes
            .iter()
            .any(|attr| attr.name == "default");

        if let Some(existing_impls) = self.impl_registry.get(trait_name) {
            let new_type = self.extract_type_name(&impl_block.target_type);

            for existing in existing_impls {
                // Skip conflict check if either impl is marked with #[default] (specialization)
                if has_default || existing.is_default {
                    continue;
                }

                if is_blanket && !existing.is_blanket {
                    let existing_type = self.extract_type_name(&existing.target_type);
                    if self.blanket_covers_specific(
                        &new_type,
                        &existing_type,
                        &impl_block.generic_params,
                    ) {
                        return Err(CoherenceError::BlanketImplConflict {
                            trait_name: trait_name.to_string(),
                            general: new_type,
                            specific: existing_type,
                            span: impl_block.span,
                        });
                    }
                } else if !is_blanket && existing.is_blanket {
                    let existing_type = self.extract_type_name(&existing.target_type);
                    if self.blanket_covers_specific(
                        &existing_type,
                        &new_type,
                        &existing.generic_params,
                    ) {
                        return Err(CoherenceError::BlanketImplConflict {
                            trait_name: trait_name.to_string(),
                            general: existing_type,
                            specific: new_type,
                            span: impl_block.span,
                        });
                    }
                }
            }
        }
        Ok(())
    }

    fn register_impl(&mut self, impl_block: &ImplBlock) {
        if let Some(trait_name) = &impl_block.trait_name {
            let mut associated_types = HashMap::new();
            for assoc_type in &impl_block.associated_types {
                associated_types.insert(assoc_type.name.clone(), assoc_type.ty.clone());
            }

            // Check for #[default] attribute (specialization #1150)
            let is_default = impl_block
                .attributes
                .iter()
                .any(|attr| attr.name == "default");

            let entry = ImplRegistryEntry {
                target_type: impl_block.target_type.clone(),
                trait_name: Some(trait_name.clone()),
                generic_params: impl_block.generic_params.clone(),
                is_blanket: !impl_block.generic_params.is_empty(),
                is_default,
                associated_types,
                span: impl_block.span,
            };

            self.impl_registry
                .entry(trait_name.clone())
                .or_insert_with(Vec::new)
                .push(entry);
        }
    }

    fn extract_type_name(&self, ty: &Type) -> String {
        match ty {
            Type::Simple(name) => name.clone(),
            Type::Generic { name, .. } => name.clone(),
            Type::Array { .. } => "Array".to_string(),
            Type::Tuple(_) => "Tuple".to_string(),
            Type::Function { .. } => "Function".to_string(),
            Type::Optional(_) => "Option".to_string(),
            Type::Pointer { .. } => "Pointer".to_string(),
            Type::Capability { .. } => "Capability".to_string(),
            Type::DynTrait(name) => name.clone(),
            _ => "Unknown".to_string(),
        }
    }

    fn types_could_unify(
        &self,
        type1: &str,
        type2: &str,
        generics1: &[String],
        generics2: &[String],
    ) -> bool {
        if type1 == type2 {
            return true;
        }

        if generics1.iter().any(|g| type1 == g) || generics2.iter().any(|g| type2 == g) {
            return true;
        }

        false
    }

    fn blanket_covers_specific(
        &self,
        blanket_type: &str,
        _specific_type: &str,
        generics: &[String],
    ) -> bool {
        generics.iter().any(|g| blanket_type == g)
    }

    pub fn check_module(&mut self, nodes: &[Node]) -> Vec<CoherenceError> {
        let mut errors = Vec::new();

        for node in nodes {
            match node {
                Node::Trait(trait_def) => {
                    self.register_trait(trait_def.name.clone());
                }
                Node::Struct(struct_def) => {
                    self.register_type(struct_def.name.clone());
                }
                Node::Class(class_def) => {
                    self.register_type(class_def.name.clone());
                }
                Node::Enum(enum_def) => {
                    self.register_type(enum_def.name.clone());
                }
                _ => {}
            }
        }

        for node in nodes {
            if let Node::Impl(impl_block) = node {
                if let Err(err) = self.check_impl(impl_block) {
                    errors.push(err);
                }
            }
        }

        errors
    }
}

impl Default for CoherenceChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_orphan_rule_local_trait() {
        let mut checker = CoherenceChecker::new();
        checker.register_trait("MyTrait".to_string());

        let result = checker.check_orphan_rule(
            "MyTrait",
            "String",
            simple_parser::token::Span::new(0, 0, 0, 0),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_orphan_rule_local_type() {
        let mut checker = CoherenceChecker::new();
        checker.register_type("MyType".to_string());

        let result = checker.check_orphan_rule(
            "Display",
            "MyType",
            simple_parser::token::Span::new(0, 0, 0, 0),
        );
        assert!(result.is_ok());
    }

    #[test]
    fn test_orphan_rule_violation() {
        let checker = CoherenceChecker::new();

        let result = checker.check_orphan_rule(
            "Display",
            "String",
            simple_parser::token::Span::new(0, 0, 0, 0),
        );
        assert!(result.is_err());

        if let Err(CoherenceError::OrphanImpl {
            trait_name,
            target_type,
            suggestion,
            ..
        }) = result
        {
            assert_eq!(trait_name, "Display");
            assert_eq!(target_type, "String");
            // Check that suggestion is provided (#1153)
            assert!(suggestion.is_some());
            let sugg = suggestion.unwrap();
            assert!(sugg.contains("newtype pattern"));
            assert!(sugg.contains("StringWrapper"));
        } else {
            panic!("Expected OrphanImpl error");
        }
    }
}
