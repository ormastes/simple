//! Type-related utilities for the Simple interpreter.
//!
//! This module handles:
//! - Type name extraction from AST Type nodes
//! - Trait implementation registration and validation
//! - Blanket impl and overlap detection

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{ImplBlock, Type};

use crate::error::{codes, CompileError, ErrorContext};

#[derive(Default)]
pub(super) struct TraitImplRegistry {
    pub blanket_impl: bool,
    pub default_blanket_impl: bool,
    pub specific_impls: HashSet<String>,
}

/// Extract type name from a Type AST node
pub(super) fn get_type_name(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, .. } => name.clone(),
        _ => "unknown".to_string(),
    }
}

/// Register a trait implementation and validate for overlapping impls
pub(super) fn register_trait_impl(
    registry: &mut HashMap<String, TraitImplRegistry>,
    impl_block: &ImplBlock,
) -> Result<(), CompileError> {
    let is_default = impl_block.attributes.iter().any(|attr| attr.name == "default");

    let Some(trait_name) = &impl_block.trait_name else {
        if is_default {
            let ctx = ErrorContext::new()
                .with_code(codes::INVALID_OPERATION)
                .with_help("Use #[default] only on trait implementations");
            return Err(CompileError::semantic_with_context(
                "#[default] attribute is only valid on trait impls".to_string(),
                ctx,
            ));
        }
        return Ok(());
    };

    let is_blanket = match &impl_block.target_type {
        Type::Simple(name) => impl_block.generic_params.iter().any(|p| p == name),
        _ => false,
    };

    if is_default && !is_blanket {
        return Err(crate::error::factory::default_impl_must_be_blanket(&trait_name));
    }

    let target_key = get_type_name(&impl_block.target_type);
    let entry = registry.entry(trait_name.clone()).or_default();

    if is_blanket {
        if entry.blanket_impl {
            return Err(crate::error::factory::duplicate_blanket_impl(&trait_name));
        }
        if !is_default && (!entry.specific_impls.is_empty() || entry.default_blanket_impl) {
            return Err(crate::error::factory::overlapping_impls(
                &trait_name,
                "blanket impl conflicts with existing impls",
            ));
        }
        entry.blanket_impl = true;
        entry.default_blanket_impl = is_default;
        return Ok(());
    }

    if entry.specific_impls.contains(&target_key) {
        return Err(crate::error::factory::duplicate_impl(&trait_name, &target_key));
    }

    if entry.blanket_impl && !entry.default_blanket_impl {
        return Err(crate::error::factory::overlapping_impls(
            &trait_name,
            &format!("specific impl for `{}` conflicts with blanket impl", target_key),
        ));
    }

    entry.specific_impls.insert(target_key);
    Ok(())
}
