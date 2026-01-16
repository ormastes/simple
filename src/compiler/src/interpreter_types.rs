//! Type-related utilities for the Simple interpreter.
//!
//! This module handles:
//! - Type name extraction from AST Type nodes
//! - Trait implementation registration and validation
//! - Blanket impl and overlap detection

use std::collections::{HashMap, HashSet};

use simple_parser::ast::{ImplBlock, Type};

use crate::error::CompileError;

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
            return Err(CompileError::Semantic(
                "#[default] is only valid on trait impls".to_string(),
            ));
        }
        return Ok(());
    };

    let is_blanket = match &impl_block.target_type {
        Type::Simple(name) => impl_block.generic_params.iter().any(|p| p == name),
        _ => false,
    };

    if is_default && !is_blanket {
        return Err(CompileError::Semantic(format!(
            "#[default] impl for trait `{}` must be a blanket impl (impl[T] Trait for T)",
            trait_name
        )));
    }

    let target_key = get_type_name(&impl_block.target_type);
    let entry = registry.entry(trait_name.clone()).or_default();

    if is_blanket {
        if entry.blanket_impl {
            return Err(CompileError::Semantic(format!(
                "duplicate blanket impl for trait `{}`",
                trait_name
            )));
        }
        if !is_default && (!entry.specific_impls.is_empty() || entry.default_blanket_impl) {
            return Err(CompileError::Semantic(format!(
                "overlapping impls for trait `{}`: blanket impl conflicts with existing impls",
                trait_name
            )));
        }
        entry.blanket_impl = true;
        entry.default_blanket_impl = is_default;
        return Ok(());
    }

    if entry.specific_impls.contains(&target_key) {
        return Err(CompileError::Semantic(format!(
            "duplicate impl for trait `{}` and type `{}`",
            trait_name, target_key
        )));
    }

    if entry.blanket_impl && !entry.default_blanket_impl {
        return Err(CompileError::Semantic(format!(
            "overlapping impls for trait `{}`: specific impl for `{}` conflicts with blanket impl",
            trait_name, target_key
        )));
    }

    entry.specific_impls.insert(target_key);
    Ok(())
}
