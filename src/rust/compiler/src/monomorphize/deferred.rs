//! Deferred monomorphization for template instantiation from .smf files.
//!
//! This module enables library-style generic imports where downstream code
//! can instantiate new type combinations from compiled .smf templates.
//!
//! ## Instantiation Modes
//!
//! - **LinkTime**: Template instantiation during native binary linking
//! - **JitTime**: Template instantiation during .smf loader execution
//!
//! ## Example
//!
//! ```ignore
//! // Library: collections.smf contains List<T> template
//! // App: imports collections and uses List<Float>
//! let mut mono = DeferredMonomorphizer::new(InstantiationMode::LinkTime);
//! mono.load_templates_from_smf(&smf_file)?;
//! let specialized = mono.instantiate_function("List::push", &[ConcreteType::Float])?;
//! ```

use std::collections::HashMap;
use std::path::Path;

use simple_parser::ast::{ClassDef, EnumDef, FunctionDef, Module, Node, StructDef, TraitDef};

use super::engine::Monomorphizer;
use super::metadata::{GenericEnumMeta, GenericFunctionMeta, GenericStructMeta, GenericTraitMeta, MonomorphizationMetadata};
use super::types::{ConcreteType, SpecializationKey};
use crate::error::CompileError;

/// Instantiation mode for deferred monomorphization.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InstantiationMode {
    /// Link-time instantiation for native binary builds.
    /// Instantiates all needed specializations before final linking.
    LinkTime,

    /// JIT-time instantiation for .smf loader execution.
    /// Instantiates specializations on-demand during runtime.
    JitTime,
}

/// Generic template wrapper.
///
/// Stores the original generic definition for later instantiation.
#[derive(Debug, Clone)]
pub enum GenericTemplate {
    Function(FunctionDef),
    Struct(StructDef),
    Class(ClassDef),
    Enum(EnumDef),
    Trait(TraitDef),
}

impl GenericTemplate {
    /// Get the name of this template.
    pub fn name(&self) -> &str {
        match self {
            GenericTemplate::Function(f) => &f.name,
            GenericTemplate::Struct(s) => &s.name,
            GenericTemplate::Class(c) => &c.name,
            GenericTemplate::Enum(e) => &e.name,
            GenericTemplate::Trait(t) => &t.name,
        }
    }

    /// Get the generic parameters of this template.
    pub fn generic_params(&self) -> &[String] {
        match self {
            GenericTemplate::Function(f) => &f.generic_params,
            GenericTemplate::Struct(s) => &s.generic_params,
            GenericTemplate::Class(c) => &c.generic_params,
            GenericTemplate::Enum(e) => &e.generic_params,
            GenericTemplate::Trait(t) => &t.generic_params,
        }
    }

    /// Check if this is a function template.
    pub fn is_function(&self) -> bool {
        matches!(self, GenericTemplate::Function(_))
    }

    /// Get as function, or error if not a function.
    pub fn as_function(&self) -> Result<&FunctionDef, CompileError> {
        match self {
            GenericTemplate::Function(f) => Ok(f),
            _ => Err(CompileError::Codegen(format!("{} is not a function template", self.name()))),
        }
    }

    /// Get as struct, or error if not a struct.
    pub fn as_struct(&self) -> Result<&StructDef, CompileError> {
        match self {
            GenericTemplate::Struct(s) => Ok(s),
            _ => Err(CompileError::Codegen(format!("{} is not a struct template", self.name()))),
        }
    }

    /// Get as class, or error if not a class.
    pub fn as_class(&self) -> Result<&ClassDef, CompileError> {
        match self {
            GenericTemplate::Class(c) => Ok(c),
            _ => Err(CompileError::Codegen(format!("{} is not a class template", self.name()))),
        }
    }

    /// Get as enum, or error if not an enum.
    pub fn as_enum(&self) -> Result<&EnumDef, CompileError> {
        match self {
            GenericTemplate::Enum(e) => Ok(e),
            _ => Err(CompileError::Codegen(format!("{} is not an enum template", self.name()))),
        }
    }
}

/// Compiled specialization code.
#[derive(Debug, Clone)]
pub enum CompiledCode {
    Function(FunctionDef),
    Struct(StructDef),
    Class(ClassDef),
    Enum(EnumDef),
}

/// Deferred monomorphizer for on-demand template instantiation.
///
/// Loads generic templates from .smf files and instantiates them on demand
/// with concrete type arguments.
pub struct DeferredMonomorphizer {
    /// Template cache: name -> template definition
    template_cache: HashMap<String, GenericTemplate>,

    /// Specialization cache: key -> compiled code
    specialization_cache: HashMap<SpecializationKey, CompiledCode>,

    /// Monomorphization metadata from loaded .smf files
    metadata: MonomorphizationMetadata,

    /// Instantiation mode (link-time or JIT-time)
    mode: InstantiationMode,
}

impl DeferredMonomorphizer {
    /// Create a new deferred monomorphizer.
    pub fn new(mode: InstantiationMode) -> Self {
        Self {
            template_cache: HashMap::new(),
            specialization_cache: HashMap::new(),
            metadata: MonomorphizationMetadata::new(),
            mode,
        }
    }

    /// Get the instantiation mode.
    pub fn mode(&self) -> InstantiationMode {
        self.mode
    }

    /// Load templates from an SMF file.
    ///
    /// Extracts TemplateCode and TemplateMeta sections and populates the template cache.
    pub fn load_templates_from_smf(&mut self, smf_path: &Path) -> Result<(), CompileError> {
        // Read SMF file
        let smf_bytes = std::fs::read(smf_path)
            .map_err(|e| CompileError::Io(format!("Failed to read SMF file: {}", e)))?;

        // Parse SMF header and sections
        // TODO: Implement proper SMF parsing with simple_loader
        // For now, we'll assume templates are not in SMF yet and return early
        // This will be implemented when full serialization is complete
        tracing::warn!("SMF template loading not yet fully implemented - returning empty");

        // Placeholder for future implementation:
        // 1. Parse SMF header
        // 2. Find TemplateCode section
        // 3. Find TemplateMeta section
        // 4. Deserialize templates and metadata

        Ok(())
    }

    /// Deserialize templates from binary data.
    fn deserialize_templates(&mut self, data: &[u8]) -> Result<(), CompileError> {
        if data.len() < 10 {
            return Err(CompileError::Codegen("Template data too short".to_string()));
        }

        // Verify magic
        if &data[0..4] != b"GTPL" {
            return Err(CompileError::Codegen("Invalid template magic".to_string()));
        }

        // Read version
        let _version = u16::from_le_bytes([data[4], data[5]]);

        // Read template count
        let count = u32::from_le_bytes([data[6], data[7], data[8], data[9]]);

        // Deserialize each template (placeholder implementation)
        let mut offset = 10;
        for _ in 0..count {
            if offset >= data.len() {
                break;
            }

            let kind = data[offset];
            offset += 1;

            // Read name length
            if offset + 4 > data.len() {
                break;
            }
            let name_len = u32::from_le_bytes([data[offset], data[offset + 1], data[offset + 2], data[offset + 3]]) as usize;
            offset += 4;

            // Read name
            if offset + name_len > data.len() {
                break;
            }
            let name = String::from_utf8_lossy(&data[offset..offset + name_len]).to_string();
            offset += name_len;

            // Read generic param count
            if offset >= data.len() {
                break;
            }
            let param_count = data[offset];
            offset += 1;

            // Create placeholder template
            // TODO: Full deserialization in Phase 3 completion
            let template = self.create_placeholder_template(kind, &name, param_count)?;
            self.template_cache.insert(name, template);
        }

        Ok(())
    }

    /// Create a placeholder template (will be replaced with full deserialization).
    fn create_placeholder_template(&self, kind: u8, name: &str, param_count: u8) -> Result<GenericTemplate, CompileError> {
        // Create minimal placeholder templates
        // TODO: Replace with full AST deserialization
        let generic_params = (0..param_count).map(|i| format!("T{}", i)).collect();

        match kind {
            0 => {
                // Function
                let func = FunctionDef {
                    span: simple_parser::token::Span::new(0, 0, 0, 0),
                    name: name.to_string(),
                    generic_params,
                    params: vec![],
                    return_type: None,
                    where_clause: vec![],
                    body: simple_parser::ast::Block::default(),
                    visibility: simple_parser::ast::Visibility::Public,
                    effects: vec![],
                    decorators: vec![],
                    attributes: vec![],
                    doc_comment: None,
                    contract: None,
                    is_abstract: false,
                    is_sync: false,
                    is_me_method: false,
                    bounds_block: None,
                    return_constraint: None,
                    is_generic_template: true,
                    specialization_of: None,
                    type_bindings: HashMap::new(),
                };
                Ok(GenericTemplate::Function(func))
            }
            1 => {
                // Struct
                let struct_def = StructDef {
                    span: simple_parser::token::Span::new(0, 0, 0, 0),
                    name: name.to_string(),
                    generic_params,
                    where_clause: vec![],
                    fields: vec![],
                    methods: vec![],
                    visibility: simple_parser::ast::Visibility::Public,
                    attributes: vec![],
                    doc_comment: None,
                    invariant: None,
                    is_generic_template: true,
                    specialization_of: None,
                    type_bindings: HashMap::new(),
                };
                Ok(GenericTemplate::Struct(struct_def))
            }
            2 => {
                // Class
                let class_def = ClassDef {
                    span: simple_parser::token::Span::new(0, 0, 0, 0),
                    name: name.to_string(),
                    generic_params,
                    where_clause: vec![],
                    fields: vec![],
                    methods: vec![],
                    visibility: simple_parser::ast::Visibility::Public,
                    attributes: vec![],
                    doc_comment: None,
                    invariant: None,
                    effects: vec![],
                    macro_invocations: vec![],
                    mixins: vec![],
                    parent: None,
                    is_generic_template: true,
                    specialization_of: None,
                    type_bindings: HashMap::new(),
                };
                Ok(GenericTemplate::Class(class_def))
            }
            3 => {
                // Enum
                let enum_def = EnumDef {
                    span: simple_parser::token::Span::new(0, 0, 0, 0),
                    name: name.to_string(),
                    generic_params,
                    where_clause: vec![],
                    variants: vec![],
                    methods: vec![],
                    visibility: simple_parser::ast::Visibility::Public,
                    attributes: vec![],
                    doc_comment: None,
                    is_generic_template: true,
                    specialization_of: None,
                    type_bindings: HashMap::new(),
                };
                Ok(GenericTemplate::Enum(enum_def))
            }
            4 => {
                // Trait
                let trait_def = TraitDef {
                    span: simple_parser::token::Span::new(0, 0, 0, 0),
                    name: name.to_string(),
                    generic_params,
                    super_traits: vec![],
                    where_clause: vec![],
                    associated_types: vec![],
                    methods: vec![],
                    visibility: simple_parser::ast::Visibility::Public,
                    doc_comment: None,
                    is_generic_template: true,
                    specialization_of: None,
                    type_bindings: HashMap::new(),
                };
                Ok(GenericTemplate::Trait(trait_def))
            }
            _ => Err(CompileError::Codegen(format!("Unknown template kind: {}", kind))),
        }
    }

    /// Deserialize metadata from binary data.
    fn deserialize_metadata(&mut self, data: &[u8]) -> Result<(), CompileError> {
        if data.len() < 22 {
            return Err(CompileError::Codegen("Metadata too short".to_string()));
        }

        // Verify magic
        if &data[0..4] != b"META" {
            return Err(CompileError::Codegen("Invalid metadata magic".to_string()));
        }

        // Read version
        let _version = u16::from_le_bytes([data[4], data[5]]);

        // Read counts
        let func_count = u32::from_le_bytes([data[6], data[7], data[8], data[9]]);
        let struct_count = u32::from_le_bytes([data[10], data[11], data[12], data[13]]);
        let enum_count = u32::from_le_bytes([data[14], data[15], data[16], data[17]]);
        let trait_count = u32::from_le_bytes([data[18], data[19], data[20], data[21]]);

        // TODO: Deserialize full metadata entries
        // For now, just create empty metadata entries
        for i in 0..func_count {
            let name = format!("func_{}", i);
            self.metadata.functions.insert(name.clone(), GenericFunctionMeta::new(name, vec![]));
        }

        for i in 0..struct_count {
            let name = format!("struct_{}", i);
            self.metadata.structs.insert(name.clone(), GenericStructMeta::new(name, vec![]));
        }

        for i in 0..enum_count {
            let name = format!("enum_{}", i);
            self.metadata.enums.insert(name.clone(), GenericEnumMeta::new(name, vec![]));
        }

        for i in 0..trait_count {
            let name = format!("trait_{}", i);
            self.metadata.traits.insert(name.clone(), GenericTraitMeta::new(name, vec![]));
        }

        Ok(())
    }

    /// Instantiate a function with concrete type arguments.
    ///
    /// Returns a specialized FunctionDef, or an error if:
    /// - The template doesn't exist
    /// - The template is not a function
    /// - Type argument count doesn't match
    pub fn instantiate_function(&mut self, name: &str, type_args: &[ConcreteType]) -> Result<FunctionDef, CompileError> {
        let key = SpecializationKey::new(name.to_string(), type_args.to_vec());

        // Check cache first
        if let Some(cached) = self.specialization_cache.get(&key) {
            if let CompiledCode::Function(f) = cached {
                return Ok(f.clone());
            }
        }

        // Get template
        let template = self
            .template_cache
            .get(name)
            .ok_or_else(|| CompileError::Codegen(format!("Template not found: {}", name)))?;

        let func_template = template.as_function()?;

        // Validate type argument count
        if type_args.len() != func_template.generic_params.len() {
            return Err(CompileError::Codegen(format!(
                "Type argument count mismatch: expected {}, got {}",
                func_template.generic_params.len(),
                type_args.len()
            )));
        }

        // Perform monomorphization
        let specialized = self.monomorphize_function(func_template, type_args)?;

        // Cache the result
        self.specialization_cache
            .insert(key, CompiledCode::Function(specialized.clone()));

        Ok(specialized)
    }

    /// Instantiate a struct with concrete type arguments.
    pub fn instantiate_struct(&mut self, name: &str, type_args: &[ConcreteType]) -> Result<StructDef, CompileError> {
        let key = SpecializationKey::new(name.to_string(), type_args.to_vec());

        if let Some(CompiledCode::Struct(s)) = self.specialization_cache.get(&key) {
            return Ok(s.clone());
        }

        let template = self
            .template_cache
            .get(name)
            .ok_or_else(|| CompileError::Codegen(format!("Template not found: {}", name)))?;

        let struct_template = template.as_struct()?;

        if type_args.len() != struct_template.generic_params.len() {
            return Err(CompileError::Codegen(format!(
                "Type argument count mismatch: expected {}, got {}",
                struct_template.generic_params.len(),
                type_args.len()
            )));
        }

        let specialized = self.monomorphize_struct(struct_template, type_args)?;
        self.specialization_cache
            .insert(key, CompiledCode::Struct(specialized.clone()));

        Ok(specialized)
    }

    /// Instantiate a class with concrete type arguments.
    pub fn instantiate_class(&mut self, name: &str, type_args: &[ConcreteType]) -> Result<ClassDef, CompileError> {
        let key = SpecializationKey::new(name.to_string(), type_args.to_vec());

        if let Some(CompiledCode::Class(c)) = self.specialization_cache.get(&key) {
            return Ok(c.clone());
        }

        let template = self
            .template_cache
            .get(name)
            .ok_or_else(|| CompileError::Codegen(format!("Template not found: {}", name)))?;

        let class_template = template.as_class()?;

        if type_args.len() != class_template.generic_params.len() {
            return Err(CompileError::Codegen(format!(
                "Type argument count mismatch: expected {}, got {}",
                class_template.generic_params.len(),
                type_args.len()
            )));
        }

        let specialized = self.monomorphize_class(class_template, type_args)?;
        self.specialization_cache
            .insert(key, CompiledCode::Class(specialized.clone()));

        Ok(specialized)
    }

    /// Instantiate an enum with concrete type arguments.
    pub fn instantiate_enum(&mut self, name: &str, type_args: &[ConcreteType]) -> Result<EnumDef, CompileError> {
        let key = SpecializationKey::new(name.to_string(), type_args.to_vec());

        if let Some(CompiledCode::Enum(e)) = self.specialization_cache.get(&key) {
            return Ok(e.clone());
        }

        let template = self
            .template_cache
            .get(name)
            .ok_or_else(|| CompileError::Codegen(format!("Template not found: {}", name)))?;

        let enum_template = template.as_enum()?;

        if type_args.len() != enum_template.generic_params.len() {
            return Err(CompileError::Codegen(format!(
                "Type argument count mismatch: expected {}, got {}",
                enum_template.generic_params.len(),
                type_args.len()
            )));
        }

        let specialized = self.monomorphize_enum(enum_template, type_args)?;
        self.specialization_cache
            .insert(key, CompiledCode::Enum(specialized.clone()));

        Ok(specialized)
    }

    /// Perform monomorphization on a function template.
    fn monomorphize_function(&self, template: &FunctionDef, type_args: &[ConcreteType]) -> Result<FunctionDef, CompileError> {
        // Create a minimal module for monomorphization
        let module = Module {
            name: Some("deferred".to_string()),
            items: vec![Node::Function(template.clone())],
        };

        let mut mono = Monomorphizer::new(&module);
        let key = SpecializationKey::new(template.name.clone(), type_args.to_vec());

        // Specialize the function
        let specialized = mono.specialize_function_with_key(&key)?;

        Ok(specialized)
    }

    /// Perform monomorphization on a struct template.
    fn monomorphize_struct(&self, template: &StructDef, type_args: &[ConcreteType]) -> Result<StructDef, CompileError> {
        let module = Module {
            name: Some("deferred".to_string()),
            items: vec![Node::Struct(template.clone())],
        };

        let mut mono = Monomorphizer::new(&module);
        let key = SpecializationKey::new(template.name.clone(), type_args.to_vec());

        let specialized = mono.specialize_struct_with_key(&key)?;

        Ok(specialized)
    }

    /// Perform monomorphization on a class template.
    fn monomorphize_class(&self, template: &ClassDef, type_args: &[ConcreteType]) -> Result<ClassDef, CompileError> {
        let module = Module {
            name: Some("deferred".to_string()),
            items: vec![Node::Class(template.clone())],
        };

        let mut mono = Monomorphizer::new(&module);
        let key = SpecializationKey::new(template.name.clone(), type_args.to_vec());

        let specialized = mono.specialize_class_with_key(&key)?;

        Ok(specialized)
    }

    /// Perform monomorphization on an enum template.
    fn monomorphize_enum(&self, template: &EnumDef, type_args: &[ConcreteType]) -> Result<EnumDef, CompileError> {
        let module = Module {
            name: Some("deferred".to_string()),
            items: vec![Node::Enum(template.clone())],
        };

        let mut mono = Monomorphizer::new(&module);
        let key = SpecializationKey::new(template.name.clone(), type_args.to_vec());

        let specialized = mono.specialize_enum_with_key(&key)?;

        Ok(specialized)
    }

    /// Get all loaded template names.
    pub fn template_names(&self) -> Vec<String> {
        self.template_cache.keys().cloned().collect()
    }

    /// Get the number of cached specializations.
    pub fn specialization_count(&self) -> usize {
        self.specialization_cache.len()
    }

    /// Clear the specialization cache.
    pub fn clear_cache(&mut self) {
        self.specialization_cache.clear();
    }

    /// Get metadata for debugging/inspection.
    pub fn metadata(&self) -> &MonomorphizationMetadata {
        &self.metadata
    }

    /// Get statistics about loaded templates and cached specializations.
    pub fn get_stats(&self) -> DeferredMonoStats {
        DeferredMonoStats {
            template_count: self.template_cache.len(),
            specialization_count: self.specialization_cache.len(),
            mode: self.mode,
        }
    }
}

/// Statistics for deferred monomorphization.
#[derive(Debug, Clone)]
pub struct DeferredMonoStats {
    /// Number of loaded templates
    pub template_count: usize,
    /// Number of cached specializations
    pub specialization_count: usize,
    /// Instantiation mode
    pub mode: InstantiationMode,
}
