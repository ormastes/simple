//! Import type loading for cross-module type resolution.
//!
//! This module handles loading type definitions from imported modules during HIR lowering,
//! enabling compile-time type checking for imports like `import a.{ShapeError}`.

use simple_parser::ast::{ImportTarget, ModulePath, Node};
use std::path::PathBuf;

use super::super::types::{HirType, TypeId};
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use crate::CompileError;

impl Lowerer {
    /// Load type definitions from an imported module into the globals symbol table.
    ///
    /// This enables compile-time type checking for imports like:
    /// ```simple
    /// import verification.models.tensor_dimensions.{ShapeError, Dim}
    /// ```
    ///
    /// The function:
    /// 1. Resolves the module path to a filesystem location
    /// 2. Parses the .spl file
    /// 3. Extracts type definitions (classes, enums, structs)
    /// 4. Adds them to self.globals HashMap
    ///
    /// # Arguments
    /// * `module_path` - The module path from the import statement
    /// * `target` - The import target (what symbols to import)
    ///
    /// # Returns
    /// Ok(()) if successful, Err if module can't be loaded or parsed
    pub(super) fn load_imported_types(&mut self, module_path: &ModulePath, target: &ImportTarget) -> LowerResult<()> {
        // Only proceed if we have a module resolver
        let (resolver, current_file) = match (&self.module_resolver, &self.current_file) {
            (Some(r), Some(f)) => (r, f),
            _ => {
                // No module resolver available - skip type loading
                return Ok(());
            }
        };

        // Resolve module path to filesystem location
        let resolved = resolver
            .resolve(module_path, current_file)
            .map_err(|e| LowerError::ModuleResolution(format!("{:?}", e)))?;

        // Prevent circular imports
        if self.loaded_modules.contains(&resolved.path) {
            return Ok(()); // Already loaded
        }
        self.loaded_modules.insert(resolved.path.clone());

        // Read and parse the module file
        let source = std::fs::read_to_string(&resolved.path).map_err(|e| {
            LowerError::ModuleResolution(format!("Failed to read module file {:?}: {}", resolved.path, e))
        })?;

        let mut parser = simple_parser::Parser::new(&source);
        let imported_module = parser
            .parse()
            .map_err(|e| LowerError::ModuleResolution(format!("Failed to parse module: {}", e)))?;

        // Extract and register type definitions
        for item in &imported_module.items {
            match item {
                Node::Class(class_def) => {
                    if self.should_import_symbol(&class_def.name, target) {
                        // Register class type using existing type registration
                        let class_type_id = self.register_class(class_def)?;
                        self.globals.insert(class_def.name.clone(), class_type_id);
                    }
                }
                Node::Enum(enum_def) => {
                    if self.should_import_symbol(&enum_def.name, target) {
                        let variants = enum_def
                            .variants
                            .iter()
                            .map(|v| {
                                let fields = v.fields.as_ref().map(|enum_fields| {
                                    enum_fields
                                        .iter()
                                        .map(|f| self.resolve_type(&f.ty).unwrap_or(TypeId::VOID))
                                        .collect()
                                });
                                (v.name.clone(), fields)
                            })
                            .collect();
                        self.module.types.register_named(
                            enum_def.name.clone(),
                            HirType::Enum {
                                name: enum_def.name.clone(),
                                variants,
                                generic_params: enum_def.generic_params.clone(),
                                is_generic_template: enum_def.is_generic_template,
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                    }
                }
                Node::Struct(struct_def) => {
                    if self.should_import_symbol(&struct_def.name, target) {
                        let struct_type_id = self.register_struct(struct_def)?;
                        self.globals.insert(struct_def.name.clone(), struct_type_id);
                    }
                }
                Node::Function(func_def) => {
                    if self.should_import_symbol(&func_def.name, target) {
                        let ret_ty = self.resolve_type_opt(&func_def.return_type)?;
                        self.globals.insert(func_def.name.clone(), ret_ty);
                        if func_def.is_pure() {
                            self.pure_functions.insert(func_def.name.clone());
                        }
                    }
                }
                Node::TypeAlias(type_alias) => {
                    if self.should_import_symbol(&type_alias.name, target) {
                        self.register_type_alias(type_alias)?;
                    }
                }
                Node::Trait(trait_def) => {
                    if self.should_import_symbol(&trait_def.name, target) {
                        self.register_trait(trait_def)?;
                    }
                }
                Node::Static(static_stmt) => {
                    if self.should_import_symbol(&static_stmt.name, target) {
                        let ty = if let Some(ref t) = static_stmt.ty {
                            self.resolve_type(t).unwrap_or(TypeId::ANY)
                        } else {
                            TypeId::ANY
                        };
                        self.globals.insert(static_stmt.name.clone(), ty);
                    }
                }
                Node::Const(const_stmt) => {
                    if self.should_import_symbol(&const_stmt.name, target) {
                        let ty = if let Some(ref t) = const_stmt.ty {
                            self.resolve_type(t).unwrap_or(TypeId::ANY)
                        } else {
                            TypeId::ANY
                        };
                        self.globals.insert(const_stmt.name.clone(), ty);
                    }
                }
                Node::Let(let_stmt) => {
                    let name = match &let_stmt.pattern {
                        simple_parser::Pattern::Identifier(n) => Some(n.clone()),
                        simple_parser::Pattern::MutIdentifier(n) => Some(n.clone()),
                        _ => None,
                    };
                    if let Some(n) = name {
                        if self.should_import_symbol(&n, target) {
                            let ty = if let Some(ref t) = let_stmt.ty {
                                self.resolve_type(t).unwrap_or(TypeId::ANY)
                            } else {
                                TypeId::ANY
                            };
                            self.globals.insert(n, ty);
                        }
                    }
                }
                Node::Impl(impl_block) => {
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(ref type_name) = type_name {
                        if self.should_import_symbol(type_name, target) {
                            for method in &impl_block.methods {
                                let ret_ty = self.resolve_type_opt(&method.return_type)?;
                                let method_full_name = format!("{}.{}", type_name, method.name);
                                self.globals.insert(method_full_name, ret_ty);
                                if method.is_pure() {
                                    self.pure_functions.insert(format!("{}.{}", type_name, method.name));
                                }
                            }
                        }
                    }
                }
                Node::Extern(extern_fn) => {
                    if self.should_import_symbol(&extern_fn.name, target) {
                        let ret_ty = self.resolve_type_opt(&extern_fn.return_type)?;
                        self.globals.insert(extern_fn.name.clone(), ret_ty);
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Check if a symbol should be imported based on the import target.
    fn should_import_symbol(&self, name: &str, target: &ImportTarget) -> bool {
        match target {
            ImportTarget::Glob => true,           // Import everything
            ImportTarget::Single(n) => n == name, // Import if matches
            ImportTarget::Group(targets) => {
                // Check if any target in the group matches
                targets.iter().any(|t| self.should_import_symbol(name, t))
            }
            ImportTarget::Aliased { name: n, .. } => n == name, // Import if matches (will be aliased later)
        }
    }
}
