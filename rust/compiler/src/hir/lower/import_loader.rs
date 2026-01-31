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
        eprintln!(
            "[DEBUG import_loader] load_imported_types called for path: {:?}, target: {:?}",
            module_path, target
        );

        // Only proceed if we have a module resolver
        let (resolver, current_file) = match (&self.module_resolver, &self.current_file) {
            (Some(r), Some(f)) => (r, f),
            _ => {
                eprintln!("[DEBUG import_loader] No module resolver available, skipping");
                // No module resolver available - skip type loading
                // This maintains backward compatibility with existing code
                return Ok(());
            }
        };

        // Resolve module path to filesystem location
        eprintln!("[DEBUG import_loader] Resolving path from file: {:?}", current_file);
        let resolved = resolver.resolve(module_path, current_file).map_err(|e| {
            eprintln!("[DEBUG import_loader] Resolution failed: {:?}", e);
            LowerError::ModuleResolution(format!("{:?}", e))
        })?;
        eprintln!("[DEBUG import_loader] Resolved to: {:?}", resolved.path);

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

                        // Also register the class constructor as a function in globals
                        // This allows using the class name as a constructor: MyClass(...)
                        self.globals.insert(class_def.name.clone(), class_type_id);
                    }
                }
                Node::Enum(enum_def) => {
                    if self.should_import_symbol(&enum_def.name, target) {
                        // Register enum type (similar to what module_lowering does)
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
                        // Register struct type using existing type registration
                        let struct_type_id = self.register_struct(struct_def)?;

                        // Also register the struct constructor as a function in globals
                        // This allows using the struct name as a constructor: BlockExample(...)
                        eprintln!(
                            "[DEBUG import_loader] Registering struct constructor: '{}' with TypeId {:?}",
                            struct_def.name, struct_type_id
                        );
                        self.globals.insert(struct_def.name.clone(), struct_type_id);
                    }
                }
                Node::Function(func_def) => {
                    eprintln!(
                        "[DEBUG import_loader] Found function: '{}', checking if should import",
                        func_def.name
                    );
                    if self.should_import_symbol(&func_def.name, target) {
                        eprintln!("[DEBUG import_loader] Importing function: '{}'", func_def.name);
                        // Register function in globals
                        let ret_ty = self.resolve_type_opt(&func_def.return_type)?;
                        self.globals.insert(func_def.name.clone(), ret_ty);
                        // Track pure functions
                        if func_def.is_pure() {
                            self.pure_functions.insert(func_def.name.clone());
                        }
                    } else {
                        eprintln!(
                            "[DEBUG import_loader] Skipping function: '{}' (not matching target)",
                            func_def.name
                        );
                    }
                }
                Node::TypeAlias(type_alias) => {
                    if self.should_import_symbol(&type_alias.name, target) {
                        // Register type alias using existing type registration
                        self.register_type_alias(type_alias)?;
                    }
                }
                Node::Trait(trait_def) => {
                    if self.should_import_symbol(&trait_def.name, target) {
                        // Register trait using existing trait registration
                        self.register_trait(trait_def)?;
                    }
                }
                Node::Static(static_stmt) => {
                    if self.should_import_symbol(&static_stmt.name, target) {
                        // Register static/global variable
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
                        // Register constant
                        let ty = if let Some(ref t) = const_stmt.ty {
                            self.resolve_type(t).unwrap_or(TypeId::ANY)
                        } else {
                            TypeId::ANY
                        };
                        self.globals.insert(const_stmt.name.clone(), ty);
                    }
                }
                Node::Let(let_stmt) => {
                    // Handle module-level let (global variable)
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
                    // Handle impl blocks - register methods as functions
                    // Extract the type name from the impl block's target
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(ref type_name) = type_name {
                        // Check if this type is being imported
                        if self.should_import_symbol(type_name, target) {
                            eprintln!("[DEBUG import_loader] Processing impl block for type: '{}'", type_name);

                            // Register all methods from the impl block
                            for method in &impl_block.methods {
                                eprintln!(
                                    "[DEBUG import_loader] Registering method: '{}.{}'",
                                    type_name, method.name
                                );

                                // Register method in globals (methods are functions)
                                let ret_ty = self.resolve_type_opt(&method.return_type)?;
                                let method_full_name = format!("{}.{}", type_name, method.name);
                                self.globals.insert(method_full_name, ret_ty);

                                // Track pure functions
                                if method.is_pure() {
                                    self.pure_functions.insert(format!("{}.{}", type_name, method.name));
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Check if a symbol should be imported based on the import target.
    ///
    /// # Arguments
    /// * `name` - Symbol name to check
    /// * `target` - Import target specification
    ///
    /// # Returns
    /// true if the symbol should be imported
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
