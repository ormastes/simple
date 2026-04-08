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
    fn requested_import_names(target: &ImportTarget, out: &mut Vec<String>) {
        match target {
            ImportTarget::Glob => {}
            ImportTarget::Single(name) => out.push(name.clone()),
            ImportTarget::Aliased { name, .. } => out.push(name.clone()),
            ImportTarget::Group(targets) => {
                for nested in targets {
                    Self::requested_import_names(nested, out);
                }
            }
        }
    }

    fn file_might_define_requested_symbol(path: &std::path::Path, requested_names: &[String]) -> bool {
        if requested_names.is_empty() {
            return true;
        }

        let Ok(source) = std::fs::read_to_string(path) else {
            return false;
        };

        requested_names.iter().any(|name| {
            let fn_pat = format!("fn {}(", name);
            let extern_pat = format!("extern fn {}(", name);
            let class_pat = format!("class {}", name);
            let struct_pat = format!("struct {}", name);
            let enum_pat = format!("enum {}", name);
            let trait_pat = format!("trait {}", name);
            let let_pat = format!("let {}", name);
            let const_pat = format!("const {}", name);
            source.contains(&fn_pat)
                || source.contains(&extern_pat)
                || source.contains(&class_pat)
                || source.contains(&struct_pat)
                || source.contains(&enum_pat)
                || source.contains(&trait_pat)
                || source.contains(&let_pat)
                || source.contains(&const_pat)
        })
    }

    fn register_imported_symbols_from_items(&mut self, items: &[Node], target: &ImportTarget) -> LowerResult<usize> {
        let mut imported_count = 0;

        // Intra-file Pass 0: Pre-register ALL struct/class/enum names from this
        // file as empty placeholders. This ensures that when a type references
        // another type defined later in the same file (e.g., StyleProps references
        // BorderProps which is defined earlier but BoxShadow which might be defined
        // later), the referenced type is already in the registry.
        // We register ALL types, not just imported ones, because imported types
        // may have fields that reference non-imported types from the same file.
        for item in items {
            match item {
                Node::Class(class_def) => {
                    if self.module.types.lookup(&class_def.name).is_none() {
                        self.module.types.register_named(
                            class_def.name.clone(),
                            HirType::Struct {
                                name: class_def.name.clone(),
                                fields: vec![],
                                has_snapshot: false,
                                generic_params: class_def.generic_params.clone(),
                                is_generic_template: class_def.is_generic_template,
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                    }
                }
                Node::Struct(struct_def) => {
                    if self.module.types.lookup(&struct_def.name).is_none() {
                        self.module.types.register_named(
                            struct_def.name.clone(),
                            HirType::Struct {
                                name: struct_def.name.clone(),
                                fields: vec![],
                                has_snapshot: false,
                                generic_params: struct_def.generic_params.clone(),
                                is_generic_template: struct_def.is_generic_template,
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                    }
                }
                Node::Enum(enum_def) => {
                    if self.module.types.lookup(&enum_def.name).is_none() {
                        self.module.types.register_named(
                            enum_def.name.clone(),
                            HirType::Enum {
                                name: enum_def.name.clone(),
                                variants: vec![],
                                generic_params: enum_def.generic_params.clone(),
                                is_generic_template: enum_def.is_generic_template,
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                    }
                }
                _ => {}
            }
        }

        // Intra-file Pass 1: Full registration of imported symbols with field resolution
        for item in items {
            match item {
                Node::Class(class_def) => {
                    if self.should_import_symbol(&class_def.name, target) {
                        let class_type_id = self.register_class(class_def)?;
                        self.globals.insert(class_def.name.clone(), class_type_id);
                        imported_count += 1;
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
                        // Use update_named to update the placeholder created in Pass 0
                        // (keeps the same TypeId so earlier references stay valid)
                        self.module.types.update_named(
                            enum_def.name.clone(),
                            HirType::Enum {
                                name: enum_def.name.clone(),
                                variants,
                                generic_params: enum_def.generic_params.clone(),
                                is_generic_template: enum_def.is_generic_template,
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                        imported_count += 1;
                    }
                }
                Node::Struct(struct_def) => {
                    if self.should_import_symbol(&struct_def.name, target) {
                        let struct_type_id = self.register_struct(struct_def)?;
                        self.globals.insert(struct_def.name.clone(), struct_type_id);
                        imported_count += 1;
                    }
                }
                Node::Function(func_def) => {
                    if self.should_import_symbol(&func_def.name, target) {
                        let ret_ty = self.resolve_type_opt(&func_def.return_type)?;
                        self.globals.insert(func_def.name.clone(), ret_ty);
                        self.imported_function_names.insert(func_def.name.clone());
                        if func_def.is_pure() {
                            self.pure_functions.insert(func_def.name.clone());
                        }
                        imported_count += 1;
                    }
                }
                Node::TypeAlias(type_alias) => {
                    if self.should_import_symbol(&type_alias.name, target) {
                        self.register_type_alias(type_alias)?;
                        imported_count += 1;
                    }
                }
                Node::Trait(trait_def) => {
                    if self.should_import_symbol(&trait_def.name, target) {
                        self.register_trait(trait_def)?;
                        imported_count += 1;
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
                        imported_count += 1;
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
                        imported_count += 1;
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
                            imported_count += 1;
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
                                self.globals.insert(method_full_name.clone(), ret_ty);
                                // Mark as imported function so MIR lowering skips it as a global
                                // (prevents IncompatibleDeclaration when codegen declares it as data)
                                self.imported_function_names.insert(method_full_name);
                                if method.is_pure() {
                                    self.pure_functions.insert(format!("{}.{}", type_name, method.name));
                                }
                            }
                            imported_count += 1;
                        }
                    }
                }
                Node::Extern(extern_fn) => {
                    if self.should_import_symbol(&extern_fn.name, target) {
                        let ret_ty = self.resolve_type_opt(&extern_fn.return_type)?;
                        self.globals.insert(extern_fn.name.clone(), ret_ty);
                        imported_count += 1;
                    }
                }
                _ => {}
            }
        }

        Ok(imported_count)
    }

    fn load_imported_symbols_from_package_siblings(
        &mut self,
        package_init_path: &std::path::Path,
        target: &ImportTarget,
    ) -> LowerResult<usize> {
        let Some(package_dir) = package_init_path.parent() else {
            return Ok(0);
        };

        let mut requested_names = Vec::new();
        Self::requested_import_names(target, &mut requested_names);

        let mut sibling_files: Vec<PathBuf> = match std::fs::read_dir(package_dir) {
            Ok(entries) => entries
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|path| {
                    path.extension().is_some_and(|ext| ext == "spl")
                        && path
                            .file_name()
                            .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                        && path.is_file()
                        && Self::file_might_define_requested_symbol(path, &requested_names)
                })
                .collect(),
            Err(_) => return Ok(0),
        };

        sibling_files.sort();

        let mut imported_count = 0;
        for sibling_path in sibling_files {
            if self.loaded_modules.contains(&sibling_path) {
                continue;
            }
            self.loaded_modules.insert(sibling_path.clone());

            let mut source = std::fs::read_to_string(&sibling_path).map_err(|e| {
                LowerError::ModuleResolution(format!("Failed to read sibling module file {:?}: {}", sibling_path, e))
            })?;
            if source.contains('\r') {
                source = source.replace('\r', "");
            }

            let mut parser = simple_parser::Parser::new(&source);
            let sibling_module = parser
                .parse()
                .map_err(|e| LowerError::ModuleResolution(format!("Failed to parse sibling module: {}", e)))?;

            imported_count += self.register_imported_symbols_from_items(&sibling_module.items, target)?;
        }

        Ok(imported_count)
    }

    /// Pre-register struct/class/enum names from an imported module as placeholder types.
    ///
    /// This is the first pass of a two-pass import loading strategy:
    /// 1. Pre-register all type names (this method) — empty placeholders
    /// 2. Full import loading (load_imported_types) — resolves field types
    ///
    /// The two-pass approach fixes cross-module type ordering bugs where module A
    /// defines a struct with a field whose type is defined in module B. Without
    /// pre-registration, when A is loaded first, B's types aren't available yet
    /// and field types resolve to VOID.
    ///
    /// Example: dom.spl defines `BeDomNode { style: StyleProps }` where
    /// `StyleProps` is in css.spl. Pre-registering ensures StyleProps exists
    /// as a placeholder when BeDomNode's fields are resolved.
    pub(super) fn preregister_imported_type_names(&mut self, module_path: &ModulePath, target: &ImportTarget) -> LowerResult<()> {
        // Only proceed if we have a module resolver
        let (resolver, current_file) = match (&self.module_resolver, &self.current_file) {
            (Some(r), Some(f)) => (r, f),
            _ => return Ok(()),
        };

        // Resolve module path to filesystem location
        let resolved = match resolver.resolve(module_path, current_file) {
            Ok(r) => r,
            Err(_) => return Ok(()),  // Silently skip unresolvable modules
        };

        // Read and parse the module file
        let mut source = match std::fs::read_to_string(&resolved.path) {
            Ok(s) => s,
            Err(_) => return Ok(()),
        };
        if source.contains('\r') {
            source = source.replace('\r', "");
        }

        let mut parser = simple_parser::Parser::new(&source);
        let imported_module = match parser.parse() {
            Ok(m) => m,
            Err(_) => return Ok(()),
        };

        // Pre-register type names as empty placeholders
        for item in &imported_module.items {
            match item {
                Node::Class(class_def) => {
                    if self.should_import_symbol(&class_def.name, target) || matches!(target, ImportTarget::Glob) {
                        if self.module.types.lookup(&class_def.name).is_none() {
                            self.module.types.register_named(
                                class_def.name.clone(),
                                super::super::types::HirType::Struct {
                                    name: class_def.name.clone(),
                                    fields: vec![],
                                    has_snapshot: false,
                                    generic_params: class_def.generic_params.clone(),
                                    is_generic_template: class_def.is_generic_template,
                                    type_bindings: std::collections::HashMap::new(),
                                },
                            );
                        }
                    }
                }
                Node::Struct(struct_def) => {
                    if self.should_import_symbol(&struct_def.name, target) || matches!(target, ImportTarget::Glob) {
                        if self.module.types.lookup(&struct_def.name).is_none() {
                            self.module.types.register_named(
                                struct_def.name.clone(),
                                super::super::types::HirType::Struct {
                                    name: struct_def.name.clone(),
                                    fields: vec![],
                                    has_snapshot: false,
                                    generic_params: struct_def.generic_params.clone(),
                                    is_generic_template: struct_def.is_generic_template,
                                    type_bindings: std::collections::HashMap::new(),
                                },
                            );
                        }
                    }
                }
                Node::Enum(enum_def) => {
                    if self.should_import_symbol(&enum_def.name, target) || matches!(target, ImportTarget::Glob) {
                        if self.module.types.lookup(&enum_def.name).is_none() {
                            self.module.types.register_named(
                                enum_def.name.clone(),
                                super::super::types::HirType::Enum {
                                    name: enum_def.name.clone(),
                                    variants: vec![],
                                    generic_params: enum_def.generic_params.clone(),
                                    is_generic_template: enum_def.is_generic_template,
                                    type_bindings: std::collections::HashMap::new(),
                                },
                            );
                        }
                    }
                }
                _ => {}
            }
        }

        // Also pre-register types from sibling files in the same package
        if resolved.path.file_name().is_some_and(|name| name == "__init__.spl") {
            let _ = self.preregister_type_names_from_package_siblings(&resolved.path, target);
        }

        Ok(())
    }

    /// Pre-register type names from sibling files in a package directory.
    fn preregister_type_names_from_package_siblings(
        &mut self,
        package_init_path: &std::path::Path,
        target: &ImportTarget,
    ) -> LowerResult<()> {
        let Some(package_dir) = package_init_path.parent() else {
            return Ok(());
        };

        let mut sibling_files: Vec<PathBuf> = match std::fs::read_dir(package_dir) {
            Ok(entries) => entries
                .filter_map(|entry| entry.ok().map(|e| e.path()))
                .filter(|path| {
                    path.extension().is_some_and(|ext| ext == "spl")
                        && path.file_name().is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
                        && path.is_file()
                })
                .collect(),
            Err(_) => return Ok(()),
        };
        sibling_files.sort();

        for sibling_path in sibling_files {
            let mut source = match std::fs::read_to_string(&sibling_path) {
                Ok(s) => s,
                Err(_) => continue,
            };
            if source.contains('\r') {
                source = source.replace('\r', "");
            }

            let mut parser = simple_parser::Parser::new(&source);
            let sibling_module = match parser.parse() {
                Ok(m) => m,
                Err(_) => continue,
            };

            for item in &sibling_module.items {
                match item {
                    Node::Class(class_def) => {
                        if self.should_import_symbol(&class_def.name, target) || matches!(target, ImportTarget::Glob) {
                            if self.module.types.lookup(&class_def.name).is_none() {
                                self.module.types.register_named(
                                    class_def.name.clone(),
                                    super::super::types::HirType::Struct {
                                        name: class_def.name.clone(),
                                        fields: vec![],
                                        has_snapshot: false,
                                        generic_params: class_def.generic_params.clone(),
                                        is_generic_template: class_def.is_generic_template,
                                        type_bindings: std::collections::HashMap::new(),
                                    },
                                );
                            }
                        }
                    }
                    Node::Struct(struct_def) => {
                        if self.should_import_symbol(&struct_def.name, target) || matches!(target, ImportTarget::Glob) {
                            if self.module.types.lookup(&struct_def.name).is_none() {
                                self.module.types.register_named(
                                    struct_def.name.clone(),
                                    super::super::types::HirType::Struct {
                                        name: struct_def.name.clone(),
                                        fields: vec![],
                                        has_snapshot: false,
                                        generic_params: struct_def.generic_params.clone(),
                                        is_generic_template: struct_def.is_generic_template,
                                        type_bindings: std::collections::HashMap::new(),
                                    },
                                );
                            }
                        }
                    }
                    Node::Enum(enum_def) => {
                        if self.should_import_symbol(&enum_def.name, target) || matches!(target, ImportTarget::Glob) {
                            if self.module.types.lookup(&enum_def.name).is_none() {
                                self.module.types.register_named(
                                    enum_def.name.clone(),
                                    super::super::types::HirType::Enum {
                                        name: enum_def.name.clone(),
                                        variants: vec![],
                                        generic_params: enum_def.generic_params.clone(),
                                        is_generic_template: enum_def.is_generic_template,
                                        type_bindings: std::collections::HashMap::new(),
                                    },
                                );
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(())
    }

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
        let mut source = std::fs::read_to_string(&resolved.path).map_err(|e| {
            LowerError::ModuleResolution(format!("Failed to read module file {:?}: {}", resolved.path, e))
        })?;
        // Normalize CRLF → LF for cross-platform compatibility
        if source.contains('\r') {
            source = source.replace('\r', "");
        }

        let mut parser = simple_parser::Parser::new(&source);
        let imported_module = parser
            .parse()
            .map_err(|e| LowerError::ModuleResolution(format!("Failed to parse module: {}", e)))?;

        let imported_count = self.register_imported_symbols_from_items(&imported_module.items, target)?;

        if imported_count == 0 && resolved.path.file_name().is_some_and(|name| name == "__init__.spl") {
            let _ = self.load_imported_symbols_from_package_siblings(&resolved.path, target)?;
        }

        Ok(())
    }

    /// Check if a symbol should be imported based on the import target.
    #[allow(clippy::only_used_in_recursion)]
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
