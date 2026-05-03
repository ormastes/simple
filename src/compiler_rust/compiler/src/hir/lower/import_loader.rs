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
    fn import_target_exports_name(target: &ImportTarget, name: &str) -> bool {
        match target {
            ImportTarget::Glob => true,
            ImportTarget::Single(item) => item == name,
            ImportTarget::Aliased { name: item, alias } => item == name || alias == name,
            ImportTarget::Group(items) => items.iter().any(|item| Self::import_target_exports_name(item, name)),
        }
    }

    fn import_target_intersects(requested: &ImportTarget, available: &ImportTarget) -> bool {
        let mut requested_names = Vec::new();
        Self::requested_import_names(requested, &mut requested_names);
        if requested_names.is_empty() {
            return true;
        }

        requested_names
            .iter()
            .any(|name| Self::import_target_exports_name(available, name))
    }

    fn resolve_import_target_module_path(module_path: &ModulePath, target: &ImportTarget) -> Option<ModulePath> {
        match target {
            ImportTarget::Single(name) | ImportTarget::Aliased { name, .. } => {
                let mut module_segments = module_path.segments.clone();
                module_segments.push(name.clone());
                Some(ModulePath::new(module_segments))
            }
            _ => None,
        }
    }

    fn resolve_imported_module_path(
        &self,
        resolver: &crate::module_resolver::ModuleResolver,
        current_file: &std::path::Path,
        module_path: &ModulePath,
        target: &ImportTarget,
    ) -> LowerResult<crate::module_resolver::ResolvedModule> {
        if let Some(candidate_path) = Self::resolve_import_target_module_path(module_path, target) {
            if let Ok(resolved) = resolver.resolve(&candidate_path, current_file) {
                return Ok(resolved);
            }
        }

        resolver
            .resolve(module_path, current_file)
            .map_err(|e| LowerError::ModuleResolution(format!("{:?}", e)))
    }

    fn load_reexported_symbols_from_items(&mut self, items: &[Node], target: &ImportTarget) -> LowerResult<usize> {
        let mut imported_count = 0;

        for item in items {
            match item {
                Node::UseStmt(use_stmt) => {
                    if Self::import_target_intersects(target, &use_stmt.target) {
                        self.load_imported_types(&use_stmt.path, &use_stmt.target)?;
                        imported_count += 1;
                    }
                }
                Node::MultiUse(multi_use) => {
                    for (path, nested_target) in &multi_use.imports {
                        if Self::import_target_intersects(target, nested_target) {
                            self.load_imported_types(path, nested_target)?;
                            imported_count += 1;
                        }
                    }
                }
                Node::ExportUseStmt(export_use) => {
                    if Self::import_target_intersects(target, &export_use.target) {
                        self.load_imported_types(&export_use.path, &export_use.target)?;
                        imported_count += 1;
                    }
                }
                _ => {}
            }
        }

        Ok(imported_count)
    }

    fn preregister_imported_type_placeholder(&mut self, item: &Node) {
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
            Node::Bitfield(bitfield_def) => {
                if self.module.types.lookup(&bitfield_def.name).is_none() {
                    self.module.types.register_named(
                        bitfield_def.name.clone(),
                        HirType::Bitfield {
                            name: bitfield_def.name.clone(),
                            backing: TypeId::U64,
                            fields: vec![],
                            generic_params: Vec::new(),
                            is_generic_template: false,
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

    fn aliased_import_pairs(target: &ImportTarget, out: &mut Vec<(String, String)>) {
        match target {
            ImportTarget::Glob | ImportTarget::Single(_) => {}
            ImportTarget::Aliased { name, alias } => out.push((name.clone(), alias.clone())),
            ImportTarget::Group(targets) => {
                for nested in targets {
                    Self::aliased_import_pairs(nested, out);
                }
            }
        }
    }

    fn item_defines_symbol(item: &Node, name: &str) -> bool {
        match item {
            Node::Class(class_def) => class_def.name == name,
            Node::Struct(struct_def) => struct_def.name == name,
            Node::Bitfield(bitfield_def) => bitfield_def.name == name,
            Node::Enum(enum_def) => enum_def.name == name,
            Node::Function(func_def) => func_def.name == name,
            Node::TypeAlias(type_alias) => type_alias.name == name,
            Node::Trait(trait_def) => trait_def.name == name,
            Node::Static(static_stmt) => static_stmt.name == name,
            Node::Const(const_stmt) => const_stmt.name == name,
            Node::Let(let_stmt) => match &let_stmt.pattern {
                simple_parser::Pattern::Identifier(binding) | simple_parser::Pattern::MutIdentifier(binding) => {
                    binding == name
                }
                _ => false,
            },
            Node::Extern(extern_fn) => extern_fn.name == name,
            _ => false,
        }
    }

    fn item_defines_type_like_symbol(item: &Node, name: &str) -> bool {
        match item {
            Node::Class(class_def) => class_def.name == name,
            Node::Struct(struct_def) => struct_def.name == name,
            Node::Bitfield(bitfield_def) => bitfield_def.name == name,
            Node::Enum(enum_def) => enum_def.name == name,
            Node::TypeAlias(type_alias) => type_alias.name == name,
            Node::Trait(trait_def) => trait_def.name == name,
            _ => false,
        }
    }

    fn item_defines_callable_symbol(item: &Node, name: &str) -> bool {
        match item {
            Node::Function(func_def) => func_def.name == name,
            Node::Extern(extern_fn) => extern_fn.name == name,
            _ => false,
        }
    }

    fn materialize_import_aliases(&mut self, items: &[Node], target: &ImportTarget) {
        let mut aliases = Vec::new();
        Self::aliased_import_pairs(target, &mut aliases);

        for (original_name, alias_name) in aliases {
            if alias_name == original_name {
                continue;
            }
            if !items.iter().any(|item| Self::item_defines_symbol(item, &original_name)) {
                continue;
            }

            let is_type_like = items
                .iter()
                .any(|item| Self::item_defines_type_like_symbol(item, &original_name));
            if is_type_like {
                if let Some(type_id) = self.module.types.lookup(&original_name) {
                    self.module.types.register_alias(alias_name.clone(), type_id);
                    self.register_type_alias_mapping(alias_name.clone(), original_name.clone());
                    self.globals.insert(alias_name.clone(), type_id);
                }
            }

            if let Some(symbol_ty) = self.globals.get(&original_name).copied() {
                self.globals.insert(alias_name.clone(), symbol_ty);
            }

            let is_callable = items
                .iter()
                .any(|item| Self::item_defines_callable_symbol(item, &original_name));
            if is_callable {
                self.register_function_alias(alias_name.clone(), original_name.clone());
                if self.imported_function_names.contains(&original_name) {
                    self.imported_function_names.insert(alias_name.clone());
                }
                if self.extern_fn_names.contains(&original_name) {
                    self.extern_fn_names.insert(alias_name.clone());
                }
                if self.pure_functions.contains(&original_name) {
                    self.pure_functions.insert(alias_name);
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
            let type_pat = format!("type {}", name);
            let class_pat = format!("class {}", name);
            let struct_pat = format!("struct {}", name);
            let enum_pat = format!("enum {}", name);
            let trait_pat = format!("trait {}", name);
            let let_pat = format!("let {}", name);
            let const_pat = format!("const {}", name);
            source.contains(&fn_pat)
                || source.contains(&extern_pat)
                || source.contains(&type_pat)
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
            self.preregister_imported_type_placeholder(item);
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
                Node::Bitfield(bitfield_def) => {
                    if self.should_import_symbol(&bitfield_def.name, target) {
                        let bitfield_type_id = self.register_bitfield(bitfield_def)?;
                        self.globals.insert(bitfield_def.name.clone(), bitfield_type_id);
                        imported_count += 1;
                    }
                }
                Node::Function(func_def) => {
                    if self.should_import_symbol(&func_def.name, target) {
                        let ret_ty = self.resolve_type_opt(&func_def.return_type)?;
                        self.globals.insert(func_def.name.clone(), ret_ty);
                        self.method_return_types.insert(func_def.name.clone(), ret_ty);
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
                                self.method_return_types.insert(method_full_name.clone(), ret_ty);
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
                        self.method_return_types.insert(extern_fn.name.clone(), ret_ty);
                        // Imported externs participate in function-value lowering via
                        // HIR globals, but they are still function symbols and must be
                        // tracked as such so later MIR/LLVM stages do not redeclare
                        // them as data globals.
                        self.extern_fn_names.insert(extern_fn.name.clone());
                        imported_count += 1;
                    }
                }
                _ => {}
            }
        }

        // Intra-file Pass 2: Transitive type resolution
        // After Pass 1 fully registers imported types, some of their fields may
        // reference types that are still placeholders (0 fields). For example,
        // if layout.spl imports {StyleProps} from css.spl, StyleProps gets fully
        // registered with its fields, but StyleProps.border has type BorderProps
        // which is still a placeholder. This pass finds those placeholder
        // dependencies and fully registers them too.
        // Repeat until no new types are registered (handles multi-level chains
        // like StyleProps -> BorderProps -> BoxEdges). Bounded to 10 iterations.
        let mut transitive_processed: std::collections::HashSet<String> = std::collections::HashSet::new();
        for _iteration in 0..10 {
            // Collect names of types that need full registration:
            // They are referenced by a field of a fully-registered struct,
            // but are themselves still placeholders (0 fields).
            let mut needs_registration: Vec<String> = Vec::new();

            for (_tid, hir_ty) in self.module.types.iter() {
                if let HirType::Struct { fields, .. } = hir_ty {
                    if fields.is_empty() {
                        continue; // This is itself a placeholder, skip
                    }
                    for (_field_name, field_type_id) in fields {
                        if let Some(HirType::Struct {
                            name: ref dep_name,
                            fields: ref dep_fields,
                            ..
                        }) = self.module.types.get(*field_type_id)
                        {
                            if dep_fields.is_empty() && !transitive_processed.contains(dep_name) {
                                needs_registration.push(dep_name.clone());
                            }
                        }
                        // Also check enum placeholders (0 variants)
                        if let Some(HirType::Enum {
                            name: ref dep_name,
                            variants: ref dep_variants,
                            ..
                        }) = self.module.types.get(*field_type_id)
                        {
                            if dep_variants.is_empty() && !transitive_processed.contains(dep_name) {
                                needs_registration.push(dep_name.clone());
                            }
                        }
                    }
                }
            }

            needs_registration.sort();
            needs_registration.dedup();

            if needs_registration.is_empty() {
                break; // All transitive dependencies resolved
            }

            let mut registered_any = false;
            for name in &needs_registration {
                transitive_processed.insert(name.clone());
                // Find the matching definition in the imported items and fully register it
                for item in items {
                    match item {
                        Node::Class(class_def) if class_def.name == *name => {
                            if let Ok(type_id) = self.register_class(class_def) {
                                self.globals.insert(class_def.name.clone(), type_id);
                                registered_any = true;
                            }
                        }
                        Node::Struct(struct_def) if struct_def.name == *name => {
                            if let Ok(type_id) = self.register_struct(struct_def) {
                                self.globals.insert(struct_def.name.clone(), type_id);
                                registered_any = true;
                            }
                        }
                        Node::Enum(enum_def) if enum_def.name == *name => {
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
                            registered_any = true;
                        }
                        _ => {}
                    }
                }
            }

            if !registered_any {
                break; // No progress — remaining placeholders aren't in this file
            }
        }

        imported_count += self.load_reexported_symbols_from_items(items, target)?;
        self.materialize_import_aliases(items, target);

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
    pub(super) fn preregister_imported_type_names(
        &mut self,
        module_path: &ModulePath,
        target: &ImportTarget,
    ) -> LowerResult<()> {
        // Only proceed if we have a module resolver
        let (resolver, current_file) = match (&self.module_resolver, &self.current_file) {
            (Some(r), Some(f)) => (r, f),
            _ => return Ok(()),
        };

        // Resolve module path to filesystem location
        let resolved = match self.resolve_imported_module_path(resolver, current_file, module_path, target) {
            Ok(r) => r,
            Err(_) => return Ok(()), // Silently skip unresolvable modules
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

        let previous_file = self.current_file.clone();
        self.current_file = Some(resolved.path.clone());

        // Pre-register type names as empty placeholders
        for item in &imported_module.items {
            self.preregister_imported_type_placeholder(item);
        }

        // Also pre-register types from sibling files in the same package
        if resolved.path.file_name().is_some_and(|name| name == "__init__.spl") {
            let _ = self.preregister_type_names_from_package_siblings(&resolved.path, target);
        }

        self.current_file = previous_file;

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
                        && path
                            .file_name()
                            .is_some_and(|name| name != "__init__.spl" && name != "mod_stub.spl")
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
                self.preregister_imported_type_placeholder(item);
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
        let resolved = self.resolve_imported_module_path(resolver, current_file, module_path, target)?;

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

        let previous_file = self.current_file.clone();
        self.current_file = Some(resolved.path.clone());

        let result = (|| {
            let imported_count = self.register_imported_symbols_from_items(&imported_module.items, target)?;

            if imported_count == 0 && resolved.path.file_name().is_some_and(|name| name == "__init__.spl") {
                let _ = self.load_imported_symbols_from_package_siblings(&resolved.path, target)?;
            }

            Ok(())
        })();

        self.current_file = previous_file;
        result
    }

    /// Check if a symbol should be imported based on the import target.
    #[allow(clippy::only_used_in_recursion)] // reason: parameter threaded for consistency with sibling function signatures
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::lower::error::LowerError;
    use crate::hir::lower::lowerer::Lowerer;
    use crate::hir::types::{HirExprKind, HirStmt, TypeId};
    use crate::module_resolver::ModuleResolver;
    use crate::test_helpers::create_test_project;
    use simple_parser::Parser;
    use std::fs;

    #[test]
    fn lowers_field_access_through_reexported_use_shim() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let app_io = src.join("app").join("io");
        let app_cli = src.join("app").join("cli");
        fs::create_dir_all(&app_io).unwrap();
        fs::create_dir_all(&app_cli).unwrap();

        fs::write(
            app_io.join("process_ops.spl"),
            r#"
struct ProcessResult:
    stdout: text
    stderr: text
    exit_code: i64

fn shell(cmd: text) -> ProcessResult:
    ProcessResult(stdout: cmd, stderr: "", exit_code: 0)
"#,
        )
        .unwrap();
        fs::write(
            app_io.join("mod.spl"),
            "use app.io.process_ops.{ProcessResult, shell}\n",
        )
        .unwrap();
        let main_path = app_cli.join("main.spl");
        fs::write(
            &main_path,
            r#"
use app.io.mod (shell)

fn test() -> i64:
    val result = shell("echo hi")
    result.exit_code
"#,
        )
        .unwrap();

        let source = fs::read_to_string(&main_path).unwrap();
        let mut parser = Parser::new(&source);
        let ast = parser.parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let mut lowerer = Lowerer::with_module_resolver(resolver, main_path.clone());
        let lowered = lowerer.lower_module(&ast).expect("HIR lowering should succeed");

        let func = lowered
            .functions
            .iter()
            .find(|func| func.name == "test")
            .expect("test function");
        match &func.body[1] {
            HirStmt::Expr(expr) => {
                assert_eq!(expr.ty, TypeId::I64);
                assert!(matches!(expr.kind, HirExprKind::FieldAccess { .. }));
            }
            other => panic!("expected field access expression, got {other:?}"),
        }
    }

    #[test]
    fn import_target_intersection_matches_group_reexports() {
        let requested = ImportTarget::Single("shell".to_string());
        let available = ImportTarget::Group(vec![
            ImportTarget::Single("process_output".to_string()),
            ImportTarget::Single("shell".to_string()),
        ]);
        assert!(Lowerer::import_target_intersects(&requested, &available));
    }
}
