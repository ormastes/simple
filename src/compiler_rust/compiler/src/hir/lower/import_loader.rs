//! Import type loading for cross-module type resolution.
//!
//! This module handles loading type definitions from imported modules during HIR lowering,
//! enabling compile-time type checking for imports like `import a.{ShapeError}`.

use simple_parser::ast::{Expr, ImportTarget, ModulePath, Node};
use std::path::{Path, PathBuf};

use super::super::types::{HirType, TypeId};
use super::error::{LowerError, LowerResult};
use super::lowerer::Lowerer;
use crate::CompileError;

thread_local! {
    /// Per-process memo of PARSED imported modules, keyed by resolved path.
    ///
    /// `preregister_imported_type_names` and `load_imported_types` each read AND
    /// fully re-parsed the imported file on every `use` that names it. Measured
    /// with a call-site read trace on a lint of a TWO-LINE file: 2,672 reads at
    /// the pre-register site and 611 at the load site out of 3,522 traced reads
    /// -- `10.frontend/core/ast.spl` alone parsed 749 + 121 times. Both sites
    /// consume the result immutably (`&imported_module.items`), and parsing is a
    /// deterministic function of the file's bytes, so one parse per path per
    /// process is observationally identical.
    ///
    /// `None` memoizes "unreadable or unparseable", which both sites previously
    /// recomputed on every visit (the pre-register site silently skips, the load
    /// site reports a module-resolution error).
    ///
    /// Per-PROCESS only -- a `src/lib/**` edit is still picked up by the next
    /// run, so the "edit stdlib, no build needed" property is unchanged.
    static IMPORTED_MODULE_AST: std::cell::RefCell<
        std::collections::HashMap<std::path::PathBuf, Option<std::sync::Arc<simple_parser::ast::Module>>>,
    > = std::cell::RefCell::new(std::collections::HashMap::new());
}

/// Read + parse an imported module, memoized per process. See `IMPORTED_MODULE_AST`.
pub(crate) fn parsed_imported_module(path: &std::path::Path) -> Option<std::sync::Arc<simple_parser::ast::Module>> {
    if let Some(hit) = IMPORTED_MODULE_AST.with(|c| c.borrow().get(path).cloned()) {
        crate::perf_counters::bump(&crate::perf_counters::IMPORT_AST_HITS, 1);
        return hit;
    }
    crate::perf_counters::bump(&crate::perf_counters::IMPORT_AST_PARSES, 1);
    let parsed = match crate::read_trace::rts(file!(), line!(), path) {
        Ok(mut source) => {
            if source.contains('\r') {
                source = source.replace('\r', "");
            }
            simple_parser::Parser::new(&source)
                .parse()
                .ok()
                .map(std::sync::Arc::new)
        }
        Err(_) => None,
    };
    IMPORTED_MODULE_AST.with(|c| c.borrow_mut().insert(path.to_path_buf(), parsed.clone()));
    parsed
}

/// Drop the imported-module parse memo.
pub(crate) fn clear_imported_module_ast_cache() {
    IMPORTED_MODULE_AST.with(|c| c.borrow_mut().clear());
}

impl Lowerer {
    fn import_target_cache_key(target: &ImportTarget) -> String {
        format!("{:?}", target)
    }

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

    fn is_non_addressable_root_import(module_path: &ModulePath, target: &ImportTarget) -> bool {
        module_path.segments.is_empty() && matches!(target, ImportTarget::Group(_) | ImportTarget::Glob)
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
                        if self.load_imported_types(&use_stmt.path, &use_stmt.target).is_ok() {
                            imported_count += 1;
                        }
                    }
                }
                Node::MultiUse(multi_use) => {
                    for (path, nested_target) in &multi_use.imports {
                        if Self::import_target_intersects(target, nested_target) {
                            if self.load_imported_types(path, nested_target).is_ok() {
                                imported_count += 1;
                            }
                        }
                    }
                }
                Node::ExportUseStmt(export_use) => {
                    if export_use.path.segments.is_empty() {
                        continue;
                    }
                    if Self::import_target_intersects(target, &export_use.target) {
                        if self.load_imported_types(&export_use.path, &export_use.target).is_ok() {
                            imported_count += 1;
                        }
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
            Node::Trait(trait_def) => {
                self.module.types.register_alias(trait_def.name.clone(), TypeId::ANY);
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
            Node::Let(let_stmt) => Self::extract_pattern_name(&let_stmt.pattern).as_deref() == Some(name),
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

        let Some(source) = crate::interpreter::probe_source_cached(path, u64::MAX) else {
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
                        } else if matches!(&const_stmt.value, Expr::Integer(_)) {
                            // Unannotated integer literal const → infer i64 so comparisons
                            // against imported consts don't fall into the ANY boxing path
                            // (bug: stage4_imported_const_compare)
                            TypeId::I64
                        } else if matches!(&const_stmt.value, Expr::String(_) | Expr::FString { .. }) {
                            TypeId::STRING
                        } else {
                            TypeId::ANY
                        };
                        self.globals.insert(const_stmt.name.clone(), ty);
                        imported_count += 1;
                    }
                }
                Node::Let(let_stmt) => {
                    let name = Self::extract_pattern_name(&let_stmt.pattern);
                    if let Some(n) = name {
                        if self.should_import_symbol(&n, target) {
                            let ty = if let Some(ref t) = let_stmt.ty {
                                self.resolve_type(t).unwrap_or(TypeId::ANY)
                            } else if let Some(t) = Self::extract_pattern_type(&let_stmt.pattern) {
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

            let mut source = crate::read_trace::rts(file!(), line!(), &sibling_path).map_err(|e| {
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
        if Self::is_non_addressable_root_import(module_path, target) {
            return Ok(());
        }

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

        // Read and parse the module file (memoized per process: this site
        // re-parsed the same imported module once per `use` that names it).
        let Some(imported_module) = parsed_imported_module(&resolved.path) else {
            return Ok(());
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
            let mut source = match crate::read_trace::rts(file!(), line!(), &sibling_path) {
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
        if Self::is_non_addressable_root_import(module_path, target) {
            return Ok(());
        }

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

        let import_key = (resolved.path.clone(), Self::import_target_cache_key(target));
        if self.loaded_import_targets.contains(&import_key) {
            return Ok(());
        }

        // Prevent circular imports while still allowing the same module to be
        // materialized later for a different target symbol group.
        //
        // `loaded_modules` is the ACTIVE import path, not a visited set: entries
        // are inserted before recursing and removed after. So reaching a module
        // that is already in it means we have walked an import cycle. That has
        // always been detected here; it was just absorbed silently. Record it so
        // the cycle is reportable, then keep the existing tolerate-and-continue
        // behaviour.
        //
        // `ModuleResolver::check_circular_dependencies` was the intended report
        // path but is unreachable: its `ImportGraph` is only ever fed by
        // `record_import`, whose sole callers are unit tests, so the production
        // graph is permanently empty and the check is a guaranteed `Ok(())`.
        // This is where the real graph is walked, so this is where the cycle is
        // observable.
        if self.loaded_modules.contains(&resolved.path) {
            self.record_import_cycle(&resolved.path);
            return Ok(());
        }
        self.loaded_modules.insert(resolved.path.clone());
        self.import_stack.push(resolved.path.clone());

        if resolved.path.extension().is_some_and(|ext| ext == "smf") {
            let result = self.load_types_from_smf(&resolved.path, target);
            self.import_stack.pop();
            self.loaded_modules.remove(&resolved.path);
            if result.is_ok() {
                self.loaded_import_targets.insert(import_key);
            }
            return result;
        }

        // Read and parse the module file (memoized per process, same rationale
        // as the pre-register site above).
        let imported_module = parsed_imported_module(&resolved.path).ok_or_else(|| {
            LowerError::ModuleResolution(format!("Failed to read or parse module file {:?}", resolved.path))
        })?;

        let previous_file = self.current_file.clone();
        self.current_file = Some(resolved.path.clone());

        let result = (|| {
            // Transitive type NAMES first, mirroring the entry module's Pass
            // 0.5a in module_pass.rs. Without this, only the ENTRY module's
            // `use` statements ever pre-registered names, so a symbol whose
            // signature mentions a type the IMPORTED module itself imports
            // (`trait InputBackend: me poll_mouse() -> MouseEvent?` in a module
            // that does `use input.event.{MouseEvent}`) failed with
            // `Unknown type: MouseEvent`, the whole import was abandoned with a
            // [WARN], and the value degraded to ANY -- which then fails every
            // later field access. Names only, and `preregister_imported_type_names`
            // is already cycle-safe, so this cannot recurse unboundedly.
            for item in &imported_module.items {
                if let Node::UseStmt(use_stmt) = item {
                    let _ = self.preregister_imported_type_names(&use_stmt.path, &use_stmt.target);
                }
            }
            // ...then their full definitions (Pass 0.5b's counterpart). The
            // name alone only yields an EMPTY placeholder struct, so field
            // access on it still fails; the fields have to come across too.
            // Cycle-guarded by `loaded_modules`/`loaded_import_targets` above,
            // and failures stay non-fatal here exactly as they are for the
            // entry module.
            for item in &imported_module.items {
                if let Node::UseStmt(use_stmt) = item {
                    let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
                }
            }

            let imported_count = self.register_imported_symbols_from_items(&imported_module.items, target)?;

            if imported_count == 0 && resolved.path.file_name().is_some_and(|name| name == "__init__.spl") {
                let _ = self.load_imported_symbols_from_package_siblings(&resolved.path, target)?;
            }

            Ok(())
        })();

        self.current_file = previous_file;
        self.import_stack.pop();
        self.loaded_modules.remove(&resolved.path);
        if result.is_ok() {
            self.loaded_import_targets.insert(import_key);
        }
        result
    }

    /// Record the import cycle that closes when `repeated` is re-entered while
    /// it is still on the active import path.
    ///
    /// The recorded cycle is the suffix of the active path starting at the
    /// earlier visit of `repeated`, closed by `repeated` itself, so it reads as
    /// `a -> b -> c -> a`. Duplicates are dropped: the same cycle is reached
    /// once per import target group, and reporting it many times would bury the
    /// distinct cycles.
    pub(super) fn record_import_cycle(&mut self, repeated: &Path) {
        let Some(start) = self.import_stack.iter().position(|p| p == repeated) else {
            // `repeated` is in `loaded_modules` but not on the ordered stack.
            // That happens for the sibling-package scan, which marks modules
            // visited without pushing them; there is no cycle to name.
            return;
        };

        let mut cycle: Vec<PathBuf> = self.import_stack[start..].to_vec();
        cycle.push(repeated.to_path_buf());

        if !self.import_cycles.contains(&cycle) {
            self.import_cycles.push(cycle);
        }
    }

    fn load_types_from_smf(&mut self, smf_path: &Path, target: &ImportTarget) -> LowerResult<()> {
        use simple_common::smf::{SectionType, SmfHeader, SmfSection, SmfSymbol, SymbolType};
        use std::io::{Read, Seek, SeekFrom};

        let mut file = std::fs::File::open(smf_path)
            .map_err(|e| LowerError::ModuleResolution(format!("Failed to open SMF {:?}: {}", smf_path, e)))?;

        let header = SmfHeader::read_trailer(&mut file)
            .map_err(|e| LowerError::ModuleResolution(format!("Failed to read SMF header {:?}: {}", smf_path, e)))?;

        if header.symbol_count == 0 {
            return Ok(());
        }

        let mut string_table = Vec::new();
        if header.section_count > 0 && header.section_table_offset > 0 {
            let sec_size = std::mem::size_of::<SmfSection>();
            if file.seek(SeekFrom::Start(header.section_table_offset)).is_ok() {
                let mut sec_buf = vec![0u8; sec_size * header.section_count as usize];
                if file.read_exact(&mut sec_buf).is_ok() {
                    for i in 0..header.section_count as usize {
                        let section: SmfSection =
                            unsafe { std::ptr::read(sec_buf[i * sec_size..].as_ptr() as *const SmfSection) };
                        if section.section_type == SectionType::StrTab && section.size > 0 {
                            if file.seek(SeekFrom::Start(section.offset)).is_ok() {
                                string_table.resize(section.size as usize, 0u8);
                                let _ = file.read_exact(&mut string_table);
                            }
                            break;
                        }
                    }
                }
            }
        }

        if string_table.is_empty() {
            return Ok(());
        }

        let sym_size = std::mem::size_of::<SmfSymbol>();
        if file.seek(SeekFrom::Start(header.symbol_table_offset)).is_err() {
            return Ok(());
        }
        let mut sym_buf = vec![0u8; sym_size * header.symbol_count as usize];
        if file.read_exact(&mut sym_buf).is_err() {
            return Ok(());
        }

        for i in 0..header.symbol_count as usize {
            let sym: SmfSymbol = unsafe { std::ptr::read(sym_buf[i * sym_size..].as_ptr() as *const SmfSymbol) };

            let name = smf_read_string(&string_table, sym.name_offset as usize);
            if name.is_empty() || !self.should_import_symbol(&name, target) {
                continue;
            }

            match sym.sym_type {
                SymbolType::Type | SymbolType::Trait => {
                    if self.module.types.lookup(&name).is_none() {
                        self.module.types.register_named(
                            name.clone(),
                            HirType::Struct {
                                name: name.clone(),
                                fields: vec![],
                                has_snapshot: false,
                                generic_params: vec![],
                                is_generic_template: sym.is_generic_template(),
                                type_bindings: std::collections::HashMap::new(),
                            },
                        );
                    }
                    let type_id = self.module.types.lookup(&name).unwrap_or(TypeId::ANY);
                    self.globals.insert(name, type_id);
                }
                SymbolType::Function => {
                    self.globals.insert(name.clone(), TypeId::ANY);
                    self.imported_function_names.insert(name);
                }
                SymbolType::Constant => {
                    self.globals.insert(name, TypeId::ANY);
                }
                _ => {}
            }
        }

        Ok(())
    }

    /// Check if a symbol should be imported based on the import target.
    #[allow(clippy::only_used_in_recursion)] // reason: parameter threaded for consistency with sibling function signatures
    fn should_import_symbol(&self, name: &str, target: &ImportTarget) -> bool {
        match target {
            ImportTarget::Glob => !name.starts_with('_'),
            ImportTarget::Single(n) => n == name, // Import if matches
            ImportTarget::Group(targets) => {
                // Check if any target in the group matches
                targets.iter().any(|t| self.should_import_symbol(name, t))
            }
            ImportTarget::Aliased { name: n, .. } => n == name, // Import if matches (will be aliased later)
        }
    }
}

fn smf_read_string(table: &[u8], offset: usize) -> String {
    if offset >= table.len() {
        return String::new();
    }
    let end = table[offset..]
        .iter()
        .position(|&b| b == 0)
        .map(|p| offset + p)
        .unwrap_or(table.len());
    String::from_utf8_lossy(&table[offset..end]).into_owned()
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

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
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
    fn aliased_import_call_lowers_to_original_global_symbol() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let owner = src.join("owner");
        fs::create_dir_all(&owner).unwrap();

        fs::write(owner.join("mmio.spl"), "fn mmio_read64(addr: u64) -> u64:\n    addr\n").unwrap();
        let main_path = src.join("main.spl");
        fs::write(
            &main_path,
            r#"use owner.mmio.{mmio_read64 as hardware_mmio_read64}

fn read_hardware(addr: u64) -> u64:
    hardware_mmio_read64(addr)
"#,
        )
        .unwrap();

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
        let mut parser = Parser::new(&source);
        let ast = parser.parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
        let lowered = lowerer.lower_module(&ast).expect("HIR lowering should succeed");
        let func = lowered
            .functions
            .iter()
            .find(|func| func.name == "read_hardware")
            .expect("read_hardware function");
        let body = format!("{:?}", func.body);

        assert!(body.contains("Global(\"mmio_read64\")"), "body: {body}");
        assert!(!body.contains("Global(\"hardware_mmio_read64\")"), "body: {body}");
    }

    #[test]
    fn direct_symbol_import_call_lowers_to_global_symbol() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let owner = src.join("owner");
        fs::create_dir_all(&owner).unwrap();

        fs::write(
            owner.join("pipeline.spl"),
            "fn compile_specialized_template_default() -> i64:\n    73\n",
        )
        .unwrap();
        let main_path = src.join("main.spl");
        fs::write(
            &main_path,
            "use owner.pipeline.compile_specialized_template_default\n\nfn run() -> i64:\n    compile_specialized_template_default()\n",
        )
        .unwrap();

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
        let ast = Parser::new(&source).parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
        let lowered = Lowerer::with_module_resolver(resolver, main_path)
            .lower_module(&ast)
            .expect("direct symbol import should lower");
        let function = lowered
            .functions
            .iter()
            .find(|function| function.name == "run")
            .expect("run function");
        let body = format!("{:?}", function.body);

        assert!(
            body.contains("Global(\"compile_specialized_template_default\")"),
            "body: {body}"
        );
    }

    #[test]
    fn aliased_import_static_method_call_resolves_to_alias_target() {
        // C8-DEEP regression: `use {Real as Alias}` then a static-method /
        // constructor call `Alias.make(...)` must bind the callee to the
        // ALIAS TARGET (`RealWidget.make`), exactly as the type-annotation
        // path (`: Alias`) already resolves it. Before the fix the callee was
        // built from the raw `Alias` token, so `Alias.make` bound to a
        // same-printed-name global type instead of the alias target — which
        // on SimpleOS constructed a real `Fat32Core` where the code expected a
        // `SharedFat32Driver`, yielding a type-confused box and the boot fault
        // storm (see doc/08_tracking/bug/simpleos_native_build_entry_closure_
        // codegen_defects_2026-07-17.md, C8-DEEP).
        let dir = create_test_project();
        let src = dir.path().join("src");
        let owner = src.join("owner");
        fs::create_dir_all(&owner).unwrap();

        fs::write(
            owner.join("widget.spl"),
            "class RealWidget:\n    value: i64\n\nimpl RealWidget:\n    static fn make() -> RealWidget:\n        RealWidget(value: 7)\n",
        )
        .unwrap();
        let main_path = src.join("main.spl");
        fs::write(
            &main_path,
            r#"use owner.widget.{RealWidget as Widget}

fn build() -> Widget:
    Widget.make()
"#,
        )
        .unwrap();

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
        let mut parser = Parser::new(&source);
        let ast = parser.parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
        let lowered = lowerer.lower_module(&ast).expect("HIR lowering should succeed");
        let func = lowered
            .functions
            .iter()
            .find(|func| func.name == "build")
            .expect("build function");
        let body = format!("{:?}", func.body);

        assert!(
            body.contains("Global(\"RealWidget.make\")"),
            "static call should resolve alias to target RealWidget.make; body: {body}"
        );
        assert!(
            !body.contains("Global(\"Widget.make\")"),
            "static call still uses unresolved alias name Widget.make; body: {body}"
        );
    }

    #[test]
    fn imported_trait_optional_struct_return_preserves_field_type() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let input = src.join("input");
        fs::create_dir_all(&input).unwrap();

        fs::write(
            input.join("event.spl"),
            "struct MouseEvent:\n    left_just_pressed: bool\n",
        )
        .unwrap();
        fs::write(
            input.join("backend.spl"),
            r#"use input.event.{MouseEvent}

trait InputBackend:
    me poll_mouse() -> MouseEvent?
"#,
        )
        .unwrap();
        let main_path = src.join("main.spl");
        fs::write(
            &main_path,
            r#"use input.backend.{InputBackend}

fn pressed(backend: InputBackend) -> bool:
    if val event = backend.poll_mouse():
        return event.left_just_pressed
    false
"#,
        )
        .unwrap();

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
        let mut parser = Parser::new(&source);
        let ast = parser.parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src.clone());
        let mut lowerer = Lowerer::with_module_resolver(resolver, main_path);
        let lowered = lowerer
            .lower_module(&ast)
            .expect("HIR lowering should preserve MouseEvent?");
        let pressed = lowered
            .functions
            .iter()
            .find(|func| func.name == "pressed")
            .expect("pressed function");
        let body = format!("{:?}", pressed.body);

        // `HirExprKind::FieldAccess` carries a `field_index`, never the field
        // NAME (contract since cfe0506e336), so grepping the Debug output for
        // "left_just_pressed" could only ever match the FAILURE shape, where
        // the access degraded to a named dynamic call. Assert the shape the
        // test name describes instead: `event.left_just_pressed` lowers to a
        // FieldAccess on MouseEvent's only field, typed bool.
        let returned = pressed
            .body
            .iter()
            .find_map(|stmt| match stmt {
                HirStmt::If { then_block, .. } => then_block.iter().find_map(|inner| match inner {
                    HirStmt::Return(Some(value)) => Some(value),
                    _ => None,
                }),
                _ => None,
            })
            .unwrap_or_else(|| panic!("optional trait result must return a field access: {body}"));
        let HirExprKind::FieldAccess { field_index, .. } = &returned.kind else {
            panic!("optional trait result field must lower as a field access: {body}");
        };
        assert_eq!(*field_index, 0, "MouseEvent.left_just_pressed is field 0: {body}");
        assert_eq!(returned.ty, TypeId::BOOL, "field type must survive the import: {body}");
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

    #[test]
    fn private_glob_import_keeps_public_symbols_only() {
        let dir = create_test_project();
        let src = dir.path().join("src");
        let owner = src.join("owner");
        fs::create_dir_all(&owner).unwrap();
        fs::write(
            owner.join("state.spl"),
            "var _yield_cache: i64 = 0\nval public_value: i64 = 7\nfn public_api() -> i64:\n    public_value\n",
        )
        .unwrap();
        let main_path = src.join("main.spl");
        fs::write(
            &main_path,
            "use owner.state.*\nfn read_public() -> i64:\n    public_api()\n",
        )
        .unwrap();

        let source = crate::read_trace::rts(file!(), line!(), &main_path).unwrap();
        let ast = Parser::new(&source).parse().expect("parse failed");
        let resolver = ModuleResolver::new(dir.path().to_path_buf(), src);
        let lowered = Lowerer::with_module_resolver(resolver, main_path)
            .lower_module(&ast)
            .expect("HIR lowering should succeed");

        assert!(lowered.imported_function_names.contains("public_api"));
        assert!(lowered.globals.iter().any(|(name, _)| name == "public_value"));
        assert!(!lowered.globals.iter().any(|(name, _)| name == "_yield_cache"));
    }

    #[test]
    fn empty_group_or_glob_imports_are_non_addressable_roots() {
        let module_path = ModulePath::new(vec![]);
        let group_target = ImportTarget::Group(vec![ImportTarget::Single("PersistentTrie".to_string())]);

        assert!(Lowerer::is_non_addressable_root_import(&module_path, &group_target));
        assert!(Lowerer::is_non_addressable_root_import(
            &module_path,
            &ImportTarget::Glob
        ));
        assert!(!Lowerer::is_non_addressable_root_import(
            &module_path,
            &ImportTarget::Single("persistent_trie".to_string())
        ));
    }
}

#[cfg(test)]
mod imported_module_ast_memo_tests {
    use super::*;
    use std::sync::atomic::Ordering;

    /// Mechanism pin for the imported-module re-parse.
    ///
    /// Pre-fix, `preregister_imported_type_names` and `load_imported_types` each
    /// did `read_to_string` + a full `Parser::parse` on EVERY `use` naming the
    /// module. A call-site read trace on a lint of a TWO-LINE file counted 2,672
    /// reads at the first site and 611 at the second, out of 3,522 traced reads;
    /// `10.frontend/core/ast.spl` was parsed 749 + 121 times. End to end that was
    /// 3,819 successful `.spl` `openat` over 423 distinct files, which the memo
    /// takes to 676.
    ///
    /// Pinned by COUNT, not wall clock: this box runs at load 40+, where a time
    /// budget is noise. N visits to one path must yield exactly ONE parse.
    #[test]
    fn repeated_import_of_the_same_module_parses_it_exactly_once() {
        crate::perf_counters::set_enabled(true);
        clear_imported_module_ast_cache();
        crate::perf_counters::IMPORT_AST_PARSES.store(0, Ordering::Relaxed);
        crate::perf_counters::IMPORT_AST_HITS.store(0, Ordering::Relaxed);

        let dir = std::env::temp_dir().join(format!("import-ast-memo-{}", std::process::id()));
        std::fs::create_dir_all(&dir).expect("temp dir");
        let m = dir.join("m.spl");
        std::fs::write(&m, "pub struct Widget:\n    id: i64\n").expect("write m");

        for _ in 0..20 {
            let ast = parsed_imported_module(&m).expect("module parses");
            // Memoization must hand back the SAME parsed items, not an empty stub.
            assert!(!ast.items.is_empty(), "memoized AST lost its items");
        }
        assert_eq!(
            crate::perf_counters::IMPORT_AST_PARSES.load(Ordering::Relaxed),
            1,
            "expected exactly one parse per distinct module path"
        );
        assert_eq!(
            crate::perf_counters::IMPORT_AST_HITS.load(Ordering::Relaxed),
            19,
            "expected every repeat import to be a memo hit"
        );

        // An unparseable/unreadable module memoizes its failure too — pre-fix both
        // sites re-read and re-parsed it on every visit.
        let before = crate::perf_counters::IMPORT_AST_PARSES.load(Ordering::Relaxed);
        let missing = dir.join("does_not_exist.spl");
        for _ in 0..10 {
            assert!(parsed_imported_module(&missing).is_none());
        }
        assert_eq!(
            crate::perf_counters::IMPORT_AST_PARSES.load(Ordering::Relaxed) - before,
            1,
            "a failed import must be memoized, not retried per visit"
        );

        let _ = std::fs::remove_dir_all(&dir);
    }
}
