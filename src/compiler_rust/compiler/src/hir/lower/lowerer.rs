use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use simple_parser::{Expr, Pattern, Type};

use super::super::capability::CapabilityEnv;
use super::super::lifetime::LifetimeContext;
use super::super::types::{HirModule, TypeId};
use super::deprecation_warning::DeprecationWarningCollector;
use super::lenient_global_diag::{LenientGlobal, LenientGlobalCollector, LenientGlobalKind};
use super::memory_warning::MemoryWarningCollector;
use crate::module_resolver::ModuleResolver;
use crate::type_inference_config::TypeInferenceConfig;

type GlobalStructDefs = std::sync::Arc<HashMap<String, Vec<(String, Type)>>>;
type UniqueStructOwners = std::sync::Arc<HashMap<String, String>>;
type StructModuleOwners = std::sync::Arc<HashMap<PathBuf, String>>;
type DuplicateGlobalStructDefs = std::sync::Arc<HashMap<String, Vec<Vec<(String, Type)>>>>;
type AmbiguousFieldNames = std::sync::Arc<HashSet<String>>;
type GlobalEnumDefs = std::sync::Arc<HashMap<String, Vec<(String, Option<Vec<Type>>)>>>;
pub(crate) type QualifiedImportFunctions = std::sync::Arc<HashMap<String, String>>;

pub struct Lowerer {
    pub(super) module: HirModule,
    pub(super) globals: HashMap<String, TypeId>,
    /// Compile-time constant initial values for module-level `val` declarations.
    pub(super) global_init_values: HashMap<String, i64>,
    /// String constant initial values for module-level `val`/`var` declarations.
    pub(super) global_init_strings: HashMap<String, String>,
    /// Integer array literal initial values for module-level `val`/`var`.
    pub(super) global_init_arrays: HashMap<String, super::super::types::HirGlobalArrayInit>,
    pub(super) global_init_structs: HashMap<String, super::super::types::HirGlobalStructInit>,
    /// Function-valued global initializers for module-level `val`/`var`.
    pub(super) global_init_functions: HashMap<String, String>,
    /// Set of globals that are defined locally in this module (not imported).
    pub(super) local_globals: HashSet<String>,
    /// Set of globals that are immutable (val/const, not var).
    pub(super) immutable_globals: HashSet<String>,
    /// Set of function names that are marked with #[pure] (CTR-031)
    /// These functions can be called from contract expressions
    pub(super) pure_functions: HashSet<String>,
    /// Current class/struct type being lowered (for Self resolution)
    pub(super) current_class_type: Option<TypeId>,
    /// Current function/method name being lowered, used to enrich lowering diagnostics.
    pub(super) current_function_name: Option<String>,
    /// Declaration line of the function currently being lowered. Recorded so the
    /// `lenient_types` unresolved-name fallback can attribute the global it
    /// emits to a source location; `Expr::Identifier` carries no span of its own.
    pub(super) current_function_line: Option<usize>,
    /// `(line, column)` of the pattern currently being lowered into a
    /// pattern-condition test. Set by every entry point that owns a spanned
    /// pattern (match arm, `if val`, `elif val`, `while val`) so
    /// `option_pattern_shape_diag` can name a source location instead of only
    /// the run. `Pattern` itself carries no span; `MatchArm` and `IfStmt` do.
    pub(super) current_pattern_span: Option<(usize, usize)>,
    /// Module resolver for loading types from imports (optional for backward compatibility)
    pub(super) module_resolver: Option<ModuleResolver>,
    /// Current file being compiled (for resolving relative imports)
    pub(super) current_file: Option<PathBuf>,
    /// Track loaded modules to prevent circular dependencies.
    ///
    /// This is the ACTIVE import path, not a visited set: a module is inserted
    /// before its imports are followed and removed afterwards.
    pub(super) loaded_modules: HashSet<PathBuf>,
    /// The same active import path in visit order, so a detected cycle can be
    /// named (`a -> b -> c -> a`) rather than merely suppressed.
    pub(super) import_stack: Vec<PathBuf>,
    /// Import cycles observed while loading this module's imports.
    ///
    /// Cycles are tolerated, not rejected -- the loader has always absorbed
    /// them and returning an error here would break every existing build that
    /// contains one. They are recorded so they can be reported.
    pub(super) import_cycles: Vec<Vec<PathBuf>>,
    /// Track materialized import targets per module path. A module can be
    /// imported multiple times with different grouped symbols; path-only
    /// de-duplication skips later function imports.
    pub(super) loaded_import_targets: HashSet<(PathBuf, String)>,
    /// Memory safety warning collector
    pub(super) memory_warnings: MemoryWarningCollector,
    /// Lifetime inference context for tracking reference lifetimes
    pub(super) lifetime_context: LifetimeContext,
    /// Capability environment for tracking active reference capabilities
    pub(super) capability_env: CapabilityEnv,
    /// Type aliases: alias_name -> original_name
    pub(super) type_aliases: HashMap<String, String>,
    /// Function aliases: alias_name -> original_name
    pub(super) function_aliases: HashMap<String, String>,
    /// Reverse lookup for suggestions: original -> Vec<aliases>
    pub(super) type_aliases_reverse: HashMap<String, Vec<String>>,
    /// Reverse lookup for function suggestions: original -> Vec<aliases>
    pub(super) function_aliases_reverse: HashMap<String, Vec<String>>,
    /// Deprecated items: name -> deprecation_message (None if no message)
    pub(super) deprecated_items: HashMap<String, Option<String>>,
    /// Deprecation warning collector
    pub(super) deprecation_warnings: DeprecationWarningCollector,
    /// Type inference configuration for empty collections
    pub(super) type_inference_config: TypeInferenceConfig,
    /// Pre-registered method return types: "ClassName.method" -> return TypeId
    pub(super) method_return_types: HashMap<String, TypeId>,
    /// M12 3b: free-function parameter default-value expressions, keyed by
    /// function name (one Option per declared parameter; None = no default).
    /// Captured from the AST during module lowering so omitted trailing
    /// arguments can be filled at call sites (`lower_call`).
    pub(super) fn_param_defaults: HashMap<String, Vec<Option<Expr>>>,
    /// Whole-program map of free-function name -> declared return type,
    /// built by `build_import_map`. Functions reached via the global import map
    /// (called without a `use` import) otherwise have no return-type info, so
    /// their call results become ANY and field access on them fails. Resolved
    /// into `method_return_types` in Pass 0.5c (additive: upgrade-only).
    pub(super) global_fn_return_types: Option<std::sync::Arc<HashMap<String, Type>>>,
    /// Module-qualified source call (`variables.env_get`) to its exact native
    /// owner. Native-project builds populate this before expression lowering
    /// so duplicate bare functions do not turn the namespace into a global.
    pub(super) qualified_import_functions: Option<QualifiedImportFunctions>,
    /// Local alias -> original symbol name, for selective imports written
    /// `use m.{f as g}`.
    ///
    /// Module flattening merges `f` into the unit under its ORIGINAL name while
    /// call sites still say `g`, and records the mapping as
    /// `__simple_flatten_import_binding__=` marker consts. Every consumer of
    /// those markers used to live in the interpreter, so the codegen lane
    /// emitted `g` as an unresolved external symbol -- a silent whole-module
    /// JIT fallback (100-1000x) or a hard E1002 under AOT, where baremetal
    /// units have no interpreter to fall back to. Populated by
    /// `collect_flattened_import_aliases`, consumed by `lower_identifier`. See
    /// `doc/08_tracking/bug/aliased_use_import_does_not_bind_in_transitive_module_2026-08-10.md`.
    pub(super) import_alias_bindings: HashMap<String, String>,
    /// When true, unknown types resolve to ANY instead of erroring.
    /// This allows compilation to proceed even when imports can't be fully resolved.
    pub(super) lenient_types: bool,
    /// Names that `lenient_types` lowered to `HirExprKind::Global` because they
    /// resolved to nothing. Each becomes a `GlobalLoad` and, if no other module
    /// defines it, an undeclared symbol that only fails at LINK time with no
    /// source location. Collected so such a failure is attributable; see
    /// `lenient_global_diag`.
    pub(super) lenient_globals: LenientGlobalCollector,
    /// Names of extern function declarations for codegen
    pub(super) extern_fn_names: HashSet<String>,
    /// Function names imported via `use` statements (should not become globals in MIR)
    pub(super) imported_function_names: HashSet<String>,
    /// Canonical `module_prefix__Type` layouts from all compilation units.
    pub(super) global_struct_defs: Option<GlobalStructDefs>,
    /// Bare names that have exactly one canonical nominal owner.  This is a
    /// compatibility index, never an identity source for colliding types.
    pub(super) unique_global_struct_owners: Option<UniqueStructOwners>,
    /// Resolver declaration path -> canonical module owner metadata.
    pub(super) struct_module_owners: Option<StructModuleOwners>,
    /// Duplicate struct/class definitions keyed by bare type name. Each value
    /// preserves all colliding layouts so field fallback can pick a unique
    /// variant by field name without merging incompatible offsets.
    pub(super) duplicate_global_struct_defs: Option<DuplicateGlobalStructDefs>,
    /// Field names that appear in more than one globally-known struct.
    /// Cross-module lookups skip these to avoid picking the wrong struct's
    /// byte offset (see the BeDomNode/BeLayoutBox `children` collision that
    /// originally motivated the old "single-field structs only" filter).
    pub(super) ambiguous_field_names: Option<AmbiguousFieldNames>,
    /// Global enum definitions from all compilation units, keyed by enum
    /// name with payload field types per variant. Set by the native_project
    /// compiler driver before `lower_module` runs and consumed by
    /// `register_global_enums()` to eagerly seed `module.types.name_to_id`
    /// and `globals` with real enum TypeIds. Without this, cross-module
    /// enum receivers reached via re-export (and not via a direct `use`
    /// chain) leave `lookup(EnumName)` returning None and the enum-variant
    /// early-return in `expr/access.rs::lower_field_access` falls through
    /// to the field-access fallback (W13-F class 1, fixed in W15-H).
    pub(super) global_enum_defs: Option<GlobalEnumDefs>,
    /// Source file each struct/class bare name was DECLARED in, recorded by
    /// `register_struct`. A name that collides across modules maps to the file
    /// of whichever declaration registered last -- which is exactly the signal
    /// needed: `lower_struct_init_fields` only hard-rejects an unknown named
    /// argument when the construction site sits in that same file, so the
    /// registry entry it validates against is provably the local declaration
    /// and not a same-bare-name struct from another module. See the SOUNDNESS
    /// GATE comment in hir/lower/expr/collections.rs.
    pub(super) struct_decl_files: HashMap<String, Option<PathBuf>>,
    /// Declared field DEFAULT expressions, keyed by struct/class bare name then
    /// field name (`class D: var m: i64 = 7` -> `{"D": {"m": <7>}}`).
    ///
    /// ROOT FIX (JIT omitted-field-default bug, 2026-08-17):
    /// `lower_struct_init_fields` filled every declared slot nothing wrote with
    /// a `HirExprKind::Nil` placeholder, which MIR lowers to the raw nil tag
    /// `3`. Read back through an `i64`-typed field that surfaces as the literal
    /// integer `3`, so `class D: var n: i64 = 0; var m: i64 = 7` constructed as
    /// `D()` printed `n=3 m=3` under the JIT while the interpreter (which
    /// evaluates declared defaults directly) printed `n=0 m=7`. Recording the
    /// default expressions at registration time lets that loop lower the real
    /// default instead. Only bare names with a recorded default are affected;
    /// a field with NO declared default keeps the `Nil` placeholder exactly as
    /// before.
    pub(super) struct_field_defaults: HashMap<String, HashMap<String, Expr>>,
    /// Local bindings authored as untyped empty array literals (`var xs = []`).
    ///
    /// These start as `[Any]` placeholders in HIR so later builtin `append`
    /// calls can specialize the local to the appended element type instead of
    /// freezing the seed to the configured scalar default element type.
    pub(super) untyped_empty_array_locals: HashSet<usize>,
}

impl Lowerer {
    /// Create a new lowerer with STRICT memory mode (Rust-level safety)
    /// Memory safety violations are compile-time ERRORS by default.
    /// Use `with_lenient_mode()` for backwards compatibility during migration.
    pub fn new() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            global_init_values: HashMap::new(),
            global_init_strings: HashMap::new(),
            global_init_arrays: HashMap::new(),
            global_init_structs: HashMap::new(),
            global_init_functions: HashMap::new(),
            local_globals: HashSet::new(),
            immutable_globals: HashSet::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            current_function_name: None,
            current_function_line: None,
            current_pattern_span: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            import_stack: Vec::new(),
            import_cycles: Vec::new(),
            loaded_import_targets: HashSet::new(),
            memory_warnings: MemoryWarningCollector::strict(), // STRICT mode for Rust-level safety
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            import_alias_bindings: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            fn_param_defaults: HashMap::new(),
            global_fn_return_types: None,
            qualified_import_functions: None,
            lenient_types: false,
            lenient_globals: LenientGlobalCollector::new(),
            extern_fn_names: HashSet::new(),
            imported_function_names: HashSet::new(),
            global_struct_defs: None,
            unique_global_struct_owners: None,
            struct_module_owners: None,
            duplicate_global_struct_defs: None,
            struct_decl_files: HashMap::new(),
            struct_field_defaults: HashMap::new(),
            ambiguous_field_names: None,
            global_enum_defs: None,
            untyped_empty_array_locals: HashSet::new(),
        }
    }

    /// Create a new lowerer with module resolution support for loading imported types
    /// Uses strict memory mode by default.
    pub fn with_module_resolver(module_resolver: ModuleResolver, current_file: PathBuf) -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            global_init_values: HashMap::new(),
            global_init_strings: HashMap::new(),
            global_init_arrays: HashMap::new(),
            global_init_structs: HashMap::new(),
            global_init_functions: HashMap::new(),
            local_globals: HashSet::new(),
            immutable_globals: HashSet::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            current_function_name: None,
            current_function_line: None,
            current_pattern_span: None,
            module_resolver: Some(module_resolver),
            current_file: Some(current_file),
            loaded_modules: HashSet::new(),
            import_stack: Vec::new(),
            import_cycles: Vec::new(),
            loaded_import_targets: HashSet::new(),
            memory_warnings: MemoryWarningCollector::strict(), // STRICT by default
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            import_alias_bindings: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            fn_param_defaults: HashMap::new(),
            global_fn_return_types: None,
            qualified_import_functions: None,
            lenient_types: false,
            lenient_globals: LenientGlobalCollector::new(),
            extern_fn_names: HashSet::new(),
            imported_function_names: HashSet::new(),
            global_struct_defs: None,
            unique_global_struct_owners: None,
            struct_module_owners: None,
            duplicate_global_struct_defs: None,
            struct_decl_files: HashMap::new(),
            struct_field_defaults: HashMap::new(),
            ambiguous_field_names: None,
            global_enum_defs: None,
            untyped_empty_array_locals: HashSet::new(),
        }
    }

    /// Create a lowerer with custom type inference configuration
    pub fn with_type_inference_config(mut self, config: TypeInferenceConfig) -> Self {
        self.type_inference_config = config;
        self
    }

    /// Set type inference configuration
    pub fn set_type_inference_config(&mut self, config: TypeInferenceConfig) {
        self.type_inference_config = config;
    }

    /// Get the current type inference configuration
    pub fn type_inference_config(&self) -> &TypeInferenceConfig {
        &self.type_inference_config
    }

    /// Alias for `new()` - strict mode is now the default
    #[deprecated(since = "1.0.0", note = "strict mode is now the default; use `new()` instead")]
    pub fn with_strict_memory_mode() -> Self {
        Self::new()
    }

    /// Create a new lowerer with LENIENT memory mode (for backwards compatibility)
    /// In lenient mode, capability violations produce WARNINGS instead of errors.
    /// Use this during migration to strict mode.
    pub fn with_lenient_mode() -> Self {
        Self {
            module: HirModule::new(),
            globals: HashMap::new(),
            global_init_values: HashMap::new(),
            global_init_strings: HashMap::new(),
            global_init_arrays: HashMap::new(),
            global_init_structs: HashMap::new(),
            global_init_functions: HashMap::new(),
            local_globals: HashSet::new(),
            immutable_globals: HashSet::new(),
            pure_functions: HashSet::new(),
            current_class_type: None,
            current_function_name: None,
            current_function_line: None,
            current_pattern_span: None,
            module_resolver: None,
            current_file: None,
            loaded_modules: HashSet::new(),
            import_stack: Vec::new(),
            import_cycles: Vec::new(),
            loaded_import_targets: HashSet::new(),
            memory_warnings: MemoryWarningCollector::new(), // Lenient mode (warnings only)
            lifetime_context: LifetimeContext::new(),
            capability_env: CapabilityEnv::new(),
            type_aliases: HashMap::new(),
            function_aliases: HashMap::new(),
            import_alias_bindings: HashMap::new(),
            type_aliases_reverse: HashMap::new(),
            function_aliases_reverse: HashMap::new(),
            deprecated_items: HashMap::new(),
            deprecation_warnings: DeprecationWarningCollector::new(),
            type_inference_config: TypeInferenceConfig::default(),
            method_return_types: HashMap::new(),
            fn_param_defaults: HashMap::new(),
            global_fn_return_types: None,
            qualified_import_functions: None,
            lenient_types: false,
            lenient_globals: LenientGlobalCollector::new(),
            extern_fn_names: HashSet::new(),
            imported_function_names: HashSet::new(),
            global_struct_defs: None,
            unique_global_struct_owners: None,
            struct_module_owners: None,
            duplicate_global_struct_defs: None,
            struct_decl_files: HashMap::new(),
            struct_field_defaults: HashMap::new(),
            ambiguous_field_names: None,
            global_enum_defs: None,
            untyped_empty_array_locals: HashSet::new(),
        }
    }

    /// Get the collected memory warnings
    pub fn memory_warnings(&self) -> &MemoryWarningCollector {
        &self.memory_warnings
    }

    /// Get mutable access to the memory warnings collector
    pub fn memory_warnings_mut(&mut self) -> &mut MemoryWarningCollector {
        &mut self.memory_warnings
    }

    /// Set whether to use strict mode for memory safety checks
    pub fn set_strict_mode(&mut self, strict: bool) {
        self.memory_warnings.set_strict(strict);
    }

    /// Set whether to use lenient type resolution.
    /// When enabled, unknown types resolve to ANY instead of producing errors.
    /// This allows compilation to proceed even when imports can't be fully resolved.
    pub fn set_lenient_types(&mut self, lenient: bool) {
        self.lenient_types = lenient;
    }

    /// Attribute a name that the `lenient_types` fallback is about to lower to
    /// `HirExprKind::Global`.
    ///
    /// This does not change what is compiled -- the fallback is load-bearing for
    /// cross-module references, which are genuinely unresolvable while lowering
    /// one file at a time. It records *where the name came from* so that a
    /// link-time "undefined symbol" can be traced back to a file and function
    /// instead of appearing with no source location at all.
    pub(super) fn record_lenient_global(&mut self, name: &str, kind: LenientGlobalKind) {
        let entry = LenientGlobal {
            file: self.current_file.as_ref().map(|path| path.display().to_string()),
            function: self.current_function_name.clone(),
            function_line: self.current_function_line,
            name: name.to_string(),
            kind,
        };
        // Mirror into the process-global registry so the native link path can
        // resolve an "undefined symbol" back to this location. The production
        // path (`native_project::compile_file_to_object`) calls
        // `lower_module`, which consumes the lowerer and returns only a
        // `HirModule`, so this per-instance collector never reaches the linker.
        super::lenient_global_diag::record_for_link_diagnostics(&entry);
        self.lenient_globals.record(entry);
    }

    /// Names lowered as globals by the `lenient_types` fallback, dedup'd.
    ///
    /// The count is the population of symbols that can only fail at link time;
    /// `attributions_for` maps a linker-reported symbol back to its source.
    pub fn lenient_globals(&self) -> &LenientGlobalCollector {
        &self.lenient_globals
    }

    /// Pre-register global struct definitions from all compilation units.
    /// This ensures consistent field offsets across all modules by making
    /// every file's type registry aware of all struct layouts in the project.
    /// Set global struct definitions for cross-module field resolution.
    /// The type resolver uses these to look up field indices when the struct type
    /// isn't in the per-file registry.
    pub fn set_global_struct_defs(&mut self, defs: GlobalStructDefs) {
        self.global_struct_defs = Some(defs);
    }

    pub fn set_unique_global_struct_owners(&mut self, owners: UniqueStructOwners) {
        self.unique_global_struct_owners = Some(owners);
    }

    pub fn set_struct_module_owners(&mut self, owners: StructModuleOwners) {
        self.struct_module_owners = Some(owners);
    }

    /// Set the whole-program free-function return-type map (see field doc).
    pub fn set_global_fn_return_types(&mut self, defs: std::sync::Arc<HashMap<String, Type>>) {
        self.global_fn_return_types = Some(defs);
    }

    pub(crate) fn set_qualified_import_functions(&mut self, functions: QualifiedImportFunctions) {
        self.qualified_import_functions = Some(functions);
    }

    pub fn set_duplicate_global_struct_defs(&mut self, defs: DuplicateGlobalStructDefs) {
        self.duplicate_global_struct_defs = Some(defs);
    }

    /// Get global struct definitions (if set).
    pub fn global_struct_defs(&self) -> Option<&HashMap<String, Vec<(String, Type)>>> {
        self.global_struct_defs.as_deref()
    }

    /// Set the blacklist of ambiguous field names. Any field name on this
    /// list is skipped by the cross-module field lookup fallback in
    /// `get_field_info`, which falls back to a method call instead. See the
    /// comment on `global_struct_defs` and the `native_project/compiler.rs`
    /// setup site for background.
    pub fn set_ambiguous_field_names(&mut self, names: AmbiguousFieldNames) {
        self.ambiguous_field_names = Some(names);
    }

    /// Check whether a field name is globally ambiguous (defined in more
    /// than one known struct).
    pub(super) fn is_ambiguous_global_field(&self, name: &str) -> bool {
        self.ambiguous_field_names.as_ref().is_some_and(|s| s.contains(name))
    }

    /// Set global enum definitions for cross-module enum receiver resolution.
    /// W15-H: paired with `register_global_enums()`, which the
    /// `native_project` compiler driver calls before `lower_module(&ast)`.
    /// See the doc comment on `global_enum_defs` for the why.
    pub fn set_global_enum_defs(&mut self, defs: GlobalEnumDefs) {
        self.global_enum_defs = Some(defs);
    }

    /// Eagerly register every enum from `global_enum_defs` into the local
    /// type registry as a real `HirType::Enum` and bind its name in
    /// `self.globals` to the freshly-allocated TypeId.
    ///
    /// MUST be called by the compiler driver after `set_global_enum_defs`
    /// and BEFORE `lower_module(&ast)`. The lowerer's Pass 0 placeholder
    /// registration in `module_pass.rs::lower_module` then takes precedence
    /// for any enum that is also locally defined in this compilation unit
    /// (we lookup-guard with `is_none()`), so this only fills in the
    /// cross-module gap that the per-`use_stmt` import-loader pass misses
    /// when an enum reaches the file via re-export rather than a direct
    /// `use` chain (W13-F class 1).
    ///
    /// All names are registered before payloads are resolved so references to
    /// another project enum do not depend on hash-map iteration order.
    pub fn register_global_enums(&mut self) {
        let defs = match self.global_enum_defs.clone() {
            Some(d) => d,
            None => return,
        };
        let mut seeded = Vec::new();
        for enum_name in defs.keys() {
            // Skip enums that already have a real registration (locally
            // defined in this compilation unit, or pre-registered by
            // `preregister_imported_type_names` for a directly-imported
            // enum). `register_named` would otherwise allocate a fresh
            // TypeId and orphan the original.
            if self.module.types.lookup(enum_name).is_some() {
                continue;
            }
            let type_id = self.module.types.register_named(
                enum_name.clone(),
                super::super::types::HirType::Enum {
                    name: enum_name.clone(),
                    variants: vec![],
                    generic_params: vec![],
                    is_generic_template: false,
                    type_bindings: std::collections::HashMap::new(),
                },
            );
            // Bind the enum name in `self.globals` to the real TypeId.
            // HashMap::insert overwrites — this displaces any prior binding
            // (notably `TypeId::ANY` set by the declare_globals pass for
            // imported enum names that lacked a registered TypeId), which
            // is the W13-F class 1 root cause.
            self.globals.insert(enum_name.clone(), type_id);
            seeded.push(enum_name.clone());
        }

        for enum_name in seeded {
            let Some(variant_summary) = defs.get(&enum_name) else {
                continue;
            };
            let variants = self.resolve_global_enum_variants(variant_summary);
            let type_id = self.module.types.update_named(
                enum_name.clone(),
                super::super::types::HirType::Enum {
                    name: enum_name.clone(),
                    variants,
                    generic_params: vec![],
                    is_generic_template: false,
                    type_bindings: std::collections::HashMap::new(),
                },
            );
            self.globals.insert(enum_name, type_id);
        }
    }

    pub(super) fn resolve_global_enum_variants(
        &mut self,
        summary: &[(String, Option<Vec<Type>>)],
    ) -> Vec<(String, Option<Vec<TypeId>>)> {
        summary
            .iter()
            .map(|(variant_name, payload)| {
                let payload = payload.as_ref().map(|fields| {
                    fields
                        .iter()
                        .map(|field| match field {
                            Type::Simple(name) if name == "Any" => TypeId::ANY,
                            _ => self.resolve_type(field).unwrap_or(TypeId::ANY),
                        })
                        .collect()
                });
                (variant_name.clone(), payload)
            })
            .collect()
    }

    /// Take ownership of the memory warnings
    pub fn take_memory_warnings(&mut self) -> MemoryWarningCollector {
        std::mem::take(&mut self.memory_warnings)
    }

    /// Get the collected deprecation warnings
    pub fn deprecation_warnings(&self) -> &DeprecationWarningCollector {
        &self.deprecation_warnings
    }

    /// Take ownership of the deprecation warnings
    pub fn take_deprecation_warnings(&mut self) -> DeprecationWarningCollector {
        std::mem::take(&mut self.deprecation_warnings)
    }

    /// Check if a function is marked as pure
    pub fn is_pure_function(&self, name: &str) -> bool {
        self.pure_functions.contains(name)
    }

    pub(super) fn extract_pattern_name(pattern: &Pattern) -> Option<String> {
        match pattern {
            Pattern::Identifier(n) => Some(n.clone()),
            Pattern::MutIdentifier(n) => Some(n.clone()),
            Pattern::MoveIdentifier(n) => Some(n.clone()),
            Pattern::Typed { pattern: inner, .. } => Self::extract_pattern_name(inner),
            _ => None,
        }
    }

    /// Extract type annotation from a Pattern::Typed wrapper.
    /// Returns None if the pattern doesn't have a type annotation.
    pub(super) fn extract_pattern_type(pattern: &Pattern) -> Option<&simple_parser::Type> {
        match pattern {
            Pattern::Typed { ty, .. } => Some(ty),
            _ => None,
        }
    }

    /// Get the lifetime context
    pub fn lifetime_context(&self) -> &LifetimeContext {
        &self.lifetime_context
    }

    /// Get mutable access to the lifetime context
    pub fn lifetime_context_mut(&mut self) -> &mut LifetimeContext {
        &mut self.lifetime_context
    }

    /// Check if there are any lifetime violations
    pub fn has_lifetime_violations(&self) -> bool {
        self.lifetime_context.has_violations()
    }

    /// Get all lifetime violations
    pub fn lifetime_violations(&self) -> &[super::super::lifetime::LifetimeViolation] {
        self.lifetime_context.violations()
    }

    /// Generate Lean 4 verification code for lifetime constraints
    pub fn generate_lean4_lifetime_verification(&self) -> String {
        self.lifetime_context.generate_lean4()
    }

    /// Get the capability environment
    pub fn capability_env(&self) -> &CapabilityEnv {
        &self.capability_env
    }

    /// Get mutable access to the capability environment
    pub fn capability_env_mut(&mut self) -> &mut CapabilityEnv {
        &mut self.capability_env
    }

    // === Alias and Deprecation Tracking ===

    /// Register a type alias name mapping: alias NewName = OldName
    pub(super) fn register_type_alias_mapping(&mut self, alias_name: String, target_name: String) {
        // Add forward mapping
        self.type_aliases.insert(alias_name.clone(), target_name.clone());

        // Add reverse mapping for suggestion lookup
        self.type_aliases_reverse
            .entry(target_name)
            .or_default()
            .push(alias_name);
    }

    /// Register a function alias: fn new_name = old_name
    pub(super) fn register_function_alias(&mut self, alias_name: String, target_name: String) {
        // Add forward mapping
        self.function_aliases.insert(alias_name.clone(), target_name.clone());

        // Add reverse mapping for suggestion lookup
        self.function_aliases_reverse
            .entry(target_name)
            .or_default()
            .push(alias_name);
    }

    /// Mark an item as deprecated with an optional message
    pub(super) fn mark_deprecated(&mut self, name: String, message: Option<String>) {
        self.deprecated_items.insert(name, message);
    }

    /// Check if an item is deprecated
    pub fn is_deprecated(&self, name: &str) -> bool {
        self.deprecated_items.contains_key(name)
    }

    /// Get the deprecation message for an item
    pub fn deprecation_message(&self, name: &str) -> Option<&str> {
        self.deprecated_items.get(name).and_then(|opt| opt.as_deref())
    }

    /// Resolve a type alias to its original type name
    pub fn resolve_type_alias(&self, name: &str) -> Option<&str> {
        self.type_aliases.get(name).map(|s| s.as_str())
    }

    /// Build the flattened-import alias map (local alias -> original symbol).
    ///
    /// Scans the flattened module for `__simple_flatten_import_binding__=`
    /// marker consts, the same records the interpreter consumes, and keeps only
    /// the entries where the local binding differs from the source symbol --
    /// i.e. genuine `use m.{f as g}` aliases. Plain selective imports and the
    /// `*` glob marker need no rewrite because local name == original name, and
    /// recording them would be a no-op mapping that could mask a real symbol.
    ///
    /// This is the codegen-side consumer whose absence made aliased imports
    /// lower to unresolved external symbols.
    pub(super) fn collect_flattened_import_aliases(&mut self, ast_module: &simple_parser::Module) {
        use crate::interpreter::{
            decode_import_binding_marker, flatten_owner_mangled_name, FLATTEN_MODULE_OWNER_ATTR_PREFIX,
        };

        // Flattening merges every imported module's items into one namespace. An
        // imported free function whose bare name cannot survive that merge is
        // given an owner-unique symbol by
        // `pipeline::module_loader::strip_flattened_import_nodes` (which is what
        // the native-project lane has always done via its `raw_to_mangled`
        // module-prefix scheme). `main` is the case that matters: it used to be
        // DROPPED at flatten time, so an alias to it bound the ENTRY module's
        // `main` and recursed forever.
        //
        // The marker records `source_owner` as the same `normalize_path_key`
        // string the flattener mangles with, so recomputing the mangled symbol
        // here resolves the alias to the exact function the `use` names -- no
        // side table, and no reliance on the bare name being unique.
        //
        // A source name that is still ambiguous after that is left UNRESOLVED on
        // purpose: the resulting unresolved-symbol error is correct behaviour
        // compared to silently binding the wrong function. See
        // `doc/08_tracking/bug/flattened_lane_does_not_mangle_duplicate_function_names_2026-08-10.md`.
        let mut definition_counts: HashMap<&str, usize> = HashMap::new();
        // (module owner, bare name) -> definition count. See the Function arm below.
        let mut owner_definition_counts: HashMap<(&str, &str), usize> = HashMap::new();
        // Every name the flattened unit really DECLARES, function or value. The
        // alias branch in `lower_identifier` now runs ahead of the
        // callable/global lookups (see there for why), so an entry recorded here
        // must be provably free of any real declaration of the alias name --
        // otherwise the alias could shadow a genuine value, not just a phantom
        // `use` registration.
        let mut declared_names: std::collections::HashSet<&str> = std::collections::HashSet::new();
        for item in &ast_module.items {
            match item {
                simple_parser::Node::Function(f) => {
                    *definition_counts.entry(f.name.as_str()).or_insert(0) += 1;
                    declared_names.insert(f.name.as_str());
                    // `strip_flattened_import_nodes` tags every flattened
                    // function with the module that declared it. Counting by
                    // (owner, name) lets an alias be disambiguated by the module
                    // the `use` actually names, even though only `main` is
                    // owner-MANGLED and every other name stays bare.
                    if let Some(owner) = f
                        .attributes
                        .iter()
                        .find_map(|a| a.name.strip_prefix(FLATTEN_MODULE_OWNER_ATTR_PREFIX))
                    {
                        *owner_definition_counts.entry((owner, f.name.as_str())).or_insert(0) += 1;
                    }
                }
                simple_parser::Node::Const(c) => {
                    declared_names.insert(c.name.as_str());
                }
                simple_parser::Node::Static(st) => {
                    declared_names.insert(st.name.as_str());
                }
                simple_parser::Node::Let(l) => {
                    if let simple_parser::ast::Pattern::Identifier(name)
                    | simple_parser::ast::Pattern::MutIdentifier(name)
                    | simple_parser::ast::Pattern::MoveIdentifier(name) = &l.pattern
                    {
                        declared_names.insert(name.as_str());
                    }
                }
                _ => {}
            }
        }

        // Every import/re-export edge in the flattened unit, keyed by the module
        // that WROTE it. `std.io_runtime` is a facade
        // (`src/lib/io_runtime.spl`) that re-exports the real
        // `src/lib/nogc_sync_mut/io_runtime.spl`, so a marker's `source_owner`
        // frequently names the facade, not the module that actually declares the
        // function. Following these edges is what turns the facade into the
        // declaring module.
        let mut reexport_edges: HashMap<(&str, &str), (&str, &str)> = HashMap::new();
        for item in &ast_module.items {
            if let simple_parser::Node::Const(marker) = item {
                if let Some((importer, local_name, source_owner, source_name)) =
                    decode_import_binding_marker(&marker.name)
                {
                    if local_name != "*" && source_name != "*" {
                        reexport_edges
                            .entry((importer, local_name))
                            .or_insert((source_owner, source_name));
                    }
                }
            }
        }

        for item in &ast_module.items {
            let simple_parser::Node::Const(marker) = item else {
                continue;
            };
            let Some((_importer, local_name, source_owner, source_name)) = decode_import_binding_marker(&marker.name)
            else {
                continue;
            };
            if local_name == "*" || source_name == "*" || local_name == source_name {
                continue;
            }
            // A real declaration of the alias name -- function or value -- wins
            // over the import. Recording a mapping at all would be misleading,
            // and since the alias branch now outranks the callable/global
            // lookups it would actively shadow the real declaration.
            if declared_names.contains(local_name) {
                continue;
            }
            // Prefer the owner-mangled symbol. It names exactly the function in
            // the module the `use` names, so it is unambiguous by construction
            // and is checked for existence before it is trusted.
            let owner_mangled = flatten_owner_mangled_name(source_owner, source_name);
            let resolved = if definition_counts.get(owner_mangled.as_str()).copied() == Some(1) {
                owner_mangled
            } else if definition_counts.get(source_name).copied() == Some(1) {
                // Unmangled and unique in the flattened unit: the bare name is
                // the only candidate, so binding it is safe.
                source_name.to_string()
            } else if {
                // Walk the re-export chain from the module the `use` names to
                // the module that actually DECLARES the function, then check
                // that the declaration is unique there. Bounded so a cyclic
                // facade graph cannot hang lowering.
                let mut owner = source_owner;
                let mut sym = source_name;
                let mut found = false;
                for _ in 0..16 {
                    if owner_definition_counts.get(&(owner, sym)).copied() == Some(1) {
                        found = true;
                        break;
                    }
                    match reexport_edges.get(&(owner, sym)) {
                        Some(&(next_owner, next_sym)) => {
                            owner = next_owner;
                            sym = next_sym;
                        }
                        None => break,
                    }
                }
                found
            } {
                // The bare name is ambiguous across the flattened unit (e.g.
                // FOUR modules define `file_rename`), but exactly one of them is
                // the module this `use` names, identified by the flattener's own
                // module-owner tag. Bind the bare name.
                //
                // This is not a guess and it cannot bind "the wrong function"
                // any more than the non-aliased form already does: a plain
                // `use std.io_runtime.{file_rename}` -- which the tree already
                // relies on (`src/lib/nogc_sync_mut/shell/file.spl:22`) --
                // lowers to exactly this bare name today. Refusing only the
                // ALIASED spelling made the two forms disagree and produced an
                // unresolvable `Linkage::Import` (`runtime_file_rename`) that
                // de-JITted the whole stage1 module. See
                // `doc/08_tracking/bug/jit_unresolved_rt_native_build_and_runtime_file_rename_2026-08-22.md`.
                source_name.to_string()
            } else {
                // Absent or ambiguous. Do NOT guess -- leave the alias
                // unresolved so the lane reports an unresolved symbol instead of
                // calling the wrong function.
                continue;
            };
            self.import_alias_bindings.insert(local_name.to_string(), resolved);
        }
    }

    /// Resolve a selective-import alias (`use m.{f as g}`) to its original symbol.
    pub(super) fn resolve_import_alias(&self, name: &str) -> Option<&str> {
        self.import_alias_bindings.get(name).map(|s| s.as_str())
    }

    /// Resolve a function alias to its original function name
    pub fn resolve_function_alias(&self, name: &str) -> Option<&str> {
        self.function_aliases.get(name).map(|s| s.as_str())
    }

    /// Find non-deprecated alternatives for a deprecated type
    pub fn find_non_deprecated_type_alternative(&self, name: &str) -> Option<String> {
        // Get the original type (if this is an alias)
        let original = self.type_aliases.get(name).map(|s| s.as_str()).unwrap_or(name);

        // Find all aliases of the original
        if let Some(aliases) = self.type_aliases_reverse.get(original) {
            for alias in aliases {
                // Return first non-deprecated alias
                if !self.deprecated_items.contains_key(alias) {
                    return Some(alias.clone());
                }
            }
        }

        // If original itself is not deprecated, suggest it
        if !self.deprecated_items.contains_key(original) {
            return Some(original.to_string());
        }

        None
    }

    /// Find non-deprecated alternatives for a deprecated function
    pub fn find_non_deprecated_function_alternative(&self, name: &str) -> Option<String> {
        // Get the original function (if this is an alias)
        let original = self.function_aliases.get(name).map(|s| s.as_str()).unwrap_or(name);

        // Find all aliases of the original
        if let Some(aliases) = self.function_aliases_reverse.get(original) {
            for alias in aliases {
                // Return first non-deprecated alias
                if !self.deprecated_items.contains_key(alias) {
                    return Some(alias.clone());
                }
            }
        }

        // If original itself is not deprecated, suggest it
        if !self.deprecated_items.contains_key(original) {
            return Some(original.to_string());
        }

        None
    }
}

impl Default for Lowerer {
    fn default() -> Self {
        Self::new()
    }
}
