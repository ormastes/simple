//! C code generation backend.
//!
//! Translates a `MirModule` into a complete C source file that can be compiled
//! with clang/gcc. The generated C links against the Simple runtime (`runtime.h`).

use std::collections::HashMap;

use crate::error::CompileError;
use crate::mir::{MirInst, MirModule};
use crate::value::FUNC_MAIN;

use super::c_instr::{calculate_variant_discriminant, compile_instruction, compile_terminator, sanitize_name, CInstrContext};
use super::c_runtime_ffi::generate_runtime_declarations;
use super::c_types::{type_id_to_c_param, type_id_to_c_return};

/// C code generation backend.
///
/// Unlike `NativeBackend` (which returns `Vec<u8>` object code), this returns
/// a `String` of C source text.
#[derive(Default)]
pub struct CCodegen {
    /// Accumulated C source output.
    output: String,
}

impl CCodegen {
    pub fn new() -> Self {
        Self::default()
    }

    /// Compile a MIR module to a complete C source file.
    pub fn compile_module(&mut self, mir: &MirModule) -> Result<String, CompileError> {
        self.output.clear();

        // 1. Preamble: includes and runtime declarations
        self.emit_preamble();

        // 1b. Collect all lambda names referenced by ClosureCreate instructions.
        //     These lambdas are not emitted as separate MirFunctions, so we emit
        //     a single generic stub and forward-declare each lambda name as an alias.
        let lambda_names = collect_lambda_names(mir);
        if !lambda_names.is_empty() {
            self.output
                .push_str("/* Bootstrap lambda stub (lambdas not executed in bootstrap) */\n");
            self.output
                .push_str("static int64_t __bootstrap_lambda_stub(void) { return 0; }\n");
            for lname in &lambda_names {
                // Emit a #define so that &lambda_name resolves to &__bootstrap_lambda_stub
                self.output.push_str(&format!(
                    "#define {} __bootstrap_lambda_stub\n",
                    lname
                ));
            }
            self.output.push('\n');
        }

        // 1c. Emit module-level global variables as static int64_t (deduplicated)
        if !mir.globals.is_empty() {
            self.output.push_str("/* Module-level global variables */\n");
            let mut seen_globals = std::collections::HashSet::new();
            for (name, init_val) in &mir.globals {
                let sanitized = sanitize_name(name);
                if seen_globals.insert(sanitized.clone()) {
                    self.output.push_str(&format!(
                        "static int64_t __global_{} = {};\n",
                        sanitized, init_val
                    ));
                }
            }
            self.output.push('\n');
        }

        // 2. First pass: compute deduplicated C names for all functions and build
        //    the name resolution map. This maps (sanitized_base_name, param_count)
        //    to the actual C function name (which may have a _N dedup suffix).
        //    Also builds an arity_map for truncating excess arguments at call sites.
        let mut name_counts: HashMap<String, usize> = HashMap::new();
        // Maps (base_name, arity) -> deduplicated C name for resolving call targets
        let mut name_by_arity: HashMap<(String, usize), String> = HashMap::new();
        // Maps base_name -> first deduplicated C name (for calls where arity doesn't match any variant)
        let mut arity_map: HashMap<String, usize> = HashMap::new();

        let mut dedup_names: Vec<String> = Vec::new();
        for func in &mir.functions {
            let base_name = if func.name == FUNC_MAIN {
                "simple_main".to_string()
            } else {
                sanitize_name(&func.name)
            };
            let count = name_counts.entry(base_name.clone()).or_insert(0);
            let c_name = if *count == 0 {
                base_name.clone()
            } else {
                format!("{}_{}", base_name, count)
            };
            *name_counts.get_mut(&base_name).unwrap() += 1;

            // Record the mapping from (base_name, param_count) -> c_name.
            // Use or_insert to keep the FIRST definition (count=0) as the call target.
            // Duplicate functions (count>0) get _N suffixes but their bodies will
            // still call the base function, preventing self-recursion.
            name_by_arity.entry((base_name.clone(), func.params.len())).or_insert(c_name.clone());
            // Record the first definition's arity for the base name
            arity_map.entry(base_name).or_insert(func.params.len());

            dedup_names.push(c_name);
        }

        // 3. Compile all functions, collecting string constants and external calls.
        let mut all_string_constants: Vec<(String, String)> = Vec::new();
        let mut all_external_calls: HashMap<String, std::collections::BTreeSet<usize>> =
            HashMap::new();
        let mut function_bodies: Vec<String> = Vec::new();
        let mut forward_decls: Vec<String> = Vec::new();

        for (func_idx, func) in mir.functions.iter().enumerate() {
            // Forward declaration
            let ret_type = type_id_to_c_return(func.return_type);
            let name = dedup_names[func_idx].clone();

            let params: Vec<String> = func
                .params
                .iter()
                .enumerate()
                .map(|(i, p)| {
                    format!("{} _v{}", type_id_to_c_param(p.ty), i)
                })
                .collect();
            let params_str = if params.is_empty() {
                "void".to_string()
            } else {
                params.join(", ")
            };
            forward_decls.push(format!("{} {}({});", ret_type, name, params_str));

            // Function body
            let mut ctx = CInstrContext::new();
            // Carry forward the string counter from previous functions
            ctx.string_counter = all_string_constants.len();
            // Share resolution maps so call sites can resolve deduplicated names
            // and truncate excess arguments
            ctx.arity_map = arity_map.clone();
            ctx.name_by_arity = name_by_arity.clone();

            let mut body = String::new();
            body.push_str(&format!("{} {}({}) {{\n", ret_type, name, params_str));

            // Declare local variables (all params + locals as int64_t by default)
            // Params are already declared as function parameters (indices 0..params.len())
            // Collect all vregs used in the function to declare them
            let max_vreg = compute_max_vreg(func);
            let param_count = func.params.len() as u32;
            if max_vreg >= param_count {
                let mut decls: Vec<String> = Vec::new();
                for i in param_count..=max_vreg {
                    decls.push(format!("_v{}", i));
                }
                if !decls.is_empty() {
                    body.push_str(&format!("    int64_t {};\n", decls.join(", ")));
                }
            }

            // Declare _local_N stack slots used by LocalAddr instructions
            let local_indices = collect_local_indices(func);
            for idx in &local_indices {
                body.push_str(&format!("    int64_t _local_{};\n", idx));
            }

            // Emit blocks
            for block in &func.blocks {
                body.push_str(&format!("bb{}:;\n", block.id.0));

                // Instructions
                for inst in &block.instructions {
                    compile_instruction(&mut ctx, inst);
                }

                // Terminator
                compile_terminator(&mut ctx, &block.terminator);

                // Flush accumulated lines
                for line in ctx.lines.drain(..) {
                    body.push_str(&line);
                    body.push('\n');
                }
            }

            body.push_str("}\n\n");
            function_bodies.push(body);

            // Collect string constants and external calls from this function
            all_string_constants.extend(ctx.string_constants);
            for (name, arities) in ctx.external_calls {
                all_external_calls
                    .entry(name)
                    .or_default()
                    .extend(arities);
            }
        }

        // 4. Emit string constants
        if !all_string_constants.is_empty() {
            self.output.push_str("/* String constants */\n");
            for (label, value) in &all_string_constants {
                self.output.push_str(&format!(
                    "static const char {}[] = \"{}\";\n",
                    label,
                    escape_c_string(value)
                ));
            }
            self.output.push('\n');
        }

        // 5. Build a map of defined function names → parameter count for method forwarding.
        let mut defined_functions: std::collections::HashSet<String> =
            dedup_names.iter().cloned().collect();
        // Map: function_name → param_count
        let mut func_param_count: HashMap<String, usize> = HashMap::new();
        for (idx, func) in mir.functions.iter().enumerate() {
            func_param_count.insert(dedup_names[idx].clone(), func.params.len());
        }

        // 5b. Scan all function bodies for __spl_method_X( call sites.
        //     For each unique method, collect ALL distinct call-site arities, then
        //     generate arity-aware wrappers. When a method has multiple call arities,
        //     use a variadic macro with __SPL_ARITY_SELECT to dispatch.
        let mut wrapper_bodies_only_out: Vec<String> = Vec::new();
        {
            let combined = function_bodies.join("");
            // Collect method_name → set of observed call arities
            let mut method_arities: HashMap<String, std::collections::BTreeSet<usize>> =
                HashMap::new();

            let re_prefix = "__spl_method_";
            for line in combined.lines() {
                let mut pos = 0;
                while let Some(idx) = line[pos..].find(re_prefix) {
                    let start = pos + idx + re_prefix.len();
                    let end = line[start..]
                        .find(|c: char| !c.is_alphanumeric() && c != '_')
                        .map(|e| start + e)
                        .unwrap_or(line.len());
                    let method_name = &line[start..end];
                    if !method_name.is_empty() {
                        let line_from_call = &line[pos + idx..];
                        if let Some(paren_start) = line_from_call.find('(') {
                            let after_paren = &line_from_call[paren_start + 1..];
                            let call_arity = count_call_args(after_paren);
                            method_arities
                                .entry(method_name.to_string())
                                .or_default()
                                .insert(call_arity);
                        }
                    }
                    pos = end;
                }
            }

            // Build a map from (function_name, arity) → c_name for multi-arity lookups
            // name_by_arity already has this: (base_name, param_count) → c_name

            let mut defines: Vec<String> = Vec::new();
            let mut wrapper_decls: Vec<String> = Vec::new();
            let mut wrapper_bodies: Vec<String> = Vec::new();
            let mut sorted_methods: Vec<String> = method_arities.keys().cloned().collect();
            sorted_methods.sort();

            for method_name in &sorted_methods {
                let full_name = format!("{}{}", re_prefix, method_name);
                // Skip methods already defined as stubs in preamble
                let already_defined = matches!(
                    method_name.as_str(),
                    "lower" | "upper" | "trim" | "contains" | "split_2" | "split_3"
                        | "starts_with" | "ends_with" | "replace"
                );
                if already_defined {
                    continue;
                }
                // Only generate wrapper if the bare function name is defined
                if !defined_functions.contains(method_name.as_str()) {
                    continue;
                }

                let arities = &method_arities[method_name.as_str()];

                if arities.len() == 1 {
                    // Single call arity — straightforward wrapper
                    let call_arity = *arities.iter().next().unwrap();
                    let func_arity = func_param_count
                        .get(method_name.as_str())
                        .copied()
                        .unwrap_or(0);

                    if call_arity == func_arity {
                        defines.push(format!("#define {} {}", full_name, method_name));
                    } else {
                        // Check if there's a function variant with matching arity via name_by_arity
                        let target_name =
                            if let Some(cn) = name_by_arity.get(&(method_name.clone(), call_arity))
                            {
                                cn.clone()
                            } else {
                                method_name.clone()
                            };
                        let target_arity = func_param_count
                            .get(&target_name)
                            .copied()
                            .unwrap_or(func_arity);

                        emit_wrapper(
                            &full_name,
                            &target_name,
                            call_arity,
                            target_arity,
                            &mut wrapper_decls,
                            &mut wrapper_bodies,
                        );
                    }
                } else {
                    // Multiple call arities — need per-arity wrappers + variadic dispatch macro
                    let sorted_arities: Vec<usize> = arities.iter().copied().collect();
                    let max_arity = *sorted_arities.last().unwrap();

                    // Generate a wrapper for each call arity
                    for &call_arity in &sorted_arities {
                        let variant_name = format!("{}_{}", full_name, call_arity);

                        // Find best-matching function for this arity
                        let target_name = if let Some(cn) =
                            name_by_arity.get(&(method_name.clone(), call_arity))
                        {
                            cn.clone()
                        } else {
                            method_name.clone()
                        };
                        let target_arity = func_param_count
                            .get(&target_name)
                            .copied()
                            .unwrap_or(0);

                        if call_arity == target_arity {
                            defines.push(format!("#define {} {}", variant_name, target_name));
                        } else {
                            emit_wrapper(
                                &variant_name,
                                &target_name,
                                call_arity,
                                target_arity,
                                &mut wrapper_decls,
                                &mut wrapper_bodies,
                            );
                        }
                    }

                    // Emit variadic arity selector macro
                    // Pattern: #define __spl_method_X(...) __SPL_SEL_X(__VA_ARGS__, _3, _2, _1)(__VA_ARGS__)
                    let sel_name = format!("__SPL_SEL_{}", method_name);
                    let mut selector_args: Vec<String> = Vec::new();
                    for i in 0..max_arity {
                        selector_args.push(format!("_{}", i + 1));
                    }
                    selector_args.push("NAME".to_string());
                    selector_args.push("...".to_string());

                    defines.push(format!(
                        "#define {}({}) NAME",
                        sel_name,
                        selector_args.join(",")
                    ));

                    // Build the dispatch: __spl_method_X(...) →
                    //   __SPL_SEL_X(__VA_ARGS__, _N, ..., _2, _1)(__VA_ARGS__)
                    let mut dispatch_variants: Vec<String> = Vec::new();
                    for i in (0..max_arity).rev() {
                        let arity = i + 1;
                        if sorted_arities.contains(&arity) {
                            dispatch_variants.push(format!("{}_{}", full_name, arity));
                        } else {
                            // Placeholder for unused arity
                            dispatch_variants.push(format!("{}_{}", full_name, arity));
                        }
                    }

                    defines.push(format!(
                        "#define {}(...) {}(__VA_ARGS__,{})(__VA_ARGS__)",
                        full_name,
                        sel_name,
                        dispatch_variants.join(",")
                    ));

                    // Generate stubs for arities that don't have real call sites
                    // (the selector macro might reference them)
                    for arity in 1..=max_arity {
                        if !sorted_arities.contains(&arity) {
                            let stub_name = format!("{}_{}", full_name, arity);
                            let params: Vec<String> =
                                (0..arity).map(|i| format!("int64_t _a{}", i)).collect();
                            wrapper_decls
                                .push(format!("int64_t {}({});", stub_name, params.join(", ")));
                            wrapper_bodies.push(format!(
                                "int64_t {}({}) {{ return 0; }}",
                                stub_name,
                                params.join(", ")
                            ));
                        }
                    }
                }
            }

            // Emit #defines first (before forward declarations)
            if !defines.is_empty() {
                self.output
                    .push_str("/* Method dispatch forwarding */\n");
                for def in &defines {
                    self.output.push_str(def);
                    self.output.push('\n');
                }
                self.output.push('\n');
            }

            // Emit forward declarations for wrapper functions
            if !wrapper_decls.is_empty() {
                self.output
                    .push_str("/* Method dispatch wrapper forward declarations */\n");
                for decl in &wrapper_decls {
                    self.output.push_str(decl);
                    self.output.push('\n');
                }
                self.output.push('\n');
            }

            // Collect names that are #define'd (these should be excluded from extern decls
            // because the preprocessor would expand them, causing type conflicts).
            for def in &defines {
                // Format: "#define MACRO_NAME target_name" or "#define MACRO_NAME(...) ..."
                if let Some(rest) = def.strip_prefix("#define ") {
                    let name = rest.split_whitespace().next().unwrap_or("");
                    // Strip any parenthesized suffix for variadic macros
                    let name = name.split('(').next().unwrap_or(name);
                    if !name.is_empty() {
                        defined_functions.insert(name.to_string());
                    }
                }
            }
            // Also add wrapper function names
            for decl in &wrapper_decls {
                // Format: "int64_t wrapper_name(...);"
                if let Some(rest) = decl.strip_prefix("int64_t ") {
                    let name = rest.split('(').next().unwrap_or("");
                    if !name.is_empty() {
                        defined_functions.insert(name.to_string());
                    }
                }
            }

            // Store wrapper bodies for emission after function forward declarations
            wrapper_bodies_only_out = wrapper_bodies;
        }

        // 6. Emit forward declarations for all compiled functions
        //    Wrapped in extern "C" so C++ compiled code uses C linkage
        if !forward_decls.is_empty() {
            self.output.push_str("#ifdef __cplusplus\nextern \"C\" {\n#endif\n");
            self.output.push_str("/* Forward declarations */\n");
            for decl in &forward_decls {
                self.output.push_str(decl);
                self.output.push('\n');
            }
            self.output.push('\n');
        }

        // 6a. Emit extern declarations for external function calls.
        //      These are functions called from the compiled code but not defined
        //      in this module. Without declarations, the C compiler assumes they
        //      return `int` (32-bit), which truncates 64-bit pointer return values.
        {
            use super::runtime_ffi::RUNTIME_FUNCS;

            // Build set of names that already have declarations
            let mut declared_names: std::collections::HashSet<String> =
                defined_functions.clone();
            for spec in RUNTIME_FUNCS {
                declared_names.insert(spec.name.to_string());
            }
            // Preamble stubs
            for name in &[
                "__spl_method_lower",
                "__spl_method_upper",
                "__spl_method_trim",
                "__spl_method_contains",
                "__spl_method_split",
                "__spl_method_split_2",
                "__spl_method_split_3",
                "__spl_method_starts_with",
                "__spl_method_ends_with",
                "__spl_method_replace",
                "__spl_to_string",
                "__spl_string_concat",
                "__spl_optional_check",
                "__spl_eq",
                "__bootstrap_lambda_stub",
            ] {
                declared_names.insert(name.to_string());
            }

            let mut extern_decls: Vec<String> = Vec::new();
            let mut struct_constructors: Vec<String> = Vec::new();
            let mut sorted_externals: Vec<(String, std::collections::BTreeSet<usize>)> =
                all_external_calls
                    .iter()
                    .map(|(k, v)| (k.clone(), v.clone()))
                    .collect();
            sorted_externals.sort_by(|a, b| a.0.cmp(&b.0));

            for (name, arities) in &sorted_externals {
                if declared_names.contains(name) {
                    continue;
                }
                // Skip lambda stubs that are #defined
                if lambda_names.contains(name) {
                    continue;
                }

                // Check if this looks like a struct constructor (starts with uppercase,
                // not a dunder method). For these, generate a proper constructor that
                // allocates a runtime object and sets fields, rather than just an extern
                // declaration. This handles struct construction from imported modules.
                let is_struct_ctor = name
                    .chars()
                    .next()
                    .map(|c| c.is_ascii_uppercase())
                    .unwrap_or(false)
                    && !name.starts_with("__");

                // Check if this is an enum variant constructor: contains "__" where
                // both parts start with uppercase, e.g. "HirStmtKind__Expr"
                let is_enum_variant_ctor = is_struct_ctor
                    && name.contains("__")
                    && {
                        let parts: Vec<&str> = name.splitn(2, "__").collect();
                        parts.len() == 2
                            && parts[0]
                                .chars()
                                .next()
                                .map(|c| c.is_ascii_uppercase())
                                .unwrap_or(false)
                            && parts[1]
                                .chars()
                                .next()
                                .map(|c| c.is_ascii_uppercase())
                                .unwrap_or(false)
                    };

                if is_enum_variant_ctor {
                    // Enum variant constructor: use rt_enum_new with discriminant hash
                    let variant_part = name.splitn(2, "__").nth(1).unwrap();
                    let disc = calculate_variant_discriminant(variant_part);
                    let sorted_arities: Vec<usize> = arities.iter().copied().collect();

                    if sorted_arities.len() == 1 {
                        let arity = sorted_arities[0];
                        let params: Vec<String> = (0..arity)
                            .map(|i| format!("int64_t _f{}", i))
                            .collect();
                        let params_str = if params.is_empty() {
                            "void".to_string()
                        } else {
                            params.join(", ")
                        };

                        let mut ctor = String::new();
                        ctor.push_str(&format!(
                            "__attribute__((weak)) int64_t {}({}) {{\n",
                            name, params_str
                        ));

                        if arity == 0 {
                            // Unit variant called as function
                            ctor.push_str(&format!(
                                "    return rt_enum_new(0, (int64_t){}u, 0);\n",
                                disc
                            ));
                        } else if arity == 1 {
                            // Single payload — pass directly as payload
                            ctor.push_str(&format!(
                                "    return rt_enum_new(0, (int64_t){}u, _f0);\n",
                                disc
                            ));
                        } else {
                            // Multiple fields — pack into an object payload
                            ctor.push_str(&format!(
                                "    int64_t _payload = rt_object_new(0, (int64_t){});\n",
                                arity
                            ));
                            for i in 0..arity {
                                ctor.push_str(&format!(
                                    "    rt_object_field_set(_payload, (int64_t){}, _f{});\n",
                                    i * 8,
                                    i
                                ));
                            }
                            ctor.push_str(&format!(
                                "    return rt_enum_new(0, (int64_t){}u, _payload);\n",
                                disc
                            ));
                        }
                        ctor.push_str("}\n");
                        struct_constructors.push(ctor);
                    } else {
                        // Multiple arities for enum variant: emit per-arity variants + dispatch macro
                        let max_arity = *sorted_arities.last().unwrap();
                        for &arity in &sorted_arities {
                            let variant_fn_name = format!("_ctor_{}_{}", name, arity);
                            let params: Vec<String> = (0..arity)
                                .map(|i| format!("int64_t _f{}", i))
                                .collect();
                            let params_str = if params.is_empty() {
                                "void".to_string()
                            } else {
                                params.join(", ")
                            };

                            let mut ctor = String::new();
                            ctor.push_str(&format!(
                                "static int64_t {}({}) {{\n",
                                variant_fn_name, params_str
                            ));

                            if arity == 0 {
                                ctor.push_str(&format!(
                                    "    return rt_enum_new(0, (int64_t){}u, 0);\n",
                                    disc
                                ));
                            } else if arity == 1 {
                                ctor.push_str(&format!(
                                    "    return rt_enum_new(0, (int64_t){}u, _f0);\n",
                                    disc
                                ));
                            } else {
                                ctor.push_str(&format!(
                                    "    int64_t _payload = rt_object_new(0, (int64_t){});\n",
                                    arity
                                ));
                                for i in 0..arity {
                                    ctor.push_str(&format!(
                                        "    rt_object_field_set(_payload, (int64_t){}, _f{});\n",
                                        i * 8,
                                        i
                                    ));
                                }
                                ctor.push_str(&format!(
                                    "    return rt_enum_new(0, (int64_t){}u, _payload);\n",
                                    disc
                                ));
                            }
                            ctor.push_str("}\n");
                            struct_constructors.push(ctor);
                        }

                        // Emit variadic arity selector macro
                        let sel_name = format!("__CTOR_SEL_{}", name);
                        let mut sel_args: Vec<String> = Vec::new();
                        for i in 0..max_arity {
                            sel_args.push(format!("_{}", i + 1));
                        }
                        sel_args.push("NAME".to_string());
                        sel_args.push("...".to_string());
                        struct_constructors.push(format!(
                            "#define {}({}) NAME\n",
                            sel_name,
                            sel_args.join(",")
                        ));

                        // Dispatch macro
                        let mut dispatch_variants: Vec<String> = Vec::new();
                        for i in (0..max_arity).rev() {
                            let a = i + 1;
                            dispatch_variants.push(format!("_ctor_{}_{}", name, a));
                        }
                        struct_constructors.push(format!(
                            "#define {}(...) {}(__VA_ARGS__,{})(__VA_ARGS__)\n",
                            name,
                            sel_name,
                            dispatch_variants.join(",")
                        ));
                    }

                    declared_names.insert(name.clone());
                } else if is_struct_ctor {
                    // Generate per-arity struct constructors with unique suffixed names,
                    // plus a variadic dispatch macro for multi-arity constructors.
                    let sorted_arities: Vec<usize> = arities.iter().copied().collect();
                    let max_arity = *sorted_arities.last().unwrap();

                    if sorted_arities.len() == 1 {
                        // Single arity: emit a simple constructor function (weak
                        // so external definitions like shims take priority)
                        let arity = sorted_arities[0];
                        let params: Vec<String> = (0..arity)
                            .map(|i| format!("int64_t _f{}", i))
                            .collect();
                        let params_str = if params.is_empty() {
                            "void".to_string()
                        } else {
                            params.join(", ")
                        };

                        let mut ctor = String::new();
                        ctor.push_str(&format!(
                            "__attribute__((weak)) int64_t {}({}) {{\n",
                            name, params_str
                        ));
                        ctor.push_str(&format!(
                            "    int64_t _obj = rt_object_new(0, (int64_t){});\n",
                            arity
                        ));
                        for i in 0..arity {
                            ctor.push_str(&format!(
                                "    rt_object_field_set(_obj, (int64_t){}, _f{});\n",
                                i * 8,
                                i
                            ));
                        }
                        ctor.push_str("    return _obj;\n}\n");
                        struct_constructors.push(ctor);
                    } else {
                        // Multiple arities: emit named variants + dispatch macro
                        for &arity in &sorted_arities {
                            let variant_name = format!("_ctor_{}_{}", name, arity);
                            let params: Vec<String> = (0..arity)
                                .map(|i| format!("int64_t _f{}", i))
                                .collect();
                            let params_str = params.join(", ");

                            let mut ctor = String::new();
                            ctor.push_str(&format!(
                                "static int64_t {}({}) {{\n",
                                variant_name, params_str
                            ));
                            ctor.push_str(&format!(
                                "    int64_t _obj = rt_object_new(0, (int64_t){});\n",
                                arity
                            ));
                            for i in 0..arity {
                                ctor.push_str(&format!(
                                    "    rt_object_field_set(_obj, (int64_t){}, _f{});\n",
                                    i * 8,
                                    i
                                ));
                            }
                            ctor.push_str("    return _obj;\n}\n");
                            struct_constructors.push(ctor);
                        }

                        // Emit variadic arity selector macro
                        let sel_name = format!("__CTOR_SEL_{}", name);
                        let mut sel_args: Vec<String> = Vec::new();
                        for i in 0..max_arity {
                            sel_args.push(format!("_{}", i + 1));
                        }
                        sel_args.push("NAME".to_string());
                        sel_args.push("...".to_string());
                        struct_constructors.push(format!(
                            "#define {}({}) NAME\n",
                            sel_name,
                            sel_args.join(",")
                        ));

                        // Dispatch macro
                        let mut dispatch_variants: Vec<String> = Vec::new();
                        for i in (0..max_arity).rev() {
                            let arity = i + 1;
                            dispatch_variants.push(format!("_ctor_{}_{}", name, arity));
                        }
                        struct_constructors.push(format!(
                            "#define {}(...) {}(__VA_ARGS__,{})(__VA_ARGS__)\n",
                            name,
                            sel_name,
                            dispatch_variants.join(",")
                        ));
                    }

                    // Add the name to declared_names so it's not also extern'd
                    declared_names.insert(name.clone());
                } else if arities.len() == 1 {
                    // Single arity: emit typed prototype
                    let arity = *arities.iter().next().unwrap();
                    let params = if arity == 0 {
                        "void".to_string()
                    } else {
                        (0..arity)
                            .map(|_| "int64_t".to_string())
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    extern_decls.push(format!("extern int64_t {}({});", name, params));
                } else {
                    // Multiple arities: emit per-arity extern declarations with
                    // suffixed names, plus a variadic dispatch macro (like constructors).
                    let sorted_arities: Vec<usize> = arities.iter().copied().collect();
                    let max_arity = *sorted_arities.last().unwrap();

                    // Emit typed extern for each arity as unique names
                    for &arity in &sorted_arities {
                        let variant_name = format!("{}_{}", name, arity);
                        let params = if arity == 0 {
                            "void".to_string()
                        } else {
                            (0..arity)
                                .map(|_| "int64_t".to_string())
                                .collect::<Vec<_>>()
                                .join(", ")
                        };
                        extern_decls.push(format!("extern int64_t {}({});", variant_name, params));
                    }

                    // Also emit a dispatch macro for the base name
                    let sel_name = format!("__EXT_SEL_{}", name);
                    let mut sel_args: Vec<String> = Vec::new();
                    for i in 0..max_arity {
                        sel_args.push(format!("_{}", i + 1));
                    }
                    sel_args.push("NAME".to_string());
                    sel_args.push("...".to_string());
                    extern_decls.push(format!(
                        "#define {}({}) NAME",
                        sel_name,
                        sel_args.join(",")
                    ));

                    let mut dispatch_variants: Vec<String> = Vec::new();
                    for &arity in sorted_arities.iter().rev() {
                        dispatch_variants.push(format!("{}_{}", name, arity));
                    }
                    extern_decls.push(format!(
                        "#define {}(...) {}(__VA_ARGS__,{})(__VA_ARGS__)",
                        name,
                        sel_name,
                        dispatch_variants.join(",")
                    ));
                    declared_names.insert(name.clone());
                }
            }

            if !extern_decls.is_empty() {
                self.output
                    .push_str("/* External function declarations (not defined in this module) */\n");
                for decl in &extern_decls {
                    self.output.push_str(decl);
                    self.output.push('\n');
                }
                self.output.push('\n');
            }

            if !struct_constructors.is_empty() {
                self.output.push_str(
                    "/* Auto-generated struct constructors for imported types */\n",
                );
                for ctor in &struct_constructors {
                    self.output.push_str(ctor);
                    self.output.push('\n');
                }
            }
        }

        // Close extern "C" block opened in step 6
        if !forward_decls.is_empty() {
            self.output.push_str("#ifdef __cplusplus\n} /* extern \"C\" */\n#endif\n\n");
        }

        // 6b. Now emit wrapper function bodies (after all forward declarations)
        if !wrapper_bodies_only_out.is_empty() {
            self.output
                .push_str("/* Method dispatch wrapper function bodies */\n");
            for body in &wrapper_bodies_only_out {
                self.output.push_str(body);
                self.output.push('\n');
            }
            self.output.push('\n');
        }

        // 7. Emit function bodies
        for body in &function_bodies {
            self.output.push_str(body);
        }

        // 8. Emit main entry point (if simple_main exists)
        let has_main = mir.functions.iter().any(|f| f.name == FUNC_MAIN);
        if has_main {
            self.emit_entry_point();
        }

        Ok(self.output.clone())
    }

    /// Emit the C preamble (includes, typedefs, runtime declarations).
    fn emit_preamble(&mut self) {
        self.output.push_str("/* Generated by Simple C backend */\n");
        self.output.push_str("#include <stdint.h>\n");
        self.output.push_str("#include <stdlib.h>\n");
        self.output.push_str("#include <string.h>\n");
        self.output.push_str("#include <math.h>\n");
        self.output.push('\n');

        // All external C function declarations wrapped in extern "C" for C++ compatibility
        self.output.push_str("#ifdef __cplusplus\nextern \"C\" {\n#endif\n\n");

        // Runtime FFI declarations
        self.output.push_str(&generate_runtime_declarations());
        self.output.push('\n');

        // Built-in method dispatch — provided by bootstrap_runtime.c
        self.output.push_str("/* Built-in method dispatch — provided by bootstrap_runtime.c */\n");
        self.output.push_str("extern int64_t __spl_method_lower(int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_upper(int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_trim(int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_contains(int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_split_2(int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_split_3(int64_t, int64_t, int64_t);\n");
        // Dispatch macro: select arity based on number of arguments
        self.output.push_str("#define __SPL_SPLIT_SELECT(_1,_2,_3,NAME,...) NAME\n");
        self.output.push_str("#define __spl_method_split(...) __SPL_SPLIT_SELECT(__VA_ARGS__,__spl_method_split_3,__spl_method_split_2)(__VA_ARGS__)\n");
        self.output.push_str("extern int64_t __spl_method_starts_with(int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_ends_with(int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_method_replace(int64_t, int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_to_string(int64_t);\n");
        self.output.push_str("extern int64_t __spl_string_concat(int64_t, int64_t);\n");
        self.output.push_str("extern int64_t __spl_optional_check(int64_t);\n");
        self.output.push_str("extern int64_t __spl_add(int64_t, int64_t);\n");
        self.output.push('\n');

        self.output.push_str("#ifdef __cplusplus\n} /* extern \"C\" */\n#endif\n\n");

        // Runtime equality that handles strings by content (not just pointer compare)
        self.output.push_str("/* Runtime equality — delegates to rt_string_eq for heap strings */\n");
        self.output.push_str("static inline int64_t __spl_eq(int64_t a, int64_t b) {\n");
        self.output.push_str("    if (a == b) return 1;\n");
        self.output.push_str("    if (a != 0 && b != 0 && (uint64_t)a >= 0x10000ULL && (uint64_t)b >= 0x10000ULL) {\n");
        self.output.push_str("        /* Both are heap objects - check types before dereferencing */\n");
        self.output.push_str("        int32_t ta = *(int32_t*)(intptr_t)a;\n");
        self.output.push_str("        int32_t tb = *(int32_t*)(intptr_t)b;\n");
        self.output.push_str("        if (ta == 1 && tb == 1) return rt_string_eq(a, b); /* strings */\n");
        self.output.push_str("        if (ta == 7 && tb == 7) return rt_enum_discriminant(a) == rt_enum_discriminant(b); /* enums */\n");
        self.output.push_str("    }\n");
        self.output.push_str("    /* Handle enum vs discriminant hash: if one is enum, compare its discriminant to the other */\n");
        self.output.push_str("    if (a != 0 && (uint64_t)a >= 0x10000ULL && *(int32_t*)(intptr_t)a == 7) {\n");
        self.output.push_str("        return rt_enum_discriminant(a) == b;\n");
        self.output.push_str("    }\n");
        self.output.push_str("    if (b != 0 && (uint64_t)b >= 0x10000ULL && *(int32_t*)(intptr_t)b == 7) {\n");
        self.output.push_str("        return rt_enum_discriminant(b) == a;\n");
        self.output.push_str("    }\n");
        self.output.push_str("    return 0;\n");
        self.output.push_str("}\n");
        self.output.push('\n');
    }

    /// Emit the C `main` entry point that calls `simple_main`.
    fn emit_entry_point(&mut self) {
        self.output.push_str("/* Entry point */\n");
        self.output
            .push_str("int __saved_argc = 0;\n");
        self.output
            .push_str("char** __saved_argv = NULL;\n");
        self.output
            .push_str("int main(int argc, char** argv) {\n");
        self.output
            .push_str("    __saved_argc = argc;\n");
        self.output
            .push_str("    __saved_argv = argv;\n");
        self.output
            .push_str("    __module_init();\n");
        self.output
            .push_str("    return (int)simple_main();\n");
        self.output.push_str("}\n");
    }
}

/// Generate a wrapper function that adapts call arity to function arity.
fn emit_wrapper(
    wrapper_name: &str,
    target_name: &str,
    call_arity: usize,
    func_arity: usize,
    decls: &mut Vec<String>,
    bodies: &mut Vec<String>,
) {
    let wrapper_params: Vec<String> = (0..call_arity)
        .map(|i| format!("int64_t _a{}", i))
        .collect();
    let wrapper_params_str = if wrapper_params.is_empty() {
        "void".to_string()
    } else {
        wrapper_params.join(", ")
    };

    let forward_args: String = if call_arity == func_arity + 1 {
        // Most common: drop self (arg 0), forward rest
        (1..call_arity)
            .map(|i| format!("_a{}", i))
            .collect::<Vec<_>>()
            .join(", ")
    } else if call_arity > func_arity {
        // Drop excess leading args
        let skip = call_arity - func_arity;
        (skip..call_arity)
            .map(|i| format!("_a{}", i))
            .collect::<Vec<_>>()
            .join(", ")
    } else {
        // call_arity < func_arity: pass all args, pad with zeros
        let mut args: Vec<String> = (0..call_arity).map(|i| format!("_a{}", i)).collect();
        for _ in call_arity..func_arity {
            args.push("0".to_string());
        }
        args.join(", ")
    };

    decls.push(format!("int64_t {}({});", wrapper_name, wrapper_params_str));
    bodies.push(format!(
        "int64_t {}({}) {{ return {}({}); }}",
        wrapper_name, wrapper_params_str, target_name, forward_args
    ));
}

/// Count the number of arguments in a C function call.
/// `text` starts right after the opening parenthesis.
/// Handles nested parentheses and returns 0 for empty `()`.
fn count_call_args(text: &str) -> usize {
    let mut depth = 0i32;
    let mut commas = 0usize;
    let mut has_content = false;
    for c in text.chars() {
        match c {
            '(' => {
                depth += 1;
                has_content = true;
            }
            ')' => {
                if depth == 0 {
                    // Closing paren of the call
                    break;
                }
                depth -= 1;
            }
            ',' if depth == 0 => {
                commas += 1;
            }
            c if !c.is_whitespace() && depth == 0 => {
                has_content = true;
            }
            _ => {}
        }
    }
    if has_content {
        commas + 1
    } else {
        0
    }
}

/// Collect all unique local_index values referenced by LocalAddr instructions.
fn collect_local_indices(func: &crate::mir::MirFunction) -> Vec<usize> {
    use std::collections::BTreeSet;
    let mut indices = BTreeSet::new();
    for block in &func.blocks {
        for inst in &block.instructions {
            if let crate::mir::MirInst::LocalAddr { local_index, .. } = inst {
                indices.insert(*local_index);
            }
        }
    }
    indices.into_iter().collect()
}

/// Compute the maximum VReg index used in a function.
fn compute_max_vreg(func: &crate::mir::MirFunction) -> u32 {
    let mut max = 0u32;
    // Include params
    if !func.params.is_empty() {
        max = (func.params.len() as u32).saturating_sub(1);
    }
    for block in &func.blocks {
        for inst in &block.instructions {
            if let Some(d) = inst.dest() {
                max = max.max(d.0);
            }
            for u in inst.uses() {
                max = max.max(u.0);
            }
        }
        for u in block.terminator.uses() {
            max = max.max(u.0);
        }
    }
    max
}

/// Escape a string for C string literal.
fn escape_c_string(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    for c in s.chars() {
        match c {
            '\\' => out.push_str("\\\\"),
            '"' => out.push_str("\\\""),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            '\0' => out.push_str("\\0"),
            c if c.is_ascii_graphic() || c == ' ' => out.push(c),
            c => {
                // Unicode escape as octal sequences
                let mut buf = [0u8; 4];
                let encoded = c.encode_utf8(&mut buf);
                for b in encoded.bytes() {
                    out.push_str(&format!("\\x{:02x}", b));
                }
            }
        }
    }
    out
}

/// Collect all unique lambda function names referenced by ClosureCreate instructions.
///
/// These lambda functions are referenced in the MIR but not emitted as separate
/// MirFunction entries. We collect their sanitized names so the C backend can
/// emit stubs or #defines to satisfy the linker.
fn collect_lambda_names(mir: &MirModule) -> Vec<String> {
    use std::collections::BTreeSet;
    let mut names = BTreeSet::new();
    // Also collect the set of function names that ARE defined in the module
    let defined: std::collections::HashSet<String> = mir
        .functions
        .iter()
        .map(|f| sanitize_name(&f.name))
        .collect();

    for func in &mir.functions {
        for block in &func.blocks {
            for inst in &block.instructions {
                if let MirInst::ClosureCreate { func_name, .. } = inst {
                    let sname = sanitize_name(func_name);
                    // Only stub lambdas that are NOT already defined as real functions
                    if !defined.contains(&sname) {
                        names.insert(sname);
                    }
                }
            }
        }
    }
    names.into_iter().collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hir::{BinOp, TypeId};
    use crate::mir::{BlockId, MirBlock, MirFunction, MirInst, Terminator, VReg};
    use simple_parser::ast::Visibility;

    /// Helper: create a minimal MIR module with a main function returning 42.
    fn make_return_42_module() -> MirModule {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r0, value: 42 });
        entry.terminator = Terminator::Return(Some(r0));

        let mut module = MirModule::new();
        module.functions.push(func);
        module
    }

    #[test]
    fn test_basic_return_42() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        // Should contain key pieces
        assert!(result.contains("#include <stdint.h>"));
        assert!(result.contains("int64_t simple_main(void)"));
        assert!(result.contains("_v0 = (int64_t)42;"));
        assert!(result.contains("return _v0;"));
        assert!(result.contains("int main(int argc, char** argv)"));
        assert!(result.contains("simple_main()"));
    }

    #[test]
    fn test_add_two_numbers() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();
        let r1 = func.new_vreg();
        let r2 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r0, value: 40 });
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r1, value: 2 });
        entry.instructions.push(MirInst::BinOp {
            dest: r2,
            op: BinOp::Add,
            left: r0,
            right: r1,
        });
        entry.terminator = Terminator::Return(Some(r2));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("_v0 = (int64_t)40;"));
        assert!(result.contains("_v1 = (int64_t)2;"));
        assert!(result.contains("_v2 = __spl_add(_v0, _v1);"));
        assert!(result.contains("return _v2;"));
    }

    #[test]
    fn test_string_constants() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg();
        let r1 = func.new_vreg();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstString {
            dest: r0,
            value: "hello".to_string(),
        });
        entry
            .instructions
            .push(MirInst::ConstInt { dest: r1, value: 0 });
        entry.terminator = Terminator::Return(Some(r1));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("static const char _str_0[] = \"hello\";"));
    }

    #[test]
    fn test_escape_c_string() {
        assert_eq!(escape_c_string("hello"), "hello");
        assert_eq!(escape_c_string("he\"llo"), "he\\\"llo");
        assert_eq!(escape_c_string("line\nnext"), "line\\nnext");
        assert_eq!(escape_c_string("tab\there"), "tab\\there");
        assert_eq!(escape_c_string("back\\slash"), "back\\\\slash");
    }

    #[test]
    fn test_branch_codegen() {
        let mut func = MirFunction::new("main".to_string(), TypeId::I64, Visibility::Public);
        let r0 = func.new_vreg(); // condition
        let r1 = func.new_vreg(); // result

        let then_block = func.new_block();
        let else_block = func.new_block();

        let entry = func.block_mut(BlockId(0)).unwrap();
        entry.instructions.push(MirInst::ConstBool {
            dest: r0,
            value: true,
        });
        entry.terminator = Terminator::Branch {
            cond: r0,
            then_block,
            else_block,
        };

        func.block_mut(then_block).unwrap().instructions.push(
            MirInst::ConstInt { dest: r1, value: 1 },
        );
        func.block_mut(then_block).unwrap().terminator =
            Terminator::Return(Some(r1));

        func.block_mut(else_block).unwrap().instructions.push(
            MirInst::ConstInt { dest: r1, value: 0 },
        );
        func.block_mut(else_block).unwrap().terminator =
            Terminator::Return(Some(r1));

        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("if (_v0) goto bb1; else goto bb2;"));
        assert!(result.contains("bb1:;"));
        assert!(result.contains("bb2:;"));
    }

    #[test]
    fn test_no_entry_point_without_main() {
        let func = MirFunction::new("helper".to_string(), TypeId::I64, Visibility::Public);
        let mut module = MirModule::new();
        module.functions.push(func);

        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        // Should NOT have C main entry point since there's no "main" function
        assert!(!result.contains("int main(int argc"));
    }

    #[test]
    fn test_forward_declarations() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("/* Forward declarations */"));
        assert!(result.contains("int64_t simple_main(void);"));
    }

    #[test]
    fn test_runtime_ffi_declarations() {
        let module = make_return_42_module();
        let mut codegen = CCodegen::new();
        let result = codegen.compile_module(&module).expect("compile ok");

        assert!(result.contains("extern int64_t rt_array_new("));
        assert!(result.contains("extern int64_t rt_string_concat("));
    }
}
