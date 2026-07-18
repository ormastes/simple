use std::collections::HashMap;

use simple_parser::{self as ast, Expr, Module, Node};

use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::{
    HirAopAdvice, HirArchRule, HirCapabilityItem, HirCapabilityPolicy, HirDiBinding, HirDomainBlock,
    HirGlobalArrayInit, HirGlobalFieldInit, HirGlobalStructInit, HirImpl, HirInjectGraph, HirInjectItem, HirLeanBlock,
    HirMockDecl, HirModule, HirSandboxItem, HirSandboxPolicy, HirSecurityGate, HirSecurityItem, HirSecurityPolicy,
    HirType, HirUiPolicy, HirUiPolicyItem, TypeId,
};

fn try_const_eval(expr: &Expr) -> Option<i64> {
    match expr {
        Expr::Integer(val) => Some(*val),
        // RuntimeValue nil is the tagged sentinel 0x3. Recording it here keeps
        // scalar Optional globals in .data instead of raw-zero BSS.
        Expr::Nil => Some(3),
        // Suffixed literals (`11i64`, `0xFF_u32`): same constant, typed form.
        // Without this arm, global initializers using suffixed elements (e.g.
        // FONT_ROWS_PACKED's `...i64` table) were silently dropped → zero table.
        Expr::TypedInteger(val, _) => Some(*val),
        Expr::Binary { op, left, right } => {
            let l = try_const_eval(left)?;
            let r = try_const_eval(right)?;
            match op {
                ast::BinOp::Add => l.checked_add(r),
                ast::BinOp::Sub => l.checked_sub(r),
                ast::BinOp::Mul => l.checked_mul(r),
                ast::BinOp::Div => {
                    if r == 0 {
                        None
                    } else {
                        l.checked_div(r)
                    }
                }
                ast::BinOp::Mod => {
                    if r == 0 {
                        None
                    } else {
                        l.checked_rem(r)
                    }
                }
                ast::BinOp::BitAnd => Some(l & r),
                ast::BinOp::BitOr => Some(l | r),
                ast::BinOp::BitXor => Some(l ^ r),
                ast::BinOp::ShiftLeft => Some(l << (r as u32 & 63)),
                ast::BinOp::ShiftRight => Some(l >> (r as u32 & 63)),
                _ => None,
            }
        }
        Expr::Unary { op, operand } => {
            let v = try_const_eval(operand)?;
            match op {
                ast::UnaryOp::Neg => v.checked_neg(),
                ast::UnaryOp::BitNot => Some(!v),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Const-eval a float initializer. Globals are stored as i64 RuntimeValues and
/// floats travel as f64 bits in i64 (see codegen instr/body.rs f32/f64 ABI), so
/// callers store `result.to_bits()`. Int literals are accepted (`val x: f64 = 3`).
fn try_const_float_eval(expr: &Expr) -> Option<f64> {
    match expr {
        Expr::Float(val) => Some(*val),
        Expr::TypedFloat(val, _) => Some(*val),
        Expr::Integer(val) => Some(*val as f64),
        Expr::TypedInteger(val, _) => Some(*val as f64),
        Expr::Unary {
            op: ast::UnaryOp::Neg,
            operand,
        } => Some(-try_const_float_eval(operand)?),
        Expr::Binary { op, left, right } => {
            let l = try_const_float_eval(left)?;
            let r = try_const_float_eval(right)?;
            match op {
                ast::BinOp::Add => Some(l + r),
                ast::BinOp::Sub => Some(l - r),
                ast::BinOp::Mul => Some(l * r),
                ast::BinOp::Div => Some(l / r),
                _ => None,
            }
        }
        _ => None,
    }
}

fn has_driver_manifest_attr(attrs: &[ast::Attribute]) -> bool {
    attrs
        .iter()
        .any(|attr| attr.name == "driver" || attr.name == "native_lib")
}

fn method_with_impl_driver_attrs(method: &ast::FunctionDef, impl_attrs: &[ast::Attribute]) -> ast::FunctionDef {
    if !has_driver_manifest_attr(impl_attrs) || has_driver_manifest_attr(&method.attributes) {
        return method.clone();
    }
    let mut method = method.clone();
    let mut attrs = impl_attrs.to_vec();
    attrs.extend(method.attributes);
    method.attributes = attrs;
    method
}

fn try_const_array_eval(expr: &Expr) -> Option<Vec<i64>> {
    fn element(expr: &Expr) -> Option<i64> {
        match expr {
            Expr::Bool(value) => Some(i64::from(*value)),
            _ => try_const_eval(expr),
        }
    }

    match expr {
        Expr::Array(elements) => elements.iter().map(element).collect(),
        Expr::ArrayRepeat { value, count } => {
            let value = element(value)?;
            let count = try_const_eval(count)?;
            if count < 0 {
                return None;
            }
            Some(vec![value; count as usize])
        }
        _ => None,
    }
}

fn const_string_of(expr: &Expr) -> Option<String> {
    match expr {
        Expr::String(s) => Some(s.clone()),
        Expr::FString { parts, .. } => {
            if parts.is_empty() {
                return Some(String::new());
            }
            if parts.len() == 1 {
                if let ast::FStringPart::Literal(val) = &parts[0] {
                    return Some(val.clone());
                }
            }
            None
        }
        _ => None,
    }
}

fn try_const_string_array_eval(expr: &Expr) -> Option<Vec<String>> {
    match expr {
        Expr::Array(elements) if !elements.is_empty() => elements.iter().map(const_string_of).collect(),
        _ => None,
    }
}

fn record_const_array_init(
    map: &mut HashMap<String, HirGlobalArrayInit>,
    name: &str,
    ty: TypeId,
    types: &crate::hir::types::TypeRegistry,
    expr: Option<&Expr>,
) {
    let element_type = match types.get(ty) {
        Some(HirType::Array { element, .. }) => *element,
        _ => ty,
    };
    if let Some(values) = expr.and_then(try_const_array_eval) {
        map.insert(
            name.to_string(),
            HirGlobalArrayInit {
                element_type,
                values,
                string_values: None,
            },
        );
    } else if let Some(strings) = expr.and_then(try_const_string_array_eval) {
        // `var slot: [text] = ["..."]` — string-literal elements need runtime
        // rt_string_new allocation; module init pushes them via string_values.
        map.insert(
            name.to_string(),
            HirGlobalArrayInit {
                element_type,
                values: Vec::new(),
                string_values: Some(strings),
            },
        );
    } else if expr.is_none() {
        // `var name: [T; N]` with no initializer — lower to a zero-filled
        // global, exactly like `= [0; N]`. Without this the global stays a
        // scalar tagged slot: reads return garbage and writes are lost or
        // fault (seed segfault on uninit module array var).
        if let Some(HirType::Array { size: Some(n), .. }) = types.get(ty) {
            map.insert(
                name.to_string(),
                HirGlobalArrayInit {
                    element_type,
                    values: vec![0; *n],
                    string_values: None,
                },
            );
        }
    }
}

fn record_struct_literal_init(
    map: &mut HashMap<String, HirGlobalStructInit>,
    name: &str,
    ty: TypeId,
    types: &crate::hir::types::TypeRegistry,
    expr: &Expr,
) {
    // Module-level `var g: S = S(field: <simple>, ...)`. Without this the
    // initializer is silently dropped and the global stays 0 in BSS — any
    // field access through it segfaults in native binaries (stage4
    // sugar_registry::rule_registry crash, 2026-06-10).
    // Struct literals reach module_pass in two AST shapes:
    //   `S { field: v }`  -> Expr::StructInit
    //   `S(field: v)`     -> Expr::Call with named Arguments (paren form)
    let (lit_name, literal_fields): (&str, Vec<(&str, &Expr)>) = match expr {
        Expr::StructInit { name, fields, spread } => {
            if spread.is_some() {
                return;
            }
            (name.as_str(), fields.iter().map(|(n, e)| (n.as_str(), e)).collect())
        }
        Expr::Call { callee, args } => {
            let Expr::Identifier(callee_name) = callee.as_ref() else {
                return;
            };
            let mut pairs = Vec::with_capacity(args.len());
            for arg in args {
                let Some(arg_name) = &arg.name else {
                    return; // positional args: not a recognizable struct literal
                };
                pairs.push((arg_name.as_str(), &arg.value));
            }
            (callee_name.as_str(), pairs)
        }
        _ => return,
    };
    // Field order/offsets come from the declared struct type so named-arg
    // reordering in the literal cannot scramble the layout.
    let Some(crate::hir::types::HirType::Struct {
        name: ty_name,
        fields: ty_fields,
        ..
    }) = types.get(ty)
    else {
        return;
    };
    if ty_name != lit_name {
        return;
    }
    let mut inits = Vec::with_capacity(ty_fields.len());
    for (field_name, _) in ty_fields {
        let Some((_, fexpr)) = literal_fields.iter().find(|(n, _)| *n == field_name.as_str()) else {
            // Missing field — zero-fill, matching compile_struct_init's default.
            inits.push(HirGlobalFieldInit::Value(0));
            continue;
        };
        let init = match fexpr {
            Expr::Integer(v) => HirGlobalFieldInit::Value(*v),
            Expr::Bool(b) => HirGlobalFieldInit::Value(if *b { 1 } else { 0 }),
            Expr::Nil => HirGlobalFieldInit::Value(3), // tagged nil
            Expr::Float(f) => HirGlobalFieldInit::Value(f.to_bits() as i64),
            Expr::String(v) => HirGlobalFieldInit::Str(v.clone()),
            Expr::Array(elems) if elems.is_empty() => HirGlobalFieldInit::EmptyArray,
            // Any non-simple field value: leave the whole struct unrecorded
            // (pre-existing zero-in-BSS limitation, now scoped + documented).
            _ => return,
        };
        inits.push(init);
    }
    map.insert(name.to_string(), HirGlobalStructInit { fields: inits });
}

fn record_function_init(
    map: &mut HashMap<String, String>,
    name: &str,
    ty: TypeId,
    types: &crate::hir::types::TypeRegistry,
    expr: Option<&Expr>,
) {
    if !matches!(types.get(ty), Some(HirType::Function { .. })) {
        return;
    }
    let Some(expr) = expr else {
        return;
    };
    let func_name = match expr {
        Expr::Identifier(name) => name.clone(),
        Expr::Path(parts) => parts.join("."),
        _ => return,
    };
    map.insert(name.to_string(), func_name);
}

fn is_domain_block_kind(kind: &str) -> bool {
    matches!(
        kind,
        "schema" | "style" | "ui" | "music" | "bim" | "cad" | "city" | "rtl"
    )
}

impl Lowerer {
    /// Helper: Register type and function declarations from an AST node
    fn register_declarations_from_node(&mut self, item: &Node) -> LowerResult<()> {
        match item {
            Node::Struct(s) => {
                let struct_type_id = self.register_struct(s)?;
                // Register struct constructor in globals so it can be used as a value
                self.globals.insert(s.name.clone(), struct_type_id);
                self.local_globals.insert(s.name.clone());
                for method in &s.methods {
                    let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                    let qualified = format!("{}.{}", s.name, method.name);
                    self.globals.insert(qualified.clone(), ret_ty);
                    self.local_globals.insert(qualified);
                }
            }
            Node::Function(f) => {
                let ret_ty = self.resolve_type_opt(&f.return_type)?;
                self.globals.insert(f.name.clone(), ret_ty);
                self.local_globals.insert(f.name.clone());
                // Track pure functions for CTR-030-032
                if f.is_pure() {
                    self.pure_functions.insert(f.name.clone());
                }
            }
            Node::Class(c) => {
                let class_type_id = self.register_class(c)?;
                // Register class constructor in globals so it can be used as a value
                self.globals.insert(c.name.clone(), class_type_id);
                self.local_globals.insert(c.name.clone());
                for method in &c.methods {
                    let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                    let qualified = format!("{}.{}", c.name, method.name);
                    self.globals.insert(qualified.clone(), ret_ty);
                    self.local_globals.insert(qualified);
                }
            }
            Node::Enum(e) => {
                let variants: Vec<_> = e
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

                // Get the enum type ID
                let enum_type_id = self.module.types.lookup(&e.name).unwrap_or_else(|| {
                    eprintln!("[WARNING] Enum type not found during registration: {}", e.name);
                    TypeId::VOID
                });

                // Use update_named to update the placeholder created in Pass 0
                self.module.types.update_named(
                    e.name.clone(),
                    HirType::Enum {
                        name: e.name.clone(),
                        variants,
                        generic_params: e.generic_params.clone(),
                        is_generic_template: e.is_generic_template,
                        type_bindings: std::collections::HashMap::new(), // Will be filled during specialization
                    },
                );

                // Register enum name in globals so that Backend.Native can be resolved
                // The enum name acts as a namespace for variant constructors
                self.globals.insert(e.name.clone(), enum_type_id);
                self.local_globals.insert(e.name.clone());
                for method in &e.methods {
                    let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                    let qualified = format!("{}.{}", e.name, method.name);
                    self.globals.insert(qualified.clone(), ret_ty);
                    self.local_globals.insert(qualified);
                }
            }
            Node::Mixin(m) => {
                self.register_mixin(m)?;
            }
            Node::Impl(impl_block) => {
                let type_name = match &impl_block.target_type {
                    simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                    simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                    _ => None,
                };
                if let Some(type_name) = type_name {
                    for method in &impl_block.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", type_name, method.name);
                        self.globals.insert(qualified.clone(), ret_ty);
                        self.local_globals.insert(qualified);
                    }
                }
            }
            Node::Bitfield(bf) => {
                let bitfield_type_id = self.register_bitfield(bf)?;
                self.globals.insert(bf.name.clone(), bitfield_type_id);
                self.local_globals.insert(bf.name.clone());
            }
            Node::TypeAlias(ta) => {
                self.register_type_alias(ta)?;
            }
            Node::ClassAlias(ca) => {
                // Register class/struct/enum alias mapping
                self.register_type_alias_mapping(ca.name.clone(), ca.target.clone());

                // Check for @deprecated decorator
                for decorator in &ca.decorators {
                    if let ast::Expr::Identifier(name) = &decorator.name {
                        if name == "deprecated" {
                            // Extract message from decorator args if present
                            let msg = decorator.args.as_ref().and_then(|args| {
                                args.first().and_then(|arg| {
                                    if let ast::Expr::String(s) = &arg.value {
                                        Some(s.clone())
                                    } else {
                                        None
                                    }
                                })
                            });
                            self.mark_deprecated(ca.name.clone(), msg);
                        }
                    }
                }
            }
            Node::FunctionAlias(fa) => {
                // Register function alias mapping
                self.register_function_alias(fa.name.clone(), fa.target.clone());

                // Check for @deprecated decorator
                for decorator in &fa.decorators {
                    if let ast::Expr::Identifier(name) = &decorator.name {
                        if name == "deprecated" {
                            // Extract message from decorator args if present
                            let msg = decorator.args.as_ref().and_then(|args| {
                                args.first().and_then(|arg| {
                                    if let ast::Expr::String(s) = &arg.value {
                                        Some(s.clone())
                                    } else {
                                        None
                                    }
                                })
                            });
                            self.mark_deprecated(fa.name.clone(), msg);
                        }
                    }
                }
            }
            Node::Trait(t) => {
                // Register trait with vtable slot information for static polymorphism
                self.register_trait(t)?;
            }
            Node::Actor(a) => {
                // Register actor as a class type (actors are classes with message-passing semantics)
                let class_def = ast::ClassDef {
                    span: a.span,
                    name: a.name.clone(),
                    generic_params: vec![],
                    where_clause: vec![],
                    fields: a.fields.clone(),
                    methods: a.methods.clone(),
                    parent: None,
                    visibility: a.visibility,
                    effects: vec![],
                    attributes: vec![],
                    doc_comment: None,
                    is_generic_template: false,
                    specialization_of: None,
                    type_bindings: std::collections::HashMap::new(),
                    is_value_type: false,
                    invariant: None,
                    macro_invocations: vec![],
                    mixins: vec![],
                };
                let actor_type_id = self.register_class(&class_def)?;
                self.globals.insert(a.name.clone(), actor_type_id);
                self.local_globals.insert(a.name.clone());
                for method in &a.methods {
                    let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                    let qualified = format!("{}.{}", a.name, method.name);
                    self.globals.insert(qualified.clone(), ret_ty);
                    self.local_globals.insert(qualified);
                }
            }
            Node::Extern(e) => {
                // Register extern function in globals so it can be called
                let ret_ty = self.resolve_type_opt(&e.return_type)?;
                self.globals.insert(e.name.clone(), ret_ty);
                self.local_globals.insert(e.name.clone());
                // Track as extern function for codegen (BSS slot initialization)
                self.extern_fn_names.insert(e.name.clone());
            }
            Node::ExternClass(ec) => {
                // Register extern class type
                // For now, just register the class name as a named type
                let type_id = self.module.types.register_named(
                    ec.name.clone(),
                    crate::hir::types::HirType::ExternClass { name: ec.name.clone() },
                );
                // Also register it as a global so it can be used in type expressions
                self.globals.insert(ec.name.clone(), type_id);
            }
            Node::Static(s) => {
                // Register global/static variable
                // Resolve the type if provided, otherwise use Any for dynamic typing
                let ty = if let Some(ref t) = s.ty {
                    self.resolve_type(t).unwrap_or(TypeId::ANY)
                } else {
                    TypeId::ANY
                };
                self.globals.insert(s.name.clone(), ty);
                self.local_globals.insert(s.name.clone());
                if matches!(s.mutability, ast::Mutability::Immutable) {
                    self.immutable_globals.insert(s.name.clone());
                }
                // Extract compile-time constant value from initializer.
                // Float-typed globals first: `val x: f64 = 3` must store f64
                // bits, not raw int 3 (globals are i64 slots; float loads
                // reinterpret the bits). Untyped float globals (ty=ANY) are
                // still zero-initialized — bug cranelift_f32_trig Residual.
                if matches!(ty, TypeId::F64 | TypeId::F32) {
                    if let Some(fval) = try_const_float_eval(&s.value) {
                        // GlobalLoad reads the slot with the cranelift type of the
                        // global: f64 loads 8 bytes, f32 loads the low 4 — store
                        // matching raw bits.
                        let bits = if ty == TypeId::F32 {
                            (fval as f32).to_bits() as i64
                        } else {
                            fval.to_bits() as i64
                        };
                        self.global_init_values.insert(s.name.clone(), bits);
                    }
                } else if let Some(val) = try_const_eval(&s.value) {
                    self.global_init_values.insert(s.name.clone(), val);
                } else if let Expr::String(val) = &s.value {
                    self.global_init_strings.insert(s.name.clone(), val.clone());
                } else if let Expr::FString { parts, .. } = &s.value {
                    if parts.is_empty() {
                        self.global_init_strings.insert(s.name.clone(), String::new());
                    } else if parts.len() == 1 {
                        if let ast::FStringPart::Literal(val) = &parts[0] {
                            self.global_init_strings.insert(s.name.clone(), val.clone());
                        }
                    }
                } else if let Expr::Bool(val) = &s.value {
                    // Store tagged boolean value: TAG_SPECIAL(0b011) | (payload << 3)
                    let tagged = 0b011 | ((if *val { 1 } else { 2 }) << 3);
                    self.global_init_values.insert(s.name.clone(), tagged);
                }
                record_const_array_init(
                    &mut self.global_init_arrays,
                    &s.name,
                    ty,
                    &self.module.types,
                    Some(&s.value),
                );
                record_function_init(
                    &mut self.global_init_functions,
                    &s.name,
                    ty,
                    &self.module.types,
                    Some(&s.value),
                );
                record_struct_literal_init(&mut self.global_init_structs, &s.name, ty, &self.module.types, &s.value);
            }
            Node::Const(c) => {
                // Register constant
                let ty = if let Some(ref t) = c.ty {
                    self.resolve_type(t).unwrap_or(TypeId::ANY)
                } else if try_const_eval(&c.value).is_some() {
                    // Unannotated integer literal const → infer i64 so comparisons
                    // against it don't fall into the ANY boxing path (bug: stage4_imported_const_compare)
                    TypeId::I64
                } else if matches!(&c.value, Expr::String(_) | Expr::FString { .. }) {
                    TypeId::STRING
                } else {
                    TypeId::ANY
                };
                self.globals.insert(c.name.clone(), ty);
                self.local_globals.insert(c.name.clone());
                self.immutable_globals.insert(c.name.clone());
                // Extract compile-time constant value from initializer.
                // Float-typed consts store f64 bits (see Static branch above).
                if matches!(ty, TypeId::F64 | TypeId::F32) {
                    if let Some(fval) = try_const_float_eval(&c.value) {
                        let bits = if ty == TypeId::F32 {
                            (fval as f32).to_bits() as i64
                        } else {
                            fval.to_bits() as i64
                        };
                        self.global_init_values.insert(c.name.clone(), bits);
                    }
                } else if let Some(val) = try_const_eval(&c.value) {
                    self.global_init_values.insert(c.name.clone(), val);
                } else if let Expr::String(val) = &c.value {
                    self.global_init_strings.insert(c.name.clone(), val.clone());
                } else if let Expr::FString { parts, .. } = &c.value {
                    if parts.is_empty() {
                        self.global_init_strings.insert(c.name.clone(), String::new());
                    } else if parts.len() == 1 {
                        if let ast::FStringPart::Literal(val) = &parts[0] {
                            self.global_init_strings.insert(c.name.clone(), val.clone());
                        }
                    }
                } else if let Expr::Bool(val) = &c.value {
                    let tagged = 0b011 | ((if *val { 1 } else { 2 }) << 3);
                    self.global_init_values.insert(c.name.clone(), tagged);
                }
                record_const_array_init(
                    &mut self.global_init_arrays,
                    &c.name,
                    ty,
                    &self.module.types,
                    Some(&c.value),
                );
                record_function_init(
                    &mut self.global_init_functions,
                    &c.name,
                    ty,
                    &self.module.types,
                    Some(&c.value),
                );
                record_struct_literal_init(&mut self.global_init_structs, &c.name, ty, &self.module.types, &c.value);
            }
            Node::Let(l) => {
                // Register module-level variable (var at module scope = global)
                // Extract name from pattern, handling Pattern::Typed wrapper
                let name = extract_pattern_name(&l.pattern);
                if let Some(n) = name {
                    // Resolve type: check l.ty first, then Pattern::Typed wrapper.
                    // The parser stores type annotations in Pattern::Typed (l.ty is None)
                    // when parsing `var name: Type = value`.
                    let ty = if let Some(ref t) = l.ty {
                        self.resolve_type(t).unwrap_or(TypeId::ANY)
                    } else if let Some(ref t) = extract_pattern_type(&l.pattern) {
                        self.resolve_type(t).unwrap_or(TypeId::ANY)
                    } else {
                        TypeId::ANY
                    };
                    self.globals.insert(n.clone(), ty);
                    self.local_globals.insert(n.clone());
                    if matches!(l.mutability, ast::Mutability::Immutable) {
                        self.immutable_globals.insert(n.clone());
                    }
                    // Extract compile-time constant value from initializer.
                    // Float-typed globals first (see Static branch): store raw
                    // f64/f32 bits matching GlobalLoad's typed load.
                    if matches!(ty, TypeId::F64 | TypeId::F32) {
                        if let Some(fval) = l.value.as_ref().and_then(try_const_float_eval) {
                            let bits = if ty == TypeId::F32 {
                                (fval as f32).to_bits() as i64
                            } else {
                                fval.to_bits() as i64
                            };
                            self.global_init_values.insert(n.clone(), bits);
                        }
                    } else if let Some(val) = l.value.as_ref().and_then(try_const_eval) {
                        self.global_init_values.insert(n.clone(), val);
                    } else if let Some(Expr::String(val)) = &l.value {
                        self.global_init_strings.insert(n.clone(), val.clone());
                    } else if let Some(Expr::FString { parts, .. }) = &l.value {
                        if parts.is_empty() {
                            self.global_init_strings.insert(n.clone(), String::new());
                        } else if parts.len() == 1 {
                            if let ast::FStringPart::Literal(val) = &parts[0] {
                                self.global_init_strings.insert(n.clone(), val.clone());
                            }
                        }
                    } else if let Some(Expr::Bool(val)) = &l.value {
                        let tagged = 0b011 | ((if *val { 1 } else { 2 }) << 3);
                        self.global_init_values.insert(n.clone(), tagged);
                    }
                    record_const_array_init(
                        &mut self.global_init_arrays,
                        &n,
                        ty,
                        &self.module.types,
                        l.value.as_ref(),
                    );
                    record_function_init(
                        &mut self.global_init_functions,
                        &n,
                        ty,
                        &self.module.types,
                        l.value.as_ref(),
                    );
                    if let Some(value) = l.value.as_ref() {
                        record_struct_literal_init(&mut self.global_init_structs, &n, ty, &self.module.types, value);
                    }
                }
            }
            _ => {}
        }
        Ok(())
    }

    /// Lower Lean 4 blocks from AST to HIR.
    ///
    /// This collects all lean blocks (inline code and imports) for later
    /// emission during Lean code generation.
    fn lower_lean_blocks(&mut self, ast_module: &Module) {
        let module_name = ast_module.name.clone().unwrap_or_else(|| "module".to_string());

        for item in &ast_module.items {
            if let Node::LeanBlock(lean_block) = item {
                let context = module_name.clone();

                let hir_lean_block = if let Some(ref import_path) = lean_block.import_path {
                    if lean_block.code.is_empty() {
                        HirLeanBlock::import(import_path.clone(), context)
                    } else {
                        HirLeanBlock::import_with_code(import_path.clone(), lean_block.code.clone(), context)
                    }
                } else {
                    HirLeanBlock::inline(lean_block.code.clone(), context)
                };

                self.module.lean_blocks.push(hir_lean_block);
            }
        }
    }

    /// Lower raw top-level domain blocks from AST to HIR metadata.
    ///
    /// Domain semantics are intentionally not interpreted here. This pass only
    /// records payloads that were authored at module scope so later schema,
    /// style, music, BIM, CAD, city, and RTL passes can validate them.
    fn lower_domain_blocks(&mut self, ast_module: &Module) {
        let module_name = ast_module.name.clone().unwrap_or_else(|| "module".to_string());

        for item in &ast_module.items {
            if let Node::Expression(Expr::BlockExpr { kind, payload }) = item {
                if is_domain_block_kind(kind) {
                    self.module.domain_blocks.push(HirDomainBlock::new(
                        kind.clone(),
                        payload.clone(),
                        module_name.clone(),
                    ));
                }
            }
        }
    }

    /// Lower AOP constructs (advice, DI bindings, architecture rules, mocks) from AST to HIR.
    ///
    /// This pass processes:
    /// - AOP advice (before/after/around interceptors) #1000-1050
    /// - Dependency injection bindings
    /// - Architecture rules (forbid/allow patterns)
    /// - Mock declarations for testing
    fn lower_aop_constructs(&mut self, ast_module: &Module) -> LowerResult<()> {
        for item in &ast_module.items {
            match item {
                Node::AopAdvice(advice) => {
                    self.module.aop_advices.push(HirAopAdvice {
                        predicate_text: self.predicate_to_string(&advice.pointcut),
                        advice_function: advice.interceptor.clone(),
                        form: advice.advice_type.as_str().to_string(),
                        priority: advice.priority.unwrap_or(0),
                    });
                }
                Node::DiBinding(binding) => {
                    self.module.di_bindings.push(HirDiBinding {
                        predicate_text: self.predicate_to_string(&binding.pointcut),
                        implementation: binding.implementation.clone(),
                        scope: binding.scope.map(|s| s.as_str().to_string()),
                        priority: binding.priority.unwrap_or(0),
                    });
                }
                Node::InjectGraph(graph) => {
                    self.module.inject_graphs.push(HirInjectGraph {
                        name: graph.name.clone(),
                        mode: graph.mode.map(|m| m.as_str().to_string()),
                        items: self.lower_inject_items(&graph.items)?,
                    });
                }
                Node::SecurityPolicy(policy) => {
                    self.module.security_policies.push(HirSecurityPolicy {
                        name: policy.name.clone(),
                        conventions_enabled: policy.conventions_enabled,
                        items: self.lower_security_items(&policy.items),
                    });
                }
                Node::SecurityGate(gate) => {
                    self.module.security_gates.push(Self::lower_security_gate(gate));
                }
                Node::SandboxPolicy(policy) => {
                    self.module.sandbox_policies.push(HirSandboxPolicy {
                        name: policy.name.clone(),
                        items: policy
                            .items
                            .iter()
                            .map(|item| match item {
                                ast::SandboxItem::Backend { name, .. } => {
                                    HirSandboxItem::Backend { name: name.clone() }
                                }
                                ast::SandboxItem::Rule { key, value, .. } => HirSandboxItem::Rule {
                                    key: key.clone(),
                                    value: value.clone(),
                                },
                            })
                            .collect(),
                    });
                }
                Node::CapabilityPolicy(policy) => {
                    self.module.capability_policies.push(HirCapabilityPolicy {
                        name: policy.name.clone(),
                        items: policy
                            .items
                            .iter()
                            .map(|item| match item {
                                ast::CapabilityItem::Rule { key, value, .. } => HirCapabilityItem::Rule {
                                    key: key.clone(),
                                    value: value.clone(),
                                },
                            })
                            .collect(),
                    });
                }
                Node::UiPolicy(policy) => {
                    self.module.ui_policies.push(HirUiPolicy {
                        name: policy.name.clone(),
                        items: policy
                            .items
                            .iter()
                            .map(|item| match item {
                                ast::UiPolicyItem::Show { key, condition, .. } => HirUiPolicyItem::Show {
                                    key: key.clone(),
                                    condition: condition.clone(),
                                },
                                ast::UiPolicyItem::Raw { text, .. } => HirUiPolicyItem::Raw { text: text.clone() },
                            })
                            .collect(),
                    });
                }
                Node::ArchitectureRule(rule) => {
                    self.module.arch_rules.push(HirArchRule {
                        rule_type: match rule.rule_type {
                            ast::ArchRuleType::Forbid => "forbid".to_string(),
                            ast::ArchRuleType::Allow => "allow".to_string(),
                        },
                        predicate_text: self.predicate_to_string(&rule.pointcut),
                        message: rule.message.clone(),
                        priority: 0,
                    });
                }
                Node::MockDecl(mock) => {
                    let mut expectations = Vec::new();
                    for exp in &mock.expectations {
                        expectations.push(self.lower_mock_expectation(exp)?);
                    }
                    self.module.mock_decls.push(HirMockDecl {
                        name: mock.name.clone(),
                        trait_name: mock.trait_name.clone(),
                        expectations,
                    });
                }
                _ => {}
            }
        }
        let generated_security_aop = crate::security::lower_security_to_aop(&self.module);
        self.module.aop_advices.extend(generated_security_aop.aop_advices);
        self.module.arch_rules.extend(generated_security_aop.arch_rules);
        Ok(())
    }

    fn lower_security_items(&self, items: &[ast::SecurityItem]) -> Vec<HirSecurityItem> {
        items
            .iter()
            .map(|item| match item {
                ast::SecurityItem::Root { path, .. } => HirSecurityItem::Root { path: path.clone() },
                ast::SecurityItem::Default { action, .. } => HirSecurityItem::Default { action: action.clone() },
                ast::SecurityItem::Dimension { name, rules, .. } => HirSecurityItem::Dimension {
                    name: name.clone(),
                    rules: rules.clone(),
                },
                ast::SecurityItem::Allow {
                    from,
                    to,
                    through,
                    configurable,
                    final_rule,
                    ..
                } => HirSecurityItem::Allow {
                    from: from.clone(),
                    to: to.clone(),
                    through: through.clone(),
                    configurable: *configurable,
                    final_rule: *final_rule,
                },
                ast::SecurityItem::Deny {
                    from,
                    to,
                    except,
                    direct,
                    configurable,
                    final_rule,
                    ..
                } => HirSecurityItem::Deny {
                    from: from.clone(),
                    to: to.clone(),
                    except: except.clone(),
                    direct: *direct,
                    configurable: *configurable,
                    final_rule: *final_rule,
                },
                ast::SecurityItem::Gate(gate) => HirSecurityItem::Gate(Self::lower_security_gate(gate)),
                ast::SecurityItem::Raw { text, .. } => HirSecurityItem::Raw { text: text.clone() },
            })
            .collect()
    }

    fn lower_security_gate(gate: &ast::SecurityGate) -> HirSecurityGate {
        HirSecurityGate {
            name: gate.name.clone(),
            from: gate.from.clone(),
            to: gate.to.clone(),
            policy: gate.policy.clone(),
            audit: gate.audit.clone(),
            sandbox: gate.sandbox.clone(),
            grants: gate.grants.clone(),
            body: gate.body.clone(),
        }
    }

    fn lower_inject_items(&self, items: &[ast::InjectItem]) -> LowerResult<Vec<HirInjectItem>> {
        let mut lowered = Vec::new();
        for item in items {
            lowered.push(match item {
                ast::InjectItem::Root { type_ref, .. } => HirInjectItem::Root {
                    type_ref: type_ref.clone(),
                },
                ast::InjectItem::Scan { pattern, .. } => HirInjectItem::Scan {
                    pattern: pattern.clone(),
                },
                ast::InjectItem::Load { path, .. } => {
                    crate::di::validate_local_child_config_path(path).map_err(LowerError::Unsupported)?;
                    HirInjectItem::Load { path: path.clone() }
                }
                ast::InjectItem::Bind {
                    service,
                    target,
                    lifetime,
                    configurable,
                    final_binding,
                    ..
                } => HirInjectItem::Bind {
                    service: service.clone(),
                    target: target.clone(),
                    lifetime: lifetime.map(|l| self.inject_lifetime_to_string(l)),
                    configurable: *configurable,
                    final_binding: *final_binding,
                },
                ast::InjectItem::Slot {
                    service,
                    qualifier,
                    default_target,
                    ..
                } => HirInjectItem::Slot {
                    service: service.clone(),
                    qualifier: qualifier.clone(),
                    default_target: default_target.clone(),
                },
                ast::InjectItem::Profile { name, items, .. } => HirInjectItem::Profile {
                    name: name.clone(),
                    items: self.lower_inject_items(items)?,
                },
            });
        }
        Ok(lowered)
    }

    fn inject_lifetime_to_string(&self, lifetime: ast::InjectLifetime) -> String {
        match lifetime {
            ast::InjectLifetime::Transient => "transient",
            ast::InjectLifetime::Singleton => "singleton",
            ast::InjectLifetime::Scoped => "scoped",
            ast::InjectLifetime::Arena => "arena",
            ast::InjectLifetime::Request => "request",
            ast::InjectLifetime::Thread => "thread",
            ast::InjectLifetime::Task => "task",
            ast::InjectLifetime::Static => "static",
            ast::InjectLifetime::Extern => "extern",
        }
        .to_string()
    }

    /// Pass 0.5c: Populate `method_return_types` for free functions reached via
    /// the whole-program import map (called without a `use` import). Such calls
    /// otherwise have no return-type info, so their result is ANY and field
    /// access on the result fails ("cannot infer field type, struct 'ANY'").
    /// We resolve each function's declared return type now that all
    /// imported types (and `global_struct_defs`) are available.
    /// ADDITIVE: only fills entries that are missing or ANY, and only when the
    /// return type resolves to a concrete type — never downgrades.
    fn populate_global_fn_return_types(&mut self) {
        let Some(map) = self.global_fn_return_types.clone() else {
            return;
        };
        let debug = std::env::var("SIMPLE_DEBUG_ANYRET").is_ok();
        let mut upgraded = 0usize;
        for (fn_name, ret_type) in map.iter() {
            match self.method_return_types.get(fn_name) {
                Some(&existing) if existing != TypeId::ANY => continue,
                _ => {}
            }
            if let Ok(resolved) = self.resolve_type(ret_type) {
                if resolved != TypeId::ANY {
                    self.method_return_types.insert(fn_name.clone(), resolved);
                    upgraded += 1;
                }
            }
        }
        if debug {
            eprintln!("[ANYRET-GLOBAL] upgraded={}", upgraded);
        }
    }

    /// M12 3b: record each free function's parameter default-value expressions
    /// so omitted trailing arguments can be filled at call sites (`lower_call`).
    /// Captured here (from the AST) because the HIR function *type* carries only
    /// parameter TypeIds, not the default exprs.
    fn collect_fn_param_defaults(&mut self, ast_module: &Module) {
        for item in &ast_module.items {
            if let Node::Function(f) = item {
                if f.params.iter().any(|p| p.default.is_some()) {
                    self.fn_param_defaults
                        .insert(f.name.clone(), f.params.iter().map(|p| p.default.clone()).collect());
                }
            }
        }
    }

    pub fn lower_module(mut self, ast_module: &Module) -> LowerResult<HirModule> {
        // Hoist nested type definitions (e.g. `class Foo:` defined inside an
        // SPipe `it` block) to module scope so the rest of the lowering
        // pipeline registers them as if they were authored at the top level.
        // See `nested_def_hoist.rs` for the rules and rationale.
        let hoisted = super::nested_def_hoist::module_with_hoisted_defs(ast_module);
        let ast_module: &Module = hoisted.as_ref().unwrap_or(ast_module);

        self.module.name = ast_module.name.clone();
        self.collect_fn_param_defaults(ast_module);

        // Pass 0: Pre-register all struct/class/enum names to allow self-referential types
        // This registers placeholders so types can reference each other
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    // Register placeholder struct so it can be referenced by other types
                    self.module.types.register_named(
                        s.name.clone(),
                        HirType::Struct {
                            name: s.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: s.generic_params.clone(),
                            is_generic_template: s.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Class(c) => {
                    // Register placeholder for class (uses Struct internally)
                    self.module.types.register_named(
                        c.name.clone(),
                        HirType::Struct {
                            name: c.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: c.generic_params.clone(),
                            is_generic_template: c.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Enum(e) => {
                    // Register placeholder enum so it can be referenced by other types
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants: vec![],
                            generic_params: e.generic_params.clone(),
                            is_generic_template: e.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Actor(a) => {
                    // Register placeholder for actor (uses Struct internally, like class)
                    self.module.types.register_named(
                        a.name.clone(),
                        HirType::Struct {
                            name: a.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: vec![],
                            is_generic_template: false,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                _ => {}
            }
        }

        // Pass 0.5a: Pre-register type NAMES from ALL imported modules as empty placeholders.
        // This is the first half of a two-pass import loading strategy that fixes
        // cross-module type ordering bugs. For example, if dom.spl defines
        // `BeDomNode { style: StyleProps }` and StyleProps is in css.spl,
        // pre-registering ensures StyleProps exists when BeDomNode's fields
        // are resolved in Pass 0.5b.
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let _ = self.preregister_imported_type_names(&use_stmt.path, &use_stmt.target);
            }
        }

        // Pass 0.5b: Load full types from imported modules BEFORE declaration registration.
        // Now that all type names are pre-registered (Pass 0.5a), field type resolution
        // can find types from other imported modules.
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                // Log import loading failures -- silent failures cause cross-module
                // FieldGet bugs (wrong byte_offset when type falls back to ANY).
                if let Err(e) = self.load_imported_types(&use_stmt.path, &use_stmt.target) {
                    if std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_some() {
                        continue;
                    }
                    eprintln!(
                        "[WARN] Failed to load imported types from {:?}: {}",
                        use_stmt.path.segments, e
                    );
                }
            }
        }

        // Pass 0.5c: upgrade imported return types that resolved to ANY before
        // their home module was loaded (now that all imports are registered).
        self.populate_global_fn_return_types();

        // First pass: collect type and function declarations (with full field resolution)
        for item in &ast_module.items {
            self.register_declarations_from_node(item)?;
        }

        // Continue with rest of lowering...
        for item in &ast_module.items {
            match item {
                // These were already registered in first pass
                Node::Struct(_)
                | Node::Function(_)
                | Node::Class(_)
                | Node::Enum(_)
                | Node::Mixin(_)
                | Node::TypeAlias(_)
                | Node::Trait(_)
                | Node::Actor(_) => {}
                Node::Bitfield(bf) => {
                    let bitfield_type_id = self.register_bitfield(bf)?;
                    self.globals.insert(bf.name.clone(), bitfield_type_id);
                    self.local_globals.insert(bf.name.clone());
                }
                // Other node types
                Node::Impl(_)
                | Node::Extern(_)
                | Node::ExternClass(_)
                | Node::Macro(_)
                | Node::Unit(_)
                | Node::UnitFamily(_)
                | Node::InterfaceBinding(_) => {}
                Node::Let(_)
                | Node::Const(_)
                | Node::Static(_)
                | Node::Assignment(_)
                | Node::Return(_)
                | Node::If(_)
                | Node::Match(_)
                | Node::For(_)
                | Node::While(_)
                | Node::Loop(_)
                | Node::Break(_)
                | Node::Continue(_)
                | Node::Assert(_)
                | Node::Assume(_)
                | Node::Admit(_)
                | Node::ProofHint(_)
                | Node::Calc(_)
                | Node::Context(_)
                | Node::With(_)
                | Node::Expression(_) => {}
                Node::ModDecl(_)
                | Node::UseStmt(_)
                | Node::MultiUse(_)
                | Node::CommonUseStmt(_)
                | Node::ExportUseStmt(_)
                | Node::StructuredExportStmt(_)
                | Node::AutoImportStmt(_)
                | Node::RequiresCapabilities(_)
                | Node::CompoundUnit(_)
                | Node::HandlePool(_)
                | Node::AopAdvice(_)
                | Node::DiBinding(_)
                | Node::InjectGraph(_)
                | Node::SecurityPolicy(_)
                | Node::SecurityGate(_)
                | Node::SandboxPolicy(_)
                | Node::CapabilityPolicy(_)
                | Node::UiPolicy(_)
                | Node::ArchitectureRule(_)
                | Node::MockDecl(_)
                | Node::LiteralFunction(_)
                | Node::LeanBlock(_)
                | Node::ClassAlias(_)
                | Node::FunctionAlias(_)
                | Node::Pass(_)
                | Node::Skip(_)
                | Node::Guard(_)
                | Node::Defer(_)
                | Node::ErrDefer(_)
                | Node::InlineAsm(_)
                | Node::Newtype(_)
                | Node::Extend(_)
                | Node::DomainBlock(_) => {}
            }
        }

        // Pre-register method return types (before lowering bodies)
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let ret_ty = self.resolve_type_opt(&f.return_type).unwrap_or(TypeId::ANY);
                    self.method_return_types.insert(f.name.clone(), ret_ty);
                }
                Node::Class(c) => {
                    for method in &c.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", c.name, method.name);
                        self.method_return_types.insert(qualified, ret_ty);
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", s.name, method.name);
                        self.method_return_types.insert(qualified, ret_ty);
                    }
                }
                Node::Actor(a) => {
                    for method in &a.methods {
                        let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                        let qualified = format!("{}.{}", a.name, method.name);
                        self.method_return_types.insert(qualified, ret_ty);
                    }
                }
                Node::Impl(impl_block) => {
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };
                    if let Some(type_name) = type_name {
                        let impl_method_names: std::collections::HashSet<&str> =
                            impl_block.methods.iter().map(|m| m.name.as_str()).collect();
                        for method in &impl_block.methods {
                            let ret_ty = self.resolve_type_opt(&method.return_type).unwrap_or(TypeId::ANY);
                            let qualified = format!("{}.{}", type_name, method.name);
                            self.method_return_types.insert(qualified, ret_ty);
                        }

                        // Also register return types for inherited (non-overridden)
                        // trait default methods, so calls to them resolve their real
                        // return type instead of falling back to ANY.
                        if let Some(ref trait_name) = impl_block.trait_name {
                            if let Some(trait_def) = ast_module.items.iter().find_map(|item| {
                                if let Node::Trait(t) = item {
                                    if &t.name == trait_name {
                                        Some(t)
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }) {
                                for default_method in &trait_def.methods {
                                    if default_method.is_abstract
                                        || impl_method_names.contains(default_method.name.as_str())
                                    {
                                        continue;
                                    }
                                    let ret_ty = self
                                        .resolve_type_opt(&default_method.return_type)
                                        .unwrap_or(TypeId::ANY);
                                    let qualified = format!("{}.{}", type_name, default_method.name);
                                    self.method_return_types.insert(qualified, ret_ty);
                                }
                            }
                        }
                    }
                }
                _ => {}
            }
        }

        // Second pass: lower function bodies and class/struct methods
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let hir_func = self.lower_function(f, None)?;
                    self.module.functions.push(hir_func);
                }
                Node::Class(c) => {
                    // Lower class methods with type invariant injection
                    for method in &c.methods {
                        let hir_func = self.lower_function(method, Some(&c.name))?;
                        self.module.functions.push(hir_func);
                    }

                    // Lower mixin methods applied to this class
                    for mixin_ref in &c.mixins {
                        if let Some(mixin_decl) = ast_module.items.iter().find_map(|item| {
                            if let Node::Mixin(m) = item {
                                if m.name == mixin_ref.name {
                                    Some(m)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }) {
                            // Lower mixin methods for this class
                            for method in &mixin_decl.methods {
                                let hir_func = self.lower_function(method, Some(&c.name))?;
                                self.module.functions.push(hir_func);
                            }
                        }
                    }
                }
                Node::Struct(s) => {
                    // Lower struct methods with type invariant injection
                    for method in &s.methods {
                        let hir_func = self.lower_function(method, Some(&s.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Enum(e) => {
                    for method in &e.methods {
                        let hir_func = self.lower_function(method, Some(&e.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Actor(a) => {
                    // Lower actor methods (actors are lowered like classes)
                    for method in &a.methods {
                        let hir_func = self.lower_function(method, Some(&a.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Impl(impl_block) => {
                    // Lower impl block methods
                    // Extract the type name from the impl block's target
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(ref type_name) = type_name {
                        for method in &impl_block.methods {
                            let method = method_with_impl_driver_attrs(method, &impl_block.attributes);
                            let hir_func = self.lower_function(&method, Some(type_name))?;
                            self.module.functions.push(hir_func);
                        }

                        // Record trait impl metadata for vtable emission
                        if let Some(ref trait_name) = impl_block.trait_name {
                            let type_id = self
                                .resolve_type(&simple_parser::ast::Type::Simple(type_name.clone()))
                                .unwrap_or(TypeId::ANY);
                            let mut methods_map = HashMap::new();
                            let impl_method_names: std::collections::HashSet<&str> =
                                impl_block.methods.iter().map(|m| m.name.as_str()).collect();
                            for method in &impl_block.methods {
                                let fn_name = format!("{}.{}", type_name, method.name);
                                methods_map.insert(method.name.clone(), fn_name);
                            }

                            // Merge in trait default method bodies for methods the impl
                            // doesn't override. Without this, the vtable slot list built
                            // from `methods_map` silently omits the default method and the
                            // per-slot function-pointer array ends up short, so calling the
                            // inherited default through a vtable slot reads out-of-bounds
                            // memory as a function pointer (crash) instead of dispatching to
                            // the default body. Each default is lowered fresh per-impl so
                            // `self` resolves against this impl's concrete type.
                            if let Some(trait_def) = ast_module.items.iter().find_map(|item| {
                                if let Node::Trait(t) = item {
                                    if &t.name == trait_name {
                                        Some(t)
                                    } else {
                                        None
                                    }
                                } else {
                                    None
                                }
                            }) {
                                for default_method in &trait_def.methods {
                                    if default_method.is_abstract
                                        || impl_method_names.contains(default_method.name.as_str())
                                    {
                                        continue;
                                    }
                                    let default_method =
                                        method_with_impl_driver_attrs(default_method, &impl_block.attributes);
                                    let hir_func = self.lower_function(&default_method, Some(type_name))?;
                                    self.module.functions.push(hir_func);

                                    let fn_name = format!("{}.{}", type_name, default_method.name);
                                    methods_map.insert(default_method.name.clone(), fn_name);
                                }
                            }

                            self.module.impls.push(crate::hir::HirImpl {
                                type_id,
                                trait_id: None, // trait TypeId resolution deferred
                                trait_name: impl_block.trait_name.clone(),
                                type_name: type_name.clone(),
                                methods: methods_map,
                            });
                        }
                    }
                }
                _ => {}
            }
        }

        // Copy global variables from HashMap to module's globals Vec.
        // Sort by name for deterministic output regardless of HashMap iteration order.
        let mut sorted_globals: Vec<_> = self.globals.iter().collect();
        sorted_globals.sort_by_key(|(name, _)| *name);
        for (name, ty) in sorted_globals {
            self.module.globals.push((name.clone(), *ty));
        }

        // Copy compile-time constant init values to HirModule for codegen
        self.module.global_init_values = self.global_init_values.clone();
        self.module.global_init_strings = self.global_init_strings.clone();
        self.module.global_init_arrays = self.global_init_arrays.clone();
        self.module.global_init_functions = self.global_init_functions.clone();
        self.module.global_init_structs = self.global_init_structs.clone();

        // Copy local globals set to HirModule for codegen linkage decisions
        self.module.local_globals = self.local_globals.clone();
        self.module.immutable_globals = self.immutable_globals.clone();

        // Copy extern function names to HirModule for codegen
        self.module.extern_fn_names = self.extern_fn_names.clone();
        self.module.imported_function_names = self.imported_function_names.clone();

        // Third pass: lower AOP constructs (#1000-1050)
        self.lower_aop_constructs(ast_module)?;

        // New pass: collect Lean 4 blocks for verification
        self.lower_lean_blocks(ast_module);

        // New pass: collect raw top-level domain blocks for future semantic passes
        self.lower_domain_blocks(ast_module);

        // Fourth pass: lower import statements for dependency tracking AND load types
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let import = self.lower_import(
                    &use_stmt.path,
                    &use_stmt.target,
                    use_stmt.is_type_only,
                    use_stmt.is_lazy,
                );
                self.module.imports.push(import);

                // NEW: Load types from imported module into globals symbol table
                // This enables compile-time type checking for imports
                // Errors are silently ignored for backward compatibility
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        // Fifth pass: validate sync→async calls (async validation design decision #3)
        self.validate_sync_async_calls()?;

        // Sixth pass: apply Promise auto-wrapping for async functions (design decision #2)
        let mut type_checker = crate::type_check::TypeChecker::new();
        type_checker.apply_promise_wrapping(&mut self.module)?;

        // Seventh pass: check for lifetime violations (E2001-E2006)
        if self.lifetime_context.has_violations() {
            let violations = self.lifetime_context.violations().to_vec();
            if violations.len() == 1 {
                return Err(LowerError::LifetimeViolation(violations.into_iter().next().unwrap()));
            } else {
                return Err(LowerError::LifetimeViolations(violations));
            }
        }

        // Eighth pass: in strict mode (Rust-level safety), memory warnings become errors
        if self.memory_warnings.is_strict() && self.memory_warnings.has_warnings() {
            let first_warning = self.memory_warnings.warnings().first().unwrap();
            return Err(LowerError::MemorySafetyViolation {
                code: first_warning.code,
                message: format!(
                    "{}{}{} at {}:{}",
                    first_warning.code.description(),
                    first_warning
                        .name
                        .as_ref()
                        .map(|n| format!(" ({})", n))
                        .unwrap_or_default(),
                    first_warning
                        .context
                        .as_ref()
                        .map(|c| format!(": {}", c))
                        .unwrap_or_default(),
                    first_warning.span.line,
                    first_warning.span.column
                ),
                span: first_warning.span,
                all_warnings: std::mem::take(&mut self.memory_warnings),
            });
        }

        Ok(self.module)
    }

    /// Lower an AST module to HIR and return warnings along with the module
    pub fn lower_module_with_warnings(mut self, ast_module: &Module) -> LowerResult<super::super::LoweringOutput> {
        // Hoist nested type definitions to module scope (see `lower_module`).
        let hoisted = super::nested_def_hoist::module_with_hoisted_defs(ast_module);
        let ast_module: &Module = hoisted.as_ref().unwrap_or(ast_module);

        // Perform all lowering passes
        self.module.name = ast_module.name.clone();
        self.collect_fn_param_defaults(ast_module);

        // Pass 0: Pre-register all struct/class/enum names to allow self-referential types
        for item in &ast_module.items {
            match item {
                Node::Struct(s) => {
                    self.module.types.register_named(
                        s.name.clone(),
                        HirType::Struct {
                            name: s.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: s.generic_params.clone(),
                            is_generic_template: s.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Class(c) => {
                    self.module.types.register_named(
                        c.name.clone(),
                        HirType::Struct {
                            name: c.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: c.generic_params.clone(),
                            is_generic_template: c.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Enum(e) => {
                    self.module.types.register_named(
                        e.name.clone(),
                        HirType::Enum {
                            name: e.name.clone(),
                            variants: vec![],
                            generic_params: e.generic_params.clone(),
                            is_generic_template: e.is_generic_template,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                Node::Actor(a) => {
                    self.module.types.register_named(
                        a.name.clone(),
                        HirType::Struct {
                            name: a.name.clone(),
                            fields: vec![],
                            has_snapshot: false,
                            generic_params: vec![],
                            is_generic_template: false,
                            type_bindings: std::collections::HashMap::new(),
                        },
                    );
                }
                _ => {}
            }
        }

        // Pass 0.5a: Pre-register type NAMES from ALL imported modules as empty placeholders
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let _ = self.preregister_imported_type_names(&use_stmt.path, &use_stmt.target);
            }
        }

        // Pass 0.5b: Load full types from imported modules
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                if let Err(e) = self.load_imported_types(&use_stmt.path, &use_stmt.target) {
                    if std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_some() {
                        continue;
                    }
                    eprintln!(
                        "[WARN] Failed to load imported types from {:?}: {}",
                        use_stmt.path.segments, e
                    );
                }
            }
        }

        // Pass 0.5c: upgrade imported return types that resolved to ANY before
        // their home module was loaded (now that all imports are registered).
        self.populate_global_fn_return_types();

        // First pass: collect type and function declarations
        for item in &ast_module.items {
            self.register_declarations_from_node(item)?;
        }

        // Second pass: lower function bodies
        for item in &ast_module.items {
            match item {
                Node::Function(f) => {
                    let hir_func = self.lower_function(f, None)?;
                    self.module.functions.push(hir_func);
                }
                Node::Class(c) => {
                    for method in &c.methods {
                        let hir_func = self.lower_function(method, Some(&c.name))?;
                        self.module.functions.push(hir_func);
                    }
                    for mixin_ref in &c.mixins {
                        if let Some(mixin_decl) = ast_module.items.iter().find_map(|item| {
                            if let Node::Mixin(m) = item {
                                if m.name == mixin_ref.name {
                                    Some(m)
                                } else {
                                    None
                                }
                            } else {
                                None
                            }
                        }) {
                            for method in &mixin_decl.methods {
                                let hir_func = self.lower_function(method, Some(&c.name))?;
                                self.module.functions.push(hir_func);
                            }
                        }
                    }
                }
                Node::Struct(s) => {
                    for method in &s.methods {
                        let hir_func = self.lower_function(method, Some(&s.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Enum(e) => {
                    for method in &e.methods {
                        let hir_func = self.lower_function(method, Some(&e.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Actor(a) => {
                    // Lower actor methods (actors are lowered like classes)
                    for method in &a.methods {
                        let hir_func = self.lower_function(method, Some(&a.name))?;
                        self.module.functions.push(hir_func);
                    }
                }
                Node::Impl(impl_block) => {
                    // Lower impl block methods (second pass)
                    let type_name = match &impl_block.target_type {
                        simple_parser::ast::Type::Simple(name) => Some(name.clone()),
                        simple_parser::ast::Type::Generic { name, .. } => Some(name.clone()),
                        _ => None,
                    };

                    if let Some(type_name) = type_name {
                        for method in &impl_block.methods {
                            let method = method_with_impl_driver_attrs(method, &impl_block.attributes);
                            let hir_func = self.lower_function(&method, Some(&type_name))?;
                            self.module.functions.push(hir_func);
                        }
                    }
                }
                _ => {}
            }
        }

        // Third pass: lower AOP constructs
        self.lower_aop_constructs(ast_module)?;

        // Lean pass: collect Lean 4 blocks for verification
        self.lower_lean_blocks(ast_module);

        // Domain pass: collect raw top-level domain blocks for future semantic passes
        self.lower_domain_blocks(ast_module);

        // Fourth pass: lower imports
        for item in &ast_module.items {
            if let Node::UseStmt(use_stmt) = item {
                let import = self.lower_import(
                    &use_stmt.path,
                    &use_stmt.target,
                    use_stmt.is_type_only,
                    use_stmt.is_lazy,
                );
                self.module.imports.push(import);
                let _ = self.load_imported_types(&use_stmt.path, &use_stmt.target);
            }
        }

        // Fifth pass: validate sync→async calls
        self.validate_sync_async_calls()?;

        // Sixth pass: apply Promise auto-wrapping
        let mut type_checker = crate::type_check::TypeChecker::new();
        type_checker.apply_promise_wrapping(&mut self.module)?;

        // Seventh pass: capture lifetime information for Lean 4 verification
        let lifetime_lean4 = self.lifetime_context.generate_lean4();
        let lifetime_violations = self.lifetime_context.violations().to_vec();

        // Check for lifetime violations (E2001-E2006)
        if !lifetime_violations.is_empty() {
            // Return error with lifetime violations
            if lifetime_violations.len() == 1 {
                return Err(LowerError::LifetimeViolation(
                    lifetime_violations.into_iter().next().unwrap(),
                ));
            } else {
                return Err(LowerError::LifetimeViolations(lifetime_violations));
            }
        }

        // Copy globals and init values to HirModule
        let mut sorted_globals: Vec<_> = self.globals.iter().collect();
        sorted_globals.sort_by_key(|(name, _)| *name);
        for (name, ty) in sorted_globals {
            self.module.globals.push((name.clone(), *ty));
        }
        self.module.global_init_values = self.global_init_values.clone();
        self.module.global_init_strings = self.global_init_strings.clone();
        self.module.global_init_arrays = self.global_init_arrays.clone();
        self.module.global_init_functions = self.global_init_functions.clone();
        self.module.global_init_structs = self.global_init_structs.clone();

        // Copy local globals set to HirModule for codegen linkage decisions
        self.module.local_globals = self.local_globals.clone();
        self.module.immutable_globals = self.immutable_globals.clone();

        // Copy extern function names to HirModule for codegen
        self.module.extern_fn_names = self.extern_fn_names.clone();
        self.module.imported_function_names = self.imported_function_names.clone();

        // Take warnings before consuming self
        let warnings = std::mem::take(&mut self.memory_warnings);
        let module = self.module;

        // CRITICAL: In strict mode (Rust-level safety), memory warnings become errors
        if warnings.is_strict() && warnings.has_warnings() {
            // Convert most severe warning to error
            let first_warning = warnings.warnings().first().unwrap();
            return Err(LowerError::MemorySafetyViolation {
                code: first_warning.code,
                message: format!(
                    "{}{}{} at {}:{}",
                    first_warning.code.description(),
                    first_warning
                        .name
                        .as_ref()
                        .map(|n| format!(" ({})", n))
                        .unwrap_or_default(),
                    first_warning
                        .context
                        .as_ref()
                        .map(|c| format!(": {}", c))
                        .unwrap_or_default(),
                    first_warning.span.line,
                    first_warning.span.column
                ),
                span: first_warning.span,
                all_warnings: warnings,
            });
        }

        Ok(super::super::LoweringOutput::with_lifetime(
            module,
            warnings,
            lifetime_lean4,
            lifetime_violations,
        ))
    }
}

/// Extract the variable name from a pattern, handling Pattern::Typed wrapper.
fn extract_pattern_name(pattern: &simple_parser::Pattern) -> Option<String> {
    use simple_parser::Pattern;
    match pattern {
        Pattern::Identifier(n) => Some(n.clone()),
        Pattern::MutIdentifier(n) => Some(n.clone()),
        Pattern::Typed { pattern: inner, .. } => extract_pattern_name(inner),
        _ => None,
    }
}

/// Extract the type annotation from a Pattern::Typed wrapper, if present.
/// The parser stores `var name: Type = value` as Pattern::Typed { ty, .. }
/// with LetStmt.ty = None, so this function retrieves the type from the pattern.
fn extract_pattern_type(pattern: &simple_parser::Pattern) -> Option<simple_parser::ast::Type> {
    use simple_parser::Pattern;
    match pattern {
        Pattern::Typed { ty, .. } => Some(ty.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod scalar_const_eval_tests {
    use super::*;

    #[test]
    fn nil_global_scalar_uses_tagged_nil_sentinel() {
        assert_eq!(try_const_eval(&Expr::Nil), Some(3));
    }
}
