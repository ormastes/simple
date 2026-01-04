//! Macro registry for LL(1) parser integration.
//!
//! This module provides compile-time macro registration and symbol tracking,
//! enabling the parser to immediately register introduced symbols when
//! encountering macro invocations.

use std::collections::HashMap;

use crate::ast::{
    BinOp, Expr, MacroContractItem, MacroDef, MacroIntro, MacroIntroDecl, MacroIntroSpec, Type,
    UnaryOp,
};

/// A symbol introduced by a macro (function, field, type, or variable).
#[derive(Debug, Clone, PartialEq)]
pub enum IntroducedSymbol {
    /// A function introduced by a macro
    Function {
        name: String,
        params: Vec<(String, Type)>,
        return_type: Option<Type>,
        source_macro: String,
    },
    /// A field introduced by a macro
    Field {
        name: String,
        ty: Type,
        source_macro: String,
    },
    /// A type alias introduced by a macro
    TypeAlias {
        name: String,
        source_macro: String,
    },
    /// A variable (let/const) introduced by a macro
    Variable {
        name: String,
        ty: Type,
        is_const: bool,
        source_macro: String,
    },
}

impl IntroducedSymbol {
    /// Get the name of the introduced symbol
    pub fn name(&self) -> &str {
        match self {
            IntroducedSymbol::Function { name, .. } => name,
            IntroducedSymbol::Field { name, .. } => name,
            IntroducedSymbol::TypeAlias { name, .. } => name,
            IntroducedSymbol::Variable { name, .. } => name,
        }
    }

    /// Get the source macro name
    pub fn source_macro(&self) -> &str {
        match self {
            IntroducedSymbol::Function { source_macro, .. } => source_macro,
            IntroducedSymbol::Field { source_macro, .. } => source_macro,
            IntroducedSymbol::TypeAlias { source_macro, .. } => source_macro,
            IntroducedSymbol::Variable { source_macro, .. } => source_macro,
        }
    }
}

/// Injection point registered by a macro.
#[derive(Debug, Clone, PartialEq)]
pub struct InjectionPoint {
    /// The macro that registered this injection
    pub source_macro: String,
    /// The label for this injection
    pub label: String,
    /// Where to inject: head, tail, or here
    pub anchor: InjectionAnchor,
    /// Whether to inject a single statement or a block
    pub code_kind: InjectionCodeKind,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InjectionAnchor {
    Head,
    Tail,
    Here,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum InjectionCodeKind {
    Stmt,
    Block,
}

/// Const evaluation context for macro contract processing.
#[derive(Debug, Clone, Default)]
pub struct ConstEvalContext {
    /// Const bindings from macro arguments and loop indices
    pub bindings: HashMap<String, ConstValue>,
}

/// A compile-time constant value.
#[derive(Debug, Clone, PartialEq)]
pub enum ConstValue {
    Int(i64),
    Str(String),
    Bool(bool),
}

impl ConstValue {
    /// Try to convert to i64
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            ConstValue::Int(n) => Some(*n),
            _ => None,
        }
    }

    /// Try to convert to string
    pub fn as_str(&self) -> Option<&str> {
        match self {
            ConstValue::Str(s) => Some(s),
            _ => None,
        }
    }
}

/// Registry for macro definitions and introduced symbols.
///
/// This is used by the parser to implement LL(1) macro integration:
/// - When a macro is defined, it's registered here
/// - When a macro is invoked, its contract is processed to register symbols
/// - The introduced symbols are available for name resolution and IDE completion
#[derive(Debug, Clone, Default)]
pub struct MacroRegistry {
    /// Defined macros (name → definition)
    macros: HashMap<String, MacroDef>,

    /// Symbols introduced by macros, organized by scope
    /// Key is a scope identifier (e.g., "module", "class:ClassName")
    introduced_symbols: HashMap<String, Vec<IntroducedSymbol>>,

    /// Pending injection points for the current block
    pending_injections: Vec<InjectionPoint>,

    /// Whether LL(1) mode is enabled (process contracts at parse time)
    ll1_mode: bool,
}

impl MacroRegistry {
    /// Create a new empty macro registry
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a new macro registry with LL(1) mode enabled
    pub fn with_ll1_mode() -> Self {
        Self {
            ll1_mode: true,
            ..Self::default()
        }
    }

    /// Check if LL(1) mode is enabled
    pub fn is_ll1_mode(&self) -> bool {
        self.ll1_mode
    }

    /// Enable or disable LL(1) mode
    pub fn set_ll1_mode(&mut self, enabled: bool) {
        self.ll1_mode = enabled;
    }

    /// Register a macro definition
    pub fn register_macro(&mut self, macro_def: MacroDef) {
        self.macros.insert(macro_def.name.clone(), macro_def);
    }

    /// Look up a macro by name
    pub fn get_macro(&self, name: &str) -> Option<&MacroDef> {
        self.macros.get(name)
    }

    /// Check if a macro exists
    pub fn has_macro(&self, name: &str) -> bool {
        self.macros.contains_key(name)
    }

    /// Get all registered macro names
    pub fn macro_names(&self) -> impl Iterator<Item = &str> {
        self.macros.keys().map(|s| s.as_str())
    }

    /// Process a macro invocation's contract to register introduced symbols.
    ///
    /// This is the core of LL(1) integration: when a macro is invoked,
    /// we evaluate its contract (using const arguments) and register
    /// the introduced symbols immediately.
    ///
    /// Returns the list of newly introduced symbols.
    pub fn process_macro_invocation(
        &mut self,
        macro_name: &str,
        const_args: &HashMap<String, ConstValue>,
        scope: &str,
    ) -> Result<Vec<IntroducedSymbol>, String> {
        let macro_def = self
            .macros
            .get(macro_name)
            .ok_or_else(|| format!("Macro '{}' not defined", macro_name))?
            .clone();

        let mut ctx = ConstEvalContext {
            bindings: const_args.clone(),
        };

        let mut introduced = Vec::new();

        // Process each contract item
        for item in &macro_def.contract {
            match item {
                MacroContractItem::Intro(intro) => {
                    self.process_intro_item(intro, &mut ctx, macro_name, &mut introduced)?;
                }
                MacroContractItem::Inject(inject) => {
                    // Register injection point
                    let anchor = match inject.spec.anchor {
                        crate::ast::MacroAnchor::Head => InjectionAnchor::Head,
                        crate::ast::MacroAnchor::Tail => InjectionAnchor::Tail,
                        crate::ast::MacroAnchor::Here => InjectionAnchor::Here,
                    };
                    let code_kind = match inject.spec.code_kind {
                        crate::ast::MacroCodeKind::Stmt => InjectionCodeKind::Stmt,
                        crate::ast::MacroCodeKind::Block => InjectionCodeKind::Block,
                    };
                    self.pending_injections.push(InjectionPoint {
                        source_macro: macro_name.to_string(),
                        label: inject.label.clone(),
                        anchor,
                        code_kind,
                    });
                }
                MacroContractItem::Returns(_) => {
                    // Returns items don't introduce symbols
                }
            }
        }

        // Store introduced symbols in the appropriate scope
        self.introduced_symbols
            .entry(scope.to_string())
            .or_default()
            .extend(introduced.clone());

        Ok(introduced)
    }

    /// Process an intro item from a macro contract
    fn process_intro_item(
        &self,
        intro: &MacroIntro,
        ctx: &mut ConstEvalContext,
        macro_name: &str,
        introduced: &mut Vec<IntroducedSymbol>,
    ) -> Result<(), String> {
        self.process_intro_spec(&intro.spec, ctx, macro_name, introduced)
    }

    /// Process an intro spec (may be a declaration, for loop, or if condition)
    fn process_intro_spec(
        &self,
        spec: &MacroIntroSpec,
        ctx: &mut ConstEvalContext,
        macro_name: &str,
        introduced: &mut Vec<IntroducedSymbol>,
    ) -> Result<(), String> {
        match spec {
            MacroIntroSpec::Decl(decl) => {
                self.process_intro_decl(decl, ctx, macro_name, introduced)?;
            }
            MacroIntroSpec::For { name, range, body } => {
                // Evaluate range bounds
                let start = self.eval_const_expr(&range.start, ctx)?;
                let end = self.eval_const_expr(&range.end, ctx)?;

                let start_val = start
                    .as_i64()
                    .ok_or("For loop start must be an integer")?;
                let end_val = end.as_i64().ok_or("For loop end must be an integer")?;

                // Unroll the loop
                let end_bound = if range.inclusive {
                    end_val + 1
                } else {
                    end_val
                };
                for i in start_val..end_bound {
                    // Bind loop variable
                    ctx.bindings.insert(name.clone(), ConstValue::Int(i));

                    // Process body
                    for body_spec in body {
                        self.process_intro_spec(body_spec, ctx, macro_name, introduced)?;
                    }
                }

                // Remove loop variable binding
                ctx.bindings.remove(name);
            }
            MacroIntroSpec::If {
                condition,
                then_body,
                else_body,
            } => {
                // Evaluate condition
                let cond_val = self.eval_const_expr(condition, ctx)?;
                let is_true = match cond_val {
                    ConstValue::Bool(b) => b,
                    ConstValue::Int(n) => n != 0,
                    ConstValue::Str(s) => !s.is_empty(),
                };

                let body = if is_true { then_body } else { else_body };
                for body_spec in body {
                    self.process_intro_spec(body_spec, ctx, macro_name, introduced)?;
                }
            }
        }
        Ok(())
    }

    /// Process an intro declaration to create an introduced symbol
    fn process_intro_decl(
        &self,
        decl: &MacroIntroDecl,
        ctx: &ConstEvalContext,
        macro_name: &str,
        introduced: &mut Vec<IntroducedSymbol>,
    ) -> Result<(), String> {
        use crate::ast::{MacroDeclStub, MacroIntroKind};

        match &decl.stub {
            MacroDeclStub::Fn(fn_stub) => {
                let name = self.substitute_templates(&fn_stub.name, ctx);
                let params: Vec<(String, Type)> = fn_stub
                    .params
                    .iter()
                    .map(|p| (p.name.clone(), p.ty.clone()))
                    .collect();
                introduced.push(IntroducedSymbol::Function {
                    name,
                    params,
                    return_type: fn_stub.ret.clone(),
                    source_macro: macro_name.to_string(),
                });
            }
            MacroDeclStub::Field(field_stub) => {
                let name = self.substitute_templates(&field_stub.name, ctx);
                introduced.push(IntroducedSymbol::Field {
                    name,
                    ty: field_stub.ty.clone(),
                    source_macro: macro_name.to_string(),
                });
            }
            MacroDeclStub::Type(type_stub) => {
                let name = self.substitute_templates(&type_stub.name, ctx);
                introduced.push(IntroducedSymbol::TypeAlias {
                    name,
                    source_macro: macro_name.to_string(),
                });
            }
            MacroDeclStub::Var(var_stub) => {
                let name = self.substitute_templates(&var_stub.name, ctx);
                let is_const = matches!(decl.kind, MacroIntroKind::Const);
                introduced.push(IntroducedSymbol::Variable {
                    name,
                    ty: var_stub.ty.clone(),
                    is_const,
                    source_macro: macro_name.to_string(),
                });
            }
        }
        Ok(())
    }

    /// Substitute template placeholders in a string with const values
    pub fn substitute_templates(&self, template: &str, ctx: &ConstEvalContext) -> String {
        let mut result = template.to_string();

        // Strip surrounding quotes if present
        if (result.starts_with('"') && result.ends_with('"'))
            || (result.starts_with('\'') && result.ends_with('\''))
        {
            result = result[1..result.len() - 1].to_string();
        }

        // Substitute {name} patterns
        for (name, value) in &ctx.bindings {
            let pattern = format!("{{{}}}", name);
            let replacement = match value {
                ConstValue::Int(n) => n.to_string(),
                ConstValue::Str(s) => s.clone(),
                ConstValue::Bool(b) => b.to_string(),
            };
            result = result.replace(&pattern, &replacement);
        }

        result
    }

    /// Evaluate a const expression to a ConstValue
    fn eval_const_expr(&self, expr: &Expr, ctx: &ConstEvalContext) -> Result<ConstValue, String> {
        match expr {
            Expr::Integer(n) => Ok(ConstValue::Int(*n)),
            Expr::String(s) => Ok(ConstValue::Str(s.clone())),
            Expr::Bool(b) => Ok(ConstValue::Bool(*b)),
            Expr::Identifier(name) => ctx
                .bindings
                .get(name)
                .cloned()
                .ok_or_else(|| format!("Unknown const binding: {}", name)),
            Expr::Binary { left, op, right } => {
                let l = self.eval_const_expr(left, ctx)?;
                let r = self.eval_const_expr(right, ctx)?;
                self.eval_binary_op(&l, op, &r)
            }
            Expr::Unary { op, operand } => {
                let v = self.eval_const_expr(operand, ctx)?;
                self.eval_unary_op(op, &v)
            }
            _ => Err(format!("Cannot evaluate expression as const: {:?}", expr)),
        }
    }

    /// Evaluate a binary operation on const values
    fn eval_binary_op(
        &self,
        left: &ConstValue,
        op: &BinOp,
        right: &ConstValue,
    ) -> Result<ConstValue, String> {
        match (left, right) {
            (ConstValue::Int(l), ConstValue::Int(r)) => match op {
                BinOp::Add => Ok(ConstValue::Int(l + r)),
                BinOp::Sub => Ok(ConstValue::Int(l - r)),
                BinOp::Mul => Ok(ConstValue::Int(l * r)),
                BinOp::Div => {
                    if *r == 0 {
                        Err("Division by zero".to_string())
                    } else {
                        Ok(ConstValue::Int(l / r))
                    }
                }
                BinOp::Mod => {
                    if *r == 0 {
                        Err("Modulo by zero".to_string())
                    } else {
                        Ok(ConstValue::Int(l % r))
                    }
                }
                BinOp::Eq => Ok(ConstValue::Bool(l == r)),
                BinOp::NotEq => Ok(ConstValue::Bool(l != r)),
                BinOp::Lt => Ok(ConstValue::Bool(l < r)),
                BinOp::LtEq => Ok(ConstValue::Bool(l <= r)),
                BinOp::Gt => Ok(ConstValue::Bool(l > r)),
                BinOp::GtEq => Ok(ConstValue::Bool(l >= r)),
                _ => Err(format!("Unsupported binary operator for integers: {:?}", op)),
            },
            (ConstValue::Str(l), ConstValue::Str(r)) => match op {
                BinOp::Add => Ok(ConstValue::Str(format!("{}{}", l, r))),
                BinOp::Eq => Ok(ConstValue::Bool(l == r)),
                BinOp::NotEq => Ok(ConstValue::Bool(l != r)),
                _ => Err(format!("Unsupported binary operator for strings: {:?}", op)),
            },
            (ConstValue::Bool(l), ConstValue::Bool(r)) => match op {
                BinOp::And => Ok(ConstValue::Bool(*l && *r)),
                BinOp::Or => Ok(ConstValue::Bool(*l || *r)),
                BinOp::Eq => Ok(ConstValue::Bool(l == r)),
                BinOp::NotEq => Ok(ConstValue::Bool(l != r)),
                _ => Err(format!("Unsupported binary operator for booleans: {:?}", op)),
            },
            _ => Err(format!(
                "Type mismatch in binary operation: {:?} {:?} {:?}",
                left, op, right
            )),
        }
    }

    /// Evaluate a unary operation on a const value
    fn eval_unary_op(&self, op: &UnaryOp, value: &ConstValue) -> Result<ConstValue, String> {
        match (op, value) {
            (UnaryOp::Neg, ConstValue::Int(n)) => Ok(ConstValue::Int(-n)),
            (UnaryOp::Not, ConstValue::Bool(b)) => Ok(ConstValue::Bool(!b)),
            _ => Err(format!(
                "Unsupported unary operator {:?} for value {:?}",
                op, value
            )),
        }
    }

    /// Get introduced symbols for a scope
    pub fn get_introduced_symbols(&self, scope: &str) -> &[IntroducedSymbol] {
        self.introduced_symbols
            .get(scope)
            .map(|v| v.as_slice())
            .unwrap_or(&[])
    }

    /// Get all introduced symbols across all scopes
    pub fn all_introduced_symbols(&self) -> impl Iterator<Item = &IntroducedSymbol> {
        self.introduced_symbols.values().flatten()
    }

    /// Get pending injection points and clear them
    pub fn take_pending_injections(&mut self) -> Vec<InjectionPoint> {
        std::mem::take(&mut self.pending_injections)
    }

    /// Get pending injection points without clearing
    pub fn pending_injections(&self) -> &[InjectionPoint] {
        &self.pending_injections
    }

    /// Clear all introduced symbols (e.g., when leaving a scope)
    pub fn clear_scope(&mut self, scope: &str) {
        self.introduced_symbols.remove(scope);
    }

    /// Clear all state
    pub fn clear(&mut self) {
        self.macros.clear();
        self.introduced_symbols.clear();
        self.pending_injections.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_const_eval_integer() {
        let registry = MacroRegistry::new();
        let ctx = ConstEvalContext::default();

        let result = registry.eval_const_expr(&Expr::Integer(42), &ctx);
        assert_eq!(result, Ok(ConstValue::Int(42)));
    }

    #[test]
    fn test_const_eval_string() {
        let registry = MacroRegistry::new();
        let ctx = ConstEvalContext::default();

        let result = registry.eval_const_expr(&Expr::String("hello".to_string()), &ctx);
        assert_eq!(result, Ok(ConstValue::Str("hello".to_string())));
    }

    #[test]
    fn test_const_eval_binding() {
        let registry = MacroRegistry::new();
        let mut ctx = ConstEvalContext::default();
        ctx.bindings.insert("x".to_string(), ConstValue::Int(10));

        let result = registry.eval_const_expr(&Expr::Identifier("x".to_string()), &ctx);
        assert_eq!(result, Ok(ConstValue::Int(10)));
    }

    #[test]
    fn test_template_substitution() {
        let registry = MacroRegistry::new();
        let mut ctx = ConstEvalContext::default();
        ctx.bindings.insert("i".to_string(), ConstValue::Int(5));
        ctx.bindings
            .insert("name".to_string(), ConstValue::Str("foo".to_string()));

        let result = registry.substitute_templates("get_{name}_{i}", &ctx);
        assert_eq!(result, "get_foo_5");
    }

    #[test]
    fn test_template_with_quotes() {
        let registry = MacroRegistry::new();
        let mut ctx = ConstEvalContext::default();
        ctx.bindings.insert("i".to_string(), ConstValue::Int(0));

        let result = registry.substitute_templates("\"axis{i}\"", &ctx);
        assert_eq!(result, "axis0");
    }
}
