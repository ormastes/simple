//! Literal expression lowering
//!
//! This module contains expression lowering logic for literal values
//! (integers, floats, strings, booleans, nil) and formatted strings.

use simple_parser::{self as ast, Expr};

use crate::hir::lower::context::FunctionContext;
use crate::hir::lower::error::{LowerError, LowerResult};
use crate::hir::lower::lowerer::Lowerer;
use crate::hir::types::*;

impl Lowerer {
    /// Lower a literal expression to HIR
    ///
    /// Handles Integer, Float, String, Bool, and Nil literals.
    pub(super) fn lower_literal(&self, expr: &Expr) -> LowerResult<HirExpr> {
        match expr {
            Expr::Integer(n) => Ok(HirExpr {
                kind: HirExprKind::Integer(*n),
                ty: TypeId::I64,
            }),
            Expr::Float(f) => Ok(HirExpr {
                kind: HirExprKind::Float(*f),
                ty: TypeId::F64,
            }),
            Expr::String(s) => Ok(HirExpr {
                kind: HirExprKind::String(s.clone()),
                ty: TypeId::STRING,
            }),
            Expr::Bool(b) => Ok(HirExpr {
                kind: HirExprKind::Bool(*b),
                ty: TypeId::BOOL,
            }),
            Expr::Nil => Ok(HirExpr {
                kind: HirExprKind::Nil,
                ty: TypeId::NIL,
            }),
            _ => unreachable!("lower_literal called with non-literal"),
        }
    }

    /// Lower an i18n string to HIR
    ///
    /// Performs compile-time locale lookup using the registry. If the string
    /// is found in the current locale, that value is used; otherwise falls
    /// back to the default text.
    ///
    /// Note: This means the locale is baked in at compile time. For different
    /// locales, recompile with the appropriate locale loaded in the registry.
    pub(super) fn lower_i18n_string(&self, name: &str, default_text: &str) -> LowerResult<HirExpr> {
        // Look up in locale registry at compile time, fall back to default
        let text = crate::i18n::lookup(name).unwrap_or_else(|| default_text.to_string());
        Ok(HirExpr {
            kind: HirExprKind::String(text),
            ty: TypeId::STRING,
        })
    }

    /// Lower an i18n template to HIR
    ///
    /// Performs compile-time locale lookup. If found in registry, uses that template.
    /// Otherwise, builds the default template from parts.
    ///
    /// Note: Template arguments are not substituted at compile time in native
    /// compilation. For full template support, use the interpreter mode.
    pub(super) fn lower_i18n_template(
        &self,
        name: &str,
        parts: &[ast::FStringPart],
        _args: &[(String, Expr)],
    ) -> LowerResult<HirExpr> {
        // Try to look up the template in the locale registry
        let template = if let Some(localized) = crate::i18n::lookup(name) {
            localized
        } else {
            // Build the default template from parts
            let mut default_template = String::new();
            for part in parts {
                match part {
                    ast::FStringPart::Literal(lit) => default_template.push_str(lit),
                    ast::FStringPart::Expr(e) => {
                        // Convert expression to placeholder format
                        if let Expr::Identifier(id) = e {
                            default_template.push_str(&format!("{{{}}}", id));
                        } else {
                            // For complex expressions, just use a generic placeholder
                            default_template.push_str("{...}");
                        }
                    }
                }
            }
            default_template
        };

        // Return as a string literal (placeholders remain unsubstituted)
        // Full template substitution requires runtime support
        Ok(HirExpr {
            kind: HirExprKind::String(template),
            ty: TypeId::STRING,
        })
    }

    /// Lower an i18n reference to HIR
    ///
    /// Performs compile-time locale lookup using the registry.
    /// Returns the localized string or a placeholder if not found.
    pub(super) fn lower_i18n_ref(&self, name: &str) -> LowerResult<HirExpr> {
        // Look up in locale registry at compile time
        let text = crate::i18n::lookup_or_placeholder(name);
        Ok(HirExpr {
            kind: HirExprKind::String(text),
            ty: TypeId::STRING,
        })
    }

    /// Lower an FString (formatted string) to HIR
    ///
    /// Handles both plain string literals and strings with interpolation.
    /// For interpolation, generates calls to rt_value_to_string and rt_string_concat.
    ///
    /// The `type_meta` contains compile-time metadata including const_keys extracted
    /// from placeholders. This will be used for compile-time key validation in future.
    pub(super) fn lower_fstring(
        &mut self,
        parts: &[ast::FStringPart],
        _type_meta: &ast::TypeMeta,
        ctx: &mut FunctionContext,
    ) -> LowerResult<HirExpr> {
        // Check if the FString is a simple literal (no interpolation)
        // If so, convert it to a plain string
        let mut all_literal = true;
        for part in parts {
            if let ast::FStringPart::Expr(_) = part {
                all_literal = false;
                break;
            }
        }

        if all_literal {
            // Simple case: just concatenate all literal parts
            let mut result = String::new();
            for part in parts {
                if let ast::FStringPart::Literal(s) = part {
                    result.push_str(s);
                }
            }
            return Ok(HirExpr {
                kind: HirExprKind::String(result),
                ty: TypeId::STRING,
            });
        }

        // Complex case: interpolation needed
        // Build up the string by concatenating parts
        let mut string_parts: Vec<HirExpr> = Vec::new();

        for part in parts {
            match part {
                ast::FStringPart::Literal(s) => {
                    if !s.is_empty() {
                        string_parts.push(HirExpr {
                            kind: HirExprKind::String(s.clone()),
                            ty: TypeId::STRING,
                        });
                    }
                }
                ast::FStringPart::Expr(e) => {
                    // Lower the expression
                    let expr_hir = self.lower_expr(e, ctx)?;

                    // If it's already a string, use it directly; otherwise convert
                    let string_expr = if expr_hir.ty == TypeId::STRING
                        || matches!(self.module.types.get(expr_hir.ty), Some(HirType::String))
                    {
                        expr_hir
                    } else {
                        // Convert to string using rt_value_to_string
                        HirExpr {
                            kind: HirExprKind::BuiltinCall {
                                name: "rt_value_to_string".to_string(),
                                args: vec![expr_hir],
                            },
                            ty: TypeId::STRING,
                        }
                    };
                    string_parts.push(string_expr);
                }
            }
        }

        // If only one part, return it directly
        if string_parts.len() == 1 {
            return Ok(string_parts.into_iter().next().unwrap());
        }

        // If no parts, return empty string
        if string_parts.is_empty() {
            return Ok(HirExpr {
                kind: HirExprKind::String(String::new()),
                ty: TypeId::STRING,
            });
        }

        // Concatenate all parts using rt_string_concat
        // Build a chain: concat(concat(concat(a, b), c), d)
        let mut result = string_parts.into_iter();
        let first = result.next().unwrap();
        let concatenated = result.fold(first, |acc, part| HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_string_concat".to_string(),
                args: vec![acc, part],
            },
            ty: TypeId::STRING,
        });

        Ok(concatenated)
    }
}
