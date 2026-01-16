//! Literal expression lowering
//!
//! This module contains expression lowering logic for literal values
//! (integers, floats, strings, booleans, nil) and formatted strings.

use simple_parser::{self as ast, Expr};

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
    /// Currently lowered as a plain string literal (no locale lookup at HIR level).
    /// Locale lookup happens at runtime.
    pub(super) fn lower_i18n_string(&self, _name: &str, default_text: &str) -> LowerResult<HirExpr> {
        // For now, just emit the default text as a string literal
        // TODO: Add locale lookup support in native compilation
        Ok(HirExpr {
            kind: HirExprKind::String(default_text.to_string()),
            ty: TypeId::STRING,
        })
    }

    /// Lower an i18n template to HIR
    ///
    /// Not yet supported in native compilation - falls back to interpreter.
    pub(super) fn lower_i18n_template(&self, _name: &str, _parts: &[ast::FStringPart], _args: &[(String, Expr)]) -> LowerResult<HirExpr> {
        Err(LowerError::Unsupported(
            "i18n template strings not yet supported in native compilation".to_string(),
        ))
    }

    /// Lower an i18n reference to HIR
    ///
    /// Not yet supported in native compilation - falls back to interpreter.
    pub(super) fn lower_i18n_ref(&self, _name: &str) -> LowerResult<HirExpr> {
        Err(LowerError::Unsupported(
            "i18n references not yet supported in native compilation".to_string(),
        ))
    }

    /// Lower an FString (formatted string) to HIR
    ///
    /// Currently only supports FStrings without interpolation (plain literals).
    /// FStrings with interpolation expressions are not yet supported in native compilation.
    pub(super) fn lower_fstring(&self, parts: &[ast::FStringPart]) -> LowerResult<HirExpr> {
        // Check if the FString is a simple literal (no interpolation)
        // If so, convert it to a plain string
        let mut result = String::new();
        let mut all_literal = true;
        for part in parts {
            match part {
                ast::FStringPart::Literal(s) => {
                    result.push_str(s);
                }
                ast::FStringPart::Expr(_) => {
                    all_literal = false;
                    break;
                }
            }
        }
        if all_literal {
            Ok(HirExpr {
                kind: HirExprKind::String(result),
                ty: TypeId::STRING,
            })
        } else {
            Err(LowerError::Unsupported(
                "FString with interpolation not yet supported in native compilation".to_string(),
            ))
        }
    }
}
