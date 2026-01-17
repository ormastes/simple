//! Lean expression translation.
//!
//! Translates Simple expressions to Lean 4 terms:
//! - Literals → Lean literals
//! - Binary ops → Lean operators
//! - Function calls → Lean application
//! - Match expressions → Lean match
//! - If expressions → Lean if-then-else

use super::types::{LeanType, TypeTranslator};
use crate::hir::{BinOp, HirExpr, HirExprKind, HirStmt, LocalVar, UnaryOp};
use crate::CompileError;

/// A Lean expression
#[derive(Debug, Clone)]
pub enum LeanExpr {
    /// Variable reference
    Var(String),
    /// Literal value
    Lit(LeanLit),
    /// Binary operation
    BinOp {
        op: String,
        left: Box<LeanExpr>,
        right: Box<LeanExpr>,
    },
    /// Unary operation
    UnaryOp { op: String, operand: Box<LeanExpr> },
    /// Function application
    App { func: Box<LeanExpr>, args: Vec<LeanExpr> },
    /// Lambda expression
    Lambda {
        params: Vec<(String, Option<LeanType>)>,
        body: Box<LeanExpr>,
    },
    /// Let binding
    Let {
        name: String,
        value: Box<LeanExpr>,
        body: Box<LeanExpr>,
    },
    /// If-then-else
    If {
        cond: Box<LeanExpr>,
        then_branch: Box<LeanExpr>,
        else_branch: Box<LeanExpr>,
    },
    /// Match expression
    Match {
        scrutinee: Box<LeanExpr>,
        arms: Vec<(String, Vec<String>, LeanExpr)>,
    },
    /// Field access
    Field { object: Box<LeanExpr>, field: String },
    /// Structure construction
    StructInit {
        type_name: String,
        fields: Vec<(String, LeanExpr)>,
    },
    /// Array/List literal
    List(Vec<LeanExpr>),
    /// Tuple
    Tuple(Vec<LeanExpr>),
    /// Do notation block
    Do(Vec<LeanDoStmt>),
    /// Sorry (proof stub)
    Sorry,
    /// Unit value
    Unit,
}

/// A Lean literal
#[derive(Debug, Clone)]
pub enum LeanLit {
    Int(i64),
    Nat(u64),
    Float(f64),
    Bool(bool),
    String(String),
    Char(char),
}

/// A statement in do notation
#[derive(Debug, Clone)]
pub enum LeanDoStmt {
    /// let x ← expr
    Bind { name: String, expr: LeanExpr },
    /// let x := expr
    Let { name: String, expr: LeanExpr },
    /// pure expr or return expr
    Return(LeanExpr),
    /// expr (for side effects)
    Expr(LeanExpr),
}

impl LeanExpr {
    /// Convert to Lean syntax string
    pub fn to_lean(&self) -> String {
        match self {
            LeanExpr::Var(name) => name.clone(),
            LeanExpr::Lit(lit) => lit.to_lean(),
            LeanExpr::BinOp { op, left, right } => {
                format!("({} {} {})", left.to_lean(), op, right.to_lean())
            }
            LeanExpr::UnaryOp { op, operand } => {
                format!("({} {})", op, operand.to_lean())
            }
            LeanExpr::App { func, args } => {
                if args.is_empty() {
                    func.to_lean()
                } else {
                    let args_str = args.iter().map(|a| a.to_lean()).collect::<Vec<_>>().join(" ");
                    format!("({} {})", func.to_lean(), args_str)
                }
            }
            LeanExpr::Lambda { params, body } => {
                let params_str = params
                    .iter()
                    .map(|(name, ty)| {
                        if let Some(t) = ty {
                            format!("({} : {})", name, t.to_lean())
                        } else {
                            name.clone()
                        }
                    })
                    .collect::<Vec<_>>()
                    .join(" ");
                format!("fun {} => {}", params_str, body.to_lean())
            }
            LeanExpr::Let { name, value, body } => {
                format!("let {} := {}\n  {}", name, value.to_lean(), body.to_lean())
            }
            LeanExpr::If {
                cond,
                then_branch,
                else_branch,
                ..
            } => {
                format!(
                    "if {} then {} else {}",
                    cond.to_lean(),
                    then_branch.to_lean(),
                    else_branch.to_lean()
                )
            }
            LeanExpr::Match { scrutinee, arms } => {
                let mut out = format!("match {} with\n", scrutinee.to_lean());
                for (pattern, bindings, body) in arms {
                    if bindings.is_empty() {
                        out.push_str(&format!("  | {} => {}\n", pattern, body.to_lean()));
                    } else {
                        out.push_str(&format!(
                            "  | {} {} => {}\n",
                            pattern,
                            bindings.join(" "),
                            body.to_lean()
                        ));
                    }
                }
                out
            }
            LeanExpr::Field { object, field } => {
                format!("{}.{}", object.to_lean(), field)
            }
            LeanExpr::StructInit { type_name: _, fields } => {
                let fields_str = fields
                    .iter()
                    .map(|(name, value)| format!("{} := {}", name, value.to_lean()))
                    .collect::<Vec<_>>()
                    .join(", ");
                format!("{{ {} }}", fields_str)
            }
            LeanExpr::List(elements) => {
                let elems_str = elements.iter().map(|e| e.to_lean()).collect::<Vec<_>>().join(", ");
                format!("[{}]", elems_str)
            }
            LeanExpr::Tuple(elements) => {
                let elems_str = elements.iter().map(|e| e.to_lean()).collect::<Vec<_>>().join(", ");
                format!("({})", elems_str)
            }
            LeanExpr::Do(stmts) => {
                let mut out = "do\n".to_string();
                for stmt in stmts {
                    out.push_str(&format!("  {}\n", stmt.to_lean()));
                }
                out
            }
            LeanExpr::Sorry => "sorry".to_string(),
            LeanExpr::Unit => "()".to_string(),
        }
    }
}

impl LeanLit {
    /// Convert to Lean syntax string
    pub fn to_lean(&self) -> String {
        match self {
            LeanLit::Int(n) => n.to_string(),
            LeanLit::Nat(n) => n.to_string(),
            LeanLit::Float(f) => format!("{:?}", f),
            LeanLit::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            LeanLit::String(s) => format!("\"{}\"", s.escape_default()),
            LeanLit::Char(c) => format!("'{}'", c.escape_default()),
        }
    }
}

impl LeanDoStmt {
    /// Convert to Lean syntax string
    pub fn to_lean(&self) -> String {
        match self {
            LeanDoStmt::Bind { name, expr } => format!("let {} ← {}", name, expr.to_lean()),
            LeanDoStmt::Let { name, expr } => format!("let {} := {}", name, expr.to_lean()),
            LeanDoStmt::Return(expr) => format!("pure {}", expr.to_lean()),
            LeanDoStmt::Expr(expr) => expr.to_lean(),
        }
    }
}

/// Expression translator for Simple → Lean conversion
pub struct ExprTranslator<'a> {
    type_translator: &'a TypeTranslator<'a>,
    /// Local variable names for index lookup
    locals: Vec<String>,
}

impl<'a> ExprTranslator<'a> {
    /// Create a new expression translator
    pub fn new(type_translator: &'a TypeTranslator<'a>) -> Self {
        Self {
            type_translator,
            locals: Vec::new(),
        }
    }

    /// Create an expression translator with local variable names
    pub fn with_locals(type_translator: &'a TypeTranslator<'a>, locals: &[LocalVar]) -> Self {
        Self {
            type_translator,
            locals: locals.iter().map(|l| l.name.clone()).collect(),
        }
    }

    /// Translate a HIR expression to Lean
    pub fn translate(&self, expr: &HirExpr) -> Result<LeanExpr, CompileError> {
        match &expr.kind {
            HirExprKind::Integer(n) => Ok(LeanExpr::Lit(LeanLit::Int(*n))),
            HirExprKind::Float(f) => Ok(LeanExpr::Lit(LeanLit::Float(*f))),
            HirExprKind::String(s) => Ok(LeanExpr::Lit(LeanLit::String(s.clone()))),
            HirExprKind::Bool(b) => Ok(LeanExpr::Lit(LeanLit::Bool(*b))),
            HirExprKind::Nil => Ok(LeanExpr::Unit),

            HirExprKind::Local(idx) => {
                let name = self
                    .locals
                    .get(*idx)
                    .map(|n| self.to_lean_name(n))
                    .unwrap_or_else(|| format!("local{}", idx));
                Ok(LeanExpr::Var(name))
            }
            HirExprKind::Global(name) => Ok(LeanExpr::Var(self.to_lean_name(name))),

            HirExprKind::Binary { op, left, right } => {
                let lean_op = self.translate_binop(op);
                let lean_left = self.translate(left)?;
                let lean_right = self.translate(right)?;
                Ok(LeanExpr::BinOp {
                    op: lean_op,
                    left: Box::new(lean_left),
                    right: Box::new(lean_right),
                })
            }
            HirExprKind::Unary { op, operand } => {
                let lean_op = self.translate_unaryop(op);
                let lean_operand = self.translate(operand)?;
                Ok(LeanExpr::UnaryOp {
                    op: lean_op,
                    operand: Box::new(lean_operand),
                })
            }

            HirExprKind::Call { func, args } => {
                let lean_func = self.translate(func)?;
                let lean_args: Result<Vec<_>, _> = args.iter().map(|a| self.translate(a)).collect();
                Ok(LeanExpr::App {
                    func: Box::new(lean_func),
                    args: lean_args?,
                })
            }

            HirExprKind::FieldAccess { receiver, field_index } => {
                let lean_receiver = self.translate(receiver)?;
                // Field access by index - we don't have field names here
                Ok(LeanExpr::Field {
                    object: Box::new(lean_receiver),
                    field: format!("field{}", field_index),
                })
            }

            HirExprKind::Index { receiver, index } => {
                let lean_receiver = self.translate(receiver)?;
                let lean_index = self.translate(index)?;
                Ok(LeanExpr::App {
                    func: Box::new(LeanExpr::Var("List.get!".to_string())),
                    args: vec![lean_receiver, lean_index],
                })
            }

            HirExprKind::If {
                condition,
                then_branch,
                else_branch,
            } => {
                let lean_cond = self.translate(condition)?;
                let lean_then = self.translate(then_branch)?;
                let lean_else = if let Some(ref else_expr) = else_branch {
                    self.translate(else_expr)?
                } else {
                    LeanExpr::Unit
                };
                Ok(LeanExpr::If {
                    cond: Box::new(lean_cond),
                    then_branch: Box::new(lean_then),
                    else_branch: Box::new(lean_else),
                })
            }

            HirExprKind::Array(elements) => {
                let lean_elements: Result<Vec<_>, _> = elements.iter().map(|e| self.translate(e)).collect();
                Ok(LeanExpr::List(lean_elements?))
            }
            HirExprKind::VecLiteral(elements) => {
                let lean_elements: Result<Vec<_>, _> = elements.iter().map(|e| self.translate(e)).collect();
                Ok(LeanExpr::List(lean_elements?))
            }
            HirExprKind::Tuple(elements) => {
                let lean_elements: Result<Vec<_>, _> = elements.iter().map(|e| self.translate(e)).collect();
                Ok(LeanExpr::Tuple(lean_elements?))
            }

            HirExprKind::StructInit { fields, .. } => {
                let lean_fields: Result<Vec<(String, LeanExpr)>, CompileError> = fields
                    .iter()
                    .enumerate()
                    .map(|(i, expr)| {
                        let lean_value = self.translate(expr)?;
                        Ok((format!("field{}", i), lean_value))
                    })
                    .collect();
                Ok(LeanExpr::StructInit {
                    type_name: String::new(), // Type info not available here
                    fields: lean_fields?,
                })
            }

            HirExprKind::Lambda { params, body, .. } => {
                let lean_params: Vec<_> = params
                    .iter()
                    .map(|(name, tid)| {
                        let lean_type = self.type_translator.translate(*tid).ok();
                        (self.to_lean_name(name), lean_type)
                    })
                    .collect();
                let lean_body = self.translate(body)?;
                Ok(LeanExpr::Lambda {
                    params: lean_params,
                    body: Box::new(lean_body),
                })
            }

            HirExprKind::ContractResult => Ok(LeanExpr::Var("result".to_string())),
            HirExprKind::ContractOld(inner) => {
                let lean_inner = self.translate(inner)?;
                Ok(LeanExpr::App {
                    func: Box::new(LeanExpr::Var("old".to_string())),
                    args: vec![lean_inner],
                })
            }

            // For other expression kinds, return sorry as placeholder
            _ => Ok(LeanExpr::Sorry),
        }
    }

    /// Translate statements to a Lean expression (nested lets)
    pub fn translate_stmts(&self, stmts: &[HirStmt], locals: &[LocalVar]) -> Result<LeanExpr, CompileError> {
        if stmts.is_empty() {
            return Ok(LeanExpr::Unit);
        }

        // Build nested let expressions from the end
        let mut result: Option<LeanExpr> = None;

        for stmt in stmts.iter().rev() {
            match stmt {
                HirStmt::Let { local_index, value, .. } => {
                    // Get the local name
                    let name = locals
                        .get(*local_index)
                        .map(|l| {
                            if l.is_ghost {
                                // Skip ghost variables
                                return None;
                            }
                            Some(self.to_lean_name(&l.name))
                        })
                        .flatten()
                        .unwrap_or_else(|| format!("local{}", local_index));

                    if let Some(val_expr) = value {
                        let lean_value = self.translate(val_expr)?;
                        if let Some(body) = result {
                            result = Some(LeanExpr::Let {
                                name,
                                value: Box::new(lean_value),
                                body: Box::new(body),
                            });
                        } else {
                            result = Some(lean_value);
                        }
                    }
                }
                HirStmt::Return(Some(expr)) => {
                    let lean_expr = self.translate(expr)?;
                    result = Some(lean_expr);
                }
                HirStmt::Return(None) => {
                    result = Some(LeanExpr::Unit);
                }
                HirStmt::Expr(expr) => {
                    let lean_expr = self.translate(expr)?;
                    if result.is_none() {
                        result = Some(lean_expr);
                    }
                }
                HirStmt::If {
                    condition,
                    then_block,
                    else_block,
                } => {
                    let lean_cond = self.translate(condition)?;
                    let lean_then = self.translate_stmts(then_block, locals)?;
                    let lean_else = if let Some(else_stmts) = else_block {
                        self.translate_stmts(else_stmts, locals)?
                    } else {
                        LeanExpr::Unit
                    };
                    let if_expr = LeanExpr::If {
                        cond: Box::new(lean_cond),
                        then_branch: Box::new(lean_then),
                        else_branch: Box::new(lean_else),
                    };
                    if let Some(body) = result {
                        // If there's more after, this is for side effects
                        result = Some(body);
                    } else {
                        result = Some(if_expr);
                    }
                }
                _ => {
                    // Skip other statements
                }
            }
        }

        Ok(result.unwrap_or(LeanExpr::Unit))
    }

    /// Translate a binary operator
    fn translate_binop(&self, op: &BinOp) -> String {
        match op {
            BinOp::Add => "+".to_string(),
            BinOp::Sub => "-".to_string(),
            BinOp::Mul => "*".to_string(),
            BinOp::Div => "/".to_string(),
            BinOp::Mod => "%".to_string(),
            BinOp::Pow => "^".to_string(),
            BinOp::FloorDiv => "/".to_string(), // Lean integer division
            BinOp::MatMul => "*".to_string(),   // Matrix multiplication
            BinOp::Eq => "==".to_string(),
            BinOp::NotEq => "!=".to_string(),
            BinOp::Lt => "<".to_string(),
            BinOp::LtEq => "<=".to_string(),
            BinOp::Gt => ">".to_string(),
            BinOp::GtEq => ">=".to_string(),
            BinOp::And | BinOp::AndSuspend => "&&".to_string(),
            BinOp::Or | BinOp::OrSuspend => "||".to_string(),
            BinOp::BitAnd => "&&&".to_string(),
            BinOp::BitOr => "|||".to_string(),
            BinOp::BitXor => "^^^".to_string(),
            BinOp::ShiftLeft => "<<<".to_string(),
            BinOp::ShiftRight => ">>>".to_string(),
            BinOp::Is => "==".to_string(), // Identity check becomes equality
            BinOp::In => "∈".to_string(),  // Membership
        }
    }

    /// Translate a unary operator
    fn translate_unaryop(&self, op: &UnaryOp) -> String {
        match op {
            UnaryOp::Neg => "-".to_string(),
            UnaryOp::Not => "!".to_string(),
            UnaryOp::BitNot => "~~~".to_string(),
        }
    }

    /// Convert a Simple name to Lean naming convention
    fn to_lean_name(&self, name: &str) -> String {
        // Convert snake_case to camelCase
        let mut result = String::new();
        let mut capitalize_next = false;

        for (i, c) in name.chars().enumerate() {
            if c == '_' {
                capitalize_next = true;
            } else if capitalize_next {
                result.push(c.to_ascii_uppercase());
                capitalize_next = false;
            } else if i == 0 {
                result.push(c.to_ascii_lowercase());
            } else {
                result.push(c);
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_expr_output() {
        let expr = LeanExpr::BinOp {
            op: "+".to_string(),
            left: Box::new(LeanExpr::Var("x".to_string())),
            right: Box::new(LeanExpr::Lit(LeanLit::Int(1))),
        };
        assert_eq!(expr.to_lean(), "(x + 1)");
    }

    #[test]
    fn test_lean_if_output() {
        let expr = LeanExpr::If {
            cond: Box::new(LeanExpr::Var("b".to_string())),
            then_branch: Box::new(LeanExpr::Lit(LeanLit::Int(1))),
            else_branch: Box::new(LeanExpr::Lit(LeanLit::Int(0))),
        };
        assert_eq!(expr.to_lean(), "if b then 1 else 0");
    }

    #[test]
    fn test_lean_list_output() {
        let expr = LeanExpr::List(vec![
            LeanExpr::Lit(LeanLit::Int(1)),
            LeanExpr::Lit(LeanLit::Int(2)),
            LeanExpr::Lit(LeanLit::Int(3)),
        ]);
        assert_eq!(expr.to_lean(), "[1, 2, 3]");
    }
}
