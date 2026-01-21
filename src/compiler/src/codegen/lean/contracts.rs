//! Lean contract translation.
//!
//! Translates Simple contracts to Lean 4 theorems:
//! - requires → precondition propositions
//! - ensures → postcondition theorems
//! - invariant → class invariant Props
//! - old() → local bindings for pre-state values

use super::expressions::{ExprTranslator, LeanExpr, LeanLit};
use super::types::{LeanType, TypeTranslator};
use crate::hir::{BinOp, HirContract, HirExpr, HirExprKind, HirFunction, UnaryOp};
use crate::CompileError;

/// A Lean theorem
#[derive(Debug, Clone)]
pub struct LeanTheorem {
    /// Theorem name
    pub name: String,
    /// Type parameters (implicit)
    pub type_params: Vec<String>,
    /// Hypotheses (h₁ : P₁, h₂ : P₂, ...)
    pub hypotheses: Vec<(String, LeanProp)>,
    /// Conclusion
    pub conclusion: LeanProp,
    /// Proof (None for sorry)
    pub proof: Option<String>,
    /// Documentation
    pub doc: Option<String>,
    /// Termination measure for recursive functions (from decreases: clause)
    pub termination_by: Option<LeanExpr>,
}

/// A Lean proposition
#[derive(Debug, Clone)]
pub enum LeanProp {
    /// True
    True,
    /// False
    False,
    /// Variable/named proposition
    Var(String),
    /// Negation
    Not(Box<LeanProp>),
    /// Conjunction (P ∧ Q)
    And(Box<LeanProp>, Box<LeanProp>),
    /// Disjunction (P ∨ Q)
    Or(Box<LeanProp>, Box<LeanProp>),
    /// Implication (P → Q)
    Implies(Box<LeanProp>, Box<LeanProp>),
    /// Universal quantification (∀ x, P x)
    Forall {
        var: String,
        ty: Option<LeanType>,
        body: Box<LeanProp>,
    },
    /// Existential quantification (∃ x, P x)
    Exists {
        var: String,
        ty: Option<LeanType>,
        body: Box<LeanProp>,
    },
    /// Equality (a = b)
    Eq(LeanExpr, LeanExpr),
    /// Less than (a < b)
    Lt(LeanExpr, LeanExpr),
    /// Less than or equal (a ≤ b)
    Le(LeanExpr, LeanExpr),
    /// Greater than (a > b)
    Gt(LeanExpr, LeanExpr),
    /// Greater than or equal (a ≥ b)
    Ge(LeanExpr, LeanExpr),
    /// Expression used as proposition (for decidable predicates)
    Expr(LeanExpr),
}

impl LeanTheorem {
    /// Emit as Lean theorem
    pub fn to_lean(&self, use_sorry: bool) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            for line in doc.lines() {
                out.push_str(&format!("/-- {} -/\n", line));
            }
        }

        out.push_str("theorem ");
        out.push_str(&self.name);

        // Type parameters
        if !self.type_params.is_empty() {
            out.push_str(" {");
            out.push_str(&self.type_params.join(" "));
            out.push_str("}");
        }

        // Hypotheses
        for (hyp_name, hyp_prop) in &self.hypotheses {
            out.push_str(&format!(" ({} : {})", hyp_name, hyp_prop.to_lean()));
        }

        // Conclusion
        out.push_str(&format!(" : {} :=", self.conclusion.to_lean()));

        // Proof
        if use_sorry {
            out.push_str("\n  sorry\n");
        } else if let Some(ref proof) = self.proof {
            out.push_str(&format!("\n  {}\n", proof));
        } else {
            out.push_str("\n  sorry\n");
        }

        // Termination measure (for recursive functions)
        if let Some(ref measure) = self.termination_by {
            out.push_str(&format!("termination_by {}\n", measure.to_lean()));
        }

        out
    }

    /// Emit as axiom (no proof required)
    pub fn to_axiom(&self) -> String {
        let mut out = String::new();

        // Doc comment
        if let Some(ref doc) = self.doc {
            for line in doc.lines() {
                out.push_str(&format!("/-- {} -/\n", line));
            }
        }

        out.push_str("axiom ");
        out.push_str(&self.name);

        // Type parameters
        if !self.type_params.is_empty() {
            out.push_str(" {");
            out.push_str(&self.type_params.join(" "));
            out.push_str("}");
        }

        // Hypotheses as implication
        for (_, hyp_prop) in &self.hypotheses {
            out.push_str(&format!(" : {} →", hyp_prop.to_lean()));
        }

        // Conclusion
        out.push_str(&format!(" {}\n", self.conclusion.to_lean()));

        out
    }
}

impl LeanProp {
    /// Convert to Lean syntax string
    pub fn to_lean(&self) -> String {
        match self {
            LeanProp::True => "True".to_string(),
            LeanProp::False => "False".to_string(),
            LeanProp::Var(name) => name.clone(),
            LeanProp::Not(p) => format!("¬{}", p.to_lean()),
            LeanProp::And(p, q) => format!("({} ∧ {})", p.to_lean(), q.to_lean()),
            LeanProp::Or(p, q) => format!("({} ∨ {})", p.to_lean(), q.to_lean()),
            LeanProp::Implies(p, q) => format!("({} → {})", p.to_lean(), q.to_lean()),
            LeanProp::Forall { var, ty, body } => {
                if let Some(t) = ty {
                    format!("(∀ {} : {}, {})", var, t.to_lean(), body.to_lean())
                } else {
                    format!("(∀ {}, {})", var, body.to_lean())
                }
            }
            LeanProp::Exists { var, ty, body } => {
                if let Some(t) = ty {
                    format!("(∃ {} : {}, {})", var, t.to_lean(), body.to_lean())
                } else {
                    format!("(∃ {}, {})", var, body.to_lean())
                }
            }
            LeanProp::Eq(l, r) => format!("({} = {})", l.to_lean(), r.to_lean()),
            LeanProp::Lt(l, r) => format!("({} < {})", l.to_lean(), r.to_lean()),
            LeanProp::Le(l, r) => format!("({} ≤ {})", l.to_lean(), r.to_lean()),
            LeanProp::Gt(l, r) => format!("({} > {})", l.to_lean(), r.to_lean()),
            LeanProp::Ge(l, r) => format!("({} ≥ {})", l.to_lean(), r.to_lean()),
            LeanProp::Expr(e) => e.to_lean(),
        }
    }

    /// Create a conjunction of multiple propositions
    pub fn and_all(props: Vec<LeanProp>) -> LeanProp {
        props
            .into_iter()
            .reduce(|acc, p| LeanProp::And(Box::new(acc), Box::new(p)))
            .unwrap_or(LeanProp::True)
    }

    /// Create a disjunction of multiple propositions
    pub fn or_all(props: Vec<LeanProp>) -> LeanProp {
        props
            .into_iter()
            .reduce(|acc, p| LeanProp::Or(Box::new(acc), Box::new(p)))
            .unwrap_or(LeanProp::False)
    }
}

/// Contract translator for Simple → Lean conversion
pub struct ContractTranslator<'a> {
    type_translator: &'a TypeTranslator<'a>,
}

impl<'a> ContractTranslator<'a> {
    /// Create a new contract translator
    pub fn new(type_translator: &'a TypeTranslator<'a>) -> Self {
        Self { type_translator }
    }

    /// Translate a function's contract to Lean theorems
    pub fn translate_contract(
        &self,
        func: &HirFunction,
        contract: &HirContract,
    ) -> Result<Vec<LeanTheorem>, CompileError> {
        let mut theorems = Vec::new();
        let expr_translator = ExprTranslator::new(self.type_translator);

        // Translate preconditions to hypotheses
        let preconditions: Result<Vec<_>, _> = contract
            .preconditions
            .iter()
            .map(|clause| self.translate_predicate(&expr_translator, &clause.condition))
            .collect();
        let preconditions = preconditions?;

        // Translate termination measure (decreases clause) to Lean expression
        let termination_by = if let Some(ref decreases) = contract.decreases {
            Some(expr_translator.translate(&decreases.condition)?)
        } else {
            None
        };

        // Translate success postconditions (out(ret):)
        for (i, clause) in contract.postconditions.iter().enumerate() {
            let conclusion = self.translate_predicate(&expr_translator, &clause.condition)?;

            // Build hypotheses from preconditions
            let hypotheses: Vec<_> = preconditions
                .iter()
                .enumerate()
                .map(|(j, p)| (format!("h{}", j + 1), p.clone()))
                .collect();

            let theorem = LeanTheorem {
                name: format!("{}Post_success{}", self.to_lean_name(&func.name), i + 1),
                type_params: vec![],
                hypotheses,
                conclusion,
                proof: None,
                doc: Some(format!("Success postcondition {} for function {}", i + 1, func.name)),
                termination_by: termination_by.clone(),
            };
            theorems.push(theorem);
        }

        // Translate error postconditions (out_err(err):)
        for (i, clause) in contract.error_postconditions.iter().enumerate() {
            let conclusion = self.translate_predicate(&expr_translator, &clause.condition)?;

            // Build hypotheses from preconditions
            let hypotheses: Vec<_> = preconditions
                .iter()
                .enumerate()
                .map(|(j, p)| (format!("h{}", j + 1), p.clone()))
                .collect();

            let theorem = LeanTheorem {
                name: format!("{}Post_error{}", self.to_lean_name(&func.name), i + 1),
                type_params: vec![],
                hypotheses,
                conclusion,
                proof: None,
                doc: Some(format!("Error postcondition {} for function {}", i + 1, func.name)),
                termination_by: termination_by.clone(),
            };
            theorems.push(theorem);
        }

        // Translate invariants
        for (i, clause) in contract.invariants.iter().enumerate() {
            let inv_prop = self.translate_predicate(&expr_translator, &clause.condition)?;

            let theorem = LeanTheorem {
                name: format!("{}Inv{}", self.to_lean_name(&func.name), i + 1),
                type_params: vec![],
                hypotheses: vec![],
                conclusion: inv_prop,
                proof: None,
                doc: Some(format!("Invariant {} for function {}", i + 1, func.name)),
                termination_by: None, // Invariants don't have termination measures
            };
            theorems.push(theorem);
        }

        Ok(theorems)
    }

    /// Translate a predicate expression to a Lean proposition
    fn translate_predicate(
        &self,
        expr_translator: &ExprTranslator,
        predicate: &HirExpr,
    ) -> Result<LeanProp, CompileError> {
        match &predicate.kind {
            HirExprKind::Binary { op, left, right } => {
                match op {
                    BinOp::Eq => {
                        let l = expr_translator.translate(left)?;
                        let r = expr_translator.translate(right)?;
                        Ok(LeanProp::Eq(l, r))
                    }
                    BinOp::Lt => {
                        let l = expr_translator.translate(left)?;
                        let r = expr_translator.translate(right)?;
                        Ok(LeanProp::Lt(l, r))
                    }
                    BinOp::LtEq => {
                        let l = expr_translator.translate(left)?;
                        let r = expr_translator.translate(right)?;
                        Ok(LeanProp::Le(l, r))
                    }
                    BinOp::Gt => {
                        let l = expr_translator.translate(left)?;
                        let r = expr_translator.translate(right)?;
                        Ok(LeanProp::Gt(l, r))
                    }
                    BinOp::GtEq => {
                        let l = expr_translator.translate(left)?;
                        let r = expr_translator.translate(right)?;
                        Ok(LeanProp::Ge(l, r))
                    }
                    BinOp::And => {
                        let l = self.translate_predicate(expr_translator, left)?;
                        let r = self.translate_predicate(expr_translator, right)?;
                        Ok(LeanProp::And(Box::new(l), Box::new(r)))
                    }
                    BinOp::Or => {
                        let l = self.translate_predicate(expr_translator, left)?;
                        let r = self.translate_predicate(expr_translator, right)?;
                        Ok(LeanProp::Or(Box::new(l), Box::new(r)))
                    }
                    _ => {
                        // Other operators: treat as expression
                        let expr = expr_translator.translate(predicate)?;
                        Ok(LeanProp::Expr(expr))
                    }
                }
            }
            HirExprKind::Unary { op, operand } => match op {
                UnaryOp::Not => {
                    let inner = self.translate_predicate(expr_translator, operand)?;
                    Ok(LeanProp::Not(Box::new(inner)))
                }
                _ => {
                    let expr = expr_translator.translate(predicate)?;
                    Ok(LeanProp::Expr(expr))
                }
            },
            HirExprKind::Bool(true) => Ok(LeanProp::True),
            HirExprKind::Bool(false) => Ok(LeanProp::False),
            _ => {
                // For other expressions, wrap as Expr proposition
                let expr = expr_translator.translate(predicate)?;
                Ok(LeanProp::Expr(expr))
            }
        }
    }

    /// Convert a Simple name to Lean naming convention (PascalCase for theorems)
    fn to_lean_name(&self, name: &str) -> String {
        super::naming::to_pascal_case(name)
    }
}

/// Class invariant representation
#[derive(Debug, Clone)]
pub struct LeanClassInvariant {
    /// Class name
    pub class_name: String,
    /// The invariant proposition
    pub invariant: LeanProp,
    /// Documentation
    pub doc: Option<String>,
}

impl LeanClassInvariant {
    /// Emit as Lean definition
    pub fn to_lean(&self) -> String {
        let mut out = String::new();

        if let Some(ref doc) = self.doc {
            for line in doc.lines() {
                out.push_str(&format!("/-- {} -/\n", line));
            }
        }

        out.push_str(&format!(
            "def {}Inv (self : {}) : Prop :=\n  {}\n",
            self.class_name,
            self.class_name,
            self.invariant.to_lean()
        ));

        out
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lean_prop_output() {
        let prop = LeanProp::And(
            Box::new(LeanProp::Gt(
                LeanExpr::Var("x".to_string()),
                LeanExpr::Lit(LeanLit::Int(0)),
            )),
            Box::new(LeanProp::Lt(
                LeanExpr::Var("x".to_string()),
                LeanExpr::Lit(LeanLit::Int(100)),
            )),
        );
        assert_eq!(prop.to_lean(), "((x > 0) ∧ (x < 100))");
    }

    #[test]
    fn test_lean_forall_output() {
        let prop = LeanProp::Forall {
            var: "x".to_string(),
            ty: Some(LeanType::Primitive("Int".to_string())),
            body: Box::new(LeanProp::Ge(
                LeanExpr::Var("x".to_string()),
                LeanExpr::Lit(LeanLit::Int(0)),
            )),
        };
        assert_eq!(prop.to_lean(), "(∀ x : Int, (x ≥ 0))");
    }

    #[test]
    fn test_lean_theorem_output() {
        let theorem = LeanTheorem {
            name: "addPositive".to_string(),
            type_params: vec![],
            hypotheses: vec![
                (
                    "hx".to_string(),
                    LeanProp::Gt(LeanExpr::Var("x".to_string()), LeanExpr::Lit(LeanLit::Int(0))),
                ),
                (
                    "hy".to_string(),
                    LeanProp::Gt(LeanExpr::Var("y".to_string()), LeanExpr::Lit(LeanLit::Int(0))),
                ),
            ],
            conclusion: LeanProp::Gt(
                LeanExpr::BinOp {
                    op: "+".to_string(),
                    left: Box::new(LeanExpr::Var("x".to_string())),
                    right: Box::new(LeanExpr::Var("y".to_string())),
                },
                LeanExpr::Lit(LeanLit::Int(0)),
            ),
            proof: None,
            doc: Some("Adding positive numbers yields positive".to_string()),
            termination_by: None,
        };

        let output = theorem.to_lean(true);
        assert!(output.contains("theorem addPositive"));
        assert!(output.contains("(hx : (x > 0))"));
        assert!(output.contains("sorry"));
    }

    #[test]
    fn test_lean_theorem_with_termination_by() {
        let theorem = LeanTheorem {
            name: "factorial".to_string(),
            type_params: vec![],
            hypotheses: vec![(
                "hn".to_string(),
                LeanProp::Ge(LeanExpr::Var("n".to_string()), LeanExpr::Lit(LeanLit::Int(0))),
            )],
            conclusion: LeanProp::Gt(LeanExpr::Var("result".to_string()), LeanExpr::Lit(LeanLit::Int(0))),
            proof: None,
            doc: Some("Factorial is always positive".to_string()),
            termination_by: Some(LeanExpr::Var("n".to_string())),
        };

        let output = theorem.to_lean(true);
        assert!(output.contains("theorem factorial"));
        assert!(output.contains("termination_by n"));
    }
}
