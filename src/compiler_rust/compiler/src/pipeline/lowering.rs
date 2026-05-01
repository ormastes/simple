//! AST → HIR → MIR lowering and type checking.

use simple_parser::ast::{AssignOp, BinOp, Block, Expr, ForStmt, Module, Node};
use simple_simd::detect_profile;
use simple_type::check as type_check;
use std::path::Path;

use super::core::{CompilerPipeline, SimdMode};
use crate::error::{codes, typo, ErrorContext};
use crate::hir;
use crate::hir::{BinOp as HirBinOp, HirExpr, HirExprKind, HirStmt, HirType, TypeId};
use crate::mir;
use crate::verification_checker::VerificationChecker;
use crate::CompileError;

#[derive(Clone)]
enum HIRSimdLoopCandidate {
    MapAdd {
        kernel: &'static str,
        out: HirExpr,
        lhs: HirExpr,
        rhs: HirExpr,
        guard: Option<HirExpr>,
    },
    MapMul {
        kernel: &'static str,
        out: HirExpr,
        lhs: HirExpr,
        rhs: HirExpr,
        guard: Option<HirExpr>,
    },
    MapFma {
        kernel: &'static str,
        out: HirExpr,
        a: HirExpr,
        b: HirExpr,
        c: HirExpr,
        guard: Option<HirExpr>,
    },
    ReductionSum {
        kernel: &'static str,
        target: HirExpr,
        input: HirExpr,
        guard: Option<HirExpr>,
    },
    ReductionMin {
        kernel: &'static str,
        target: HirExpr,
        input: HirExpr,
        guard: Option<HirExpr>,
    },
    ReductionMax {
        kernel: &'static str,
        target: HirExpr,
        input: HirExpr,
        guard: Option<HirExpr>,
    },
    ReductionDot {
        kernel: &'static str,
        target: HirExpr,
        lhs: HirExpr,
        rhs: HirExpr,
        guard: Option<HirExpr>,
    },
}

/// Convert LowerError to CompileError with rich error context
fn convert_lower_error(e: crate::hir::LowerError) -> CompileError {
    match e {
        crate::hir::LowerError::UnknownType {
            type_name,
            available_types,
        } => {
            // E1011 - Undefined Type
            let available_strs: Vec<&str> = available_types.iter().map(|s| s.as_str()).collect();
            let suggestion = if !available_strs.is_empty() {
                typo::suggest_name(&type_name, available_strs)
            } else {
                None
            };

            let mut ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_TYPE)
                .with_help("check that the type is defined or imported in this scope");

            if let Some(best_match) = suggestion {
                ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
            }

            CompileError::semantic_with_context(format!("type `{}` not found in this scope", type_name), ctx)
        }
        crate::hir::LowerError::SelfInStatic => {
            // E1032 - Self in Static
            let ctx = ErrorContext::new()
                .with_code(codes::SELF_IN_STATIC)
                .with_help("remove `self` or convert this to an instance method by removing `static` keyword");

            CompileError::semantic_with_context("cannot use `self` in static method".to_string(), ctx)
        }
        crate::hir::LowerError::LetBindingFailed { pattern } => {
            // E1016 - Let Binding Failed
            let ctx = ErrorContext::new()
                .with_code(codes::LET_BINDING_FAILED)
                .with_help("use a simple identifier pattern like `let x = ...` or `let mut x = ...`")
                .with_note("complex patterns like tuples and arrays are not yet supported in let bindings");

            CompileError::semantic_with_context(
                format!("let binding failed: pattern `{}` is not supported", pattern),
                ctx,
            )
        }
        crate::hir::LowerError::ImpureFunctionInContract { func_name } => {
            // E1017 - Impure Function in Contract
            let ctx = ErrorContext::new()
                .with_code(codes::IMPURE_FUNCTION_IN_CONTRACT)
                .with_help("add #[pure] attribute to the function or use a different function")
                .with_note("contract expressions (requires, ensures, invariant) must only call pure functions");

            CompileError::semantic_with_context(
                format!("cannot call impure function `{}` in contract expression", func_name),
                ctx,
            )
        }
        crate::hir::LowerError::CannotInferFieldType {
            struct_name,
            field,
            available_fields,
        } => {
            // E1012 - Undefined Field
            let available_strs: Vec<&str> = available_fields.iter().map(|s| s.as_str()).collect();
            let suggestion = if !available_strs.is_empty() {
                typo::suggest_name(&field, available_strs)
            } else {
                None
            };

            let mut ctx = ErrorContext::new()
                .with_code(codes::UNDEFINED_FIELD)
                .with_help("check the field name and struct definition");

            if let Some(best_match) = suggestion {
                ctx = ctx.with_help(format!("did you mean `{}`?", best_match));
            }

            if !available_fields.is_empty() && available_fields.len() <= 5 {
                let fields_list = available_fields.join(", ");
                ctx = ctx.with_note(format!("available fields: {}", fields_list));
            }

            CompileError::semantic_with_context(format!("struct `{}` has no field named `{}`", struct_name, field), ctx)
        }
        crate::hir::LowerError::LifetimeViolation(violation) => {
            // E2001-E2006 - Lifetime Violations
            let ctx = ErrorContext::new()
                .with_code(violation.code())
                .with_help(match &violation {
                    crate::hir::LifetimeViolation::EscapingReference { .. } => {
                        "consider returning an owned value instead of a reference"
                    }
                    crate::hir::LifetimeViolation::UseAfterDrop { .. } => {
                        "ensure the value lives long enough for all uses"
                    }
                    crate::hir::LifetimeViolation::DanglingReference { .. } => "the referenced value has been dropped",
                    crate::hir::LifetimeViolation::BorrowOutlivesOwner { .. } => {
                        "reduce the borrow's scope or extend the owner's lifetime"
                    }
                    crate::hir::LifetimeViolation::ReturnLocalReference { .. } => {
                        "return an owned value or use a parameter reference"
                    }
                    crate::hir::LifetimeViolation::StorageEscapes { .. } => {
                        "don't store short-lived references in longer-lived locations"
                    }
                });

            CompileError::semantic_with_context(violation.description(), ctx)
        }
        crate::hir::LowerError::LifetimeViolations(violations) => {
            // Multiple lifetime violations
            let messages: Vec<String> = violations
                .iter()
                .map(|v| format!("[{}] {}", v.code(), v.description()))
                .collect();
            let ctx = ErrorContext::new()
                .with_code("E2000")
                .with_note(format!("{} lifetime violations detected", violations.len()));

            CompileError::semantic_with_context(messages.join("\n"), ctx)
        }
        // Other errors just get converted to simple semantic errors
        other => crate::error::factory::hir_lowering_failed(&other),
    }
}

impl CompilerPipeline {
    pub(super) fn emit_explicit_simd_warnings(&self, ast_module: &Module) {
        if self.simd_mode != SimdMode::Auto {
            return;
        }

        for line in self.collect_explicit_simd_warning_lines(ast_module) {
            eprintln!("{line}");
        }
    }

    pub(super) fn collect_explicit_simd_warning_lines(&self, ast_module: &Module) -> Vec<String> {
        let mut lines = Vec::new();
        for item in &ast_module.items {
            self.collect_explicit_simd_warning_lines_from_node(item, &mut lines);
        }
        lines
    }

    fn collect_explicit_simd_warning_lines_from_block(&self, block: &Block, lines: &mut Vec<String>) {
        for stmt in &block.statements {
            self.collect_explicit_simd_warning_lines_from_node(stmt, lines);
        }
    }

    fn collect_explicit_simd_warning_lines_from_node(&self, node: &Node, lines: &mut Vec<String>) {
        match node {
            Node::Function(func) => self.collect_explicit_simd_warning_lines_from_block(&func.body, lines),
            Node::For(stmt) => {
                if stmt.simd_requested && self.classify_auto_simd_for_loop(stmt).is_none() {
                    lines.push(format!(
                        "warning: {}:{}: explicit @simd on for-loop was not vectorized: {}",
                        stmt.span.line,
                        stmt.span.column,
                        self.explicit_simd_for_reason(stmt)
                    ));
                }
                self.collect_explicit_simd_warning_lines_from_block(&stmt.body, lines);
            }
            Node::While(stmt) => {
                if stmt.simd_requested {
                    lines.push(format!(
                        "warning: {}:{}: explicit @simd on while-loop was not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                        stmt.span.line, stmt.span.column
                    ));
                }
                self.collect_explicit_simd_warning_lines_from_block(&stmt.body, lines);
            }
            Node::Loop(stmt) => {
                if stmt.simd_requested {
                    lines.push(format!(
                        "warning: {}:{}: explicit @simd on loop was not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                        stmt.span.line, stmt.span.column
                    ));
                }
                self.collect_explicit_simd_warning_lines_from_block(&stmt.body, lines);
            }
            Node::If(stmt) => {
                self.collect_explicit_simd_warning_lines_from_block(&stmt.then_block, lines);
                for (_, _, block) in &stmt.elif_branches {
                    self.collect_explicit_simd_warning_lines_from_block(block, lines);
                }
                if let Some(block) = &stmt.else_block {
                    self.collect_explicit_simd_warning_lines_from_block(block, lines);
                }
            }
            Node::Match(stmt) => {
                for arm in &stmt.arms {
                    self.collect_explicit_simd_warning_lines_from_block(&arm.body, lines);
                }
            }
            Node::Context(stmt) => self.collect_explicit_simd_warning_lines_from_block(&stmt.body, lines),
            Node::With(stmt) => self.collect_explicit_simd_warning_lines_from_block(&stmt.body, lines),
            Node::Defer(stmt) => match &stmt.body {
                simple_parser::ast::DeferBody::Block(block) => {
                    self.collect_explicit_simd_warning_lines_from_block(block, lines)
                }
                simple_parser::ast::DeferBody::Expr(_) => {}
            },
            Node::Skip(stmt) => {
                if let simple_parser::ast::SkipBody::Block(block) = &stmt.body {
                    self.collect_explicit_simd_warning_lines_from_block(block, lines);
                }
            }
            _ => {}
        }
    }

    pub(super) fn emit_simd_report(&self, ast_module: &Module) {
        if self.simd_mode != SimdMode::Report {
            return;
        }

        let host_tier = detect_profile();
        let selected_tier = host_tier.best_available_implementation();
        eprintln!(
            "simd-report: host_tier={} selected_runtime_tier={}",
            host_tier, selected_tier
        );

        for line in self.collect_simd_report_lines(ast_module) {
            eprintln!("{line}");
        }
    }

    pub(super) fn collect_simd_report_lines(&self, ast_module: &Module) -> Vec<String> {
        let mut lines = Vec::new();
        for item in &ast_module.items {
            self.collect_simd_report_lines_from_node(item, &mut lines);
        }
        lines
    }

    fn collect_simd_report_lines_from_block(&self, block: &Block, lines: &mut Vec<String>) {
        for stmt in &block.statements {
            self.collect_simd_report_lines_from_node(stmt, lines);
        }
    }

    fn collect_simd_report_lines_from_node(&self, node: &Node, lines: &mut Vec<String>) {
        match node {
            Node::Function(func) => self.collect_simd_report_lines_from_block(&func.body, lines),
            Node::For(stmt) => self.collect_simd_report_lines_from_block(&stmt.body, lines),
            Node::While(stmt) => {
                if stmt.simd_requested {
                    lines.push(format!(
                        "simd-report: {}:{}: explicit @simd on while-loop; not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                        stmt.span.line, stmt.span.column
                    ));
                }
                self.collect_simd_report_lines_from_block(&stmt.body, lines);
            }
            Node::Loop(stmt) => {
                if stmt.simd_requested {
                    lines.push(format!(
                        "simd-report: {}:{}: explicit @simd on loop; not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                        stmt.span.line, stmt.span.column
                    ));
                }
                self.collect_simd_report_lines_from_block(&stmt.body, lines);
            }
            Node::If(stmt) => {
                self.collect_simd_report_lines_from_block(&stmt.then_block, lines);
                for (_, _, block) in &stmt.elif_branches {
                    self.collect_simd_report_lines_from_block(block, lines);
                }
                if let Some(block) = &stmt.else_block {
                    self.collect_simd_report_lines_from_block(block, lines);
                }
            }
            Node::Match(stmt) => {
                for arm in &stmt.arms {
                    self.collect_simd_report_lines_from_block(&arm.body, lines);
                }
            }
            Node::Context(stmt) => self.collect_simd_report_lines_from_block(&stmt.body, lines),
            Node::With(stmt) => self.collect_simd_report_lines_from_block(&stmt.body, lines),
            Node::Defer(stmt) => match &stmt.body {
                simple_parser::ast::DeferBody::Block(block) => self.collect_simd_report_lines_from_block(block, lines),
                simple_parser::ast::DeferBody::Expr(_) => {}
            },
            Node::Skip(stmt) => {
                if let simple_parser::ast::SkipBody::Block(block) = &stmt.body {
                    self.collect_simd_report_lines_from_block(block, lines);
                }
            }
            _ => {}
        }
    }

    fn explicit_simd_for_reason(&self, stmt: &ForStmt) -> &'static str {
        if self.classify_auto_simd_for_loop(stmt).is_some() {
            return "loop SIMD lowering is not implemented yet";
        }

        match &stmt.pattern {
            simple_parser::ast::Pattern::Identifier(_) => {}
            _ => return "unsupported index pattern",
        }

        if !matches!(
            stmt.iterable,
            Expr::Range {
                start: Some(_),
                end: Some(_),
                ..
            }
        ) {
            return "unsupported loop form (only canonical range for-loops are analyzed)";
        }

        if stmt.body.statements.len() != 1 {
            return "loop body has unsupported shape (expected a single assignment or reduction)";
        }

        match &stmt.body.statements[0] {
            Node::Assignment(assign) => {
                if matches!(assign.op, AssignOp::AddAssign) && matches!(assign.target, Expr::Identifier(_)) {
                    return "unsupported reduction form";
                }

                if !matches!(assign.op, AssignOp::Assign) {
                    return "unsupported assignment operator";
                }

                if !matches!(assign.target, Expr::Index { .. }) {
                    return "unsupported store pattern";
                }

                "unsupported loop body shape"
            }
            _ => "unsupported loop body shape",
        }
    }

    fn classify_auto_simd_for_loop(&self, stmt: &ForStmt) -> Option<&'static str> {
        let loop_var = match &stmt.pattern {
            simple_parser::ast::Pattern::Identifier(name) => name.as_str(),
            _ => return None,
        };

        if !matches!(
            stmt.iterable,
            Expr::Range {
                start: Some(_),
                end: Some(_),
                ..
            }
        ) {
            return None;
        }

        if stmt.body.statements.len() != 1 {
            return None;
        }

        match &stmt.body.statements[0] {
            Node::Assignment(assign) => {
                if matches!(assign.op, AssignOp::AddAssign)
                    && matches!(assign.target, Expr::Identifier(_))
                    && self.indexed_receiver_name(&assign.value, loop_var).is_some()
                {
                    return Some("reduction_sum");
                }

                if !matches!(assign.op, AssignOp::Assign) {
                    return None;
                }

                let out_name = self.indexed_receiver_name(&assign.target, loop_var)?;
                let Expr::Binary { op, left, right } = &assign.value else {
                    return None;
                };

                match op {
                    BinOp::Add => {
                        if self.is_fma_shape(left, right, loop_var) || self.is_fma_shape(right, left, loop_var) {
                            return Some("map_fma_f32");
                        }
                        let lhs = self.indexed_receiver_name(left, loop_var)?;
                        let rhs = self.indexed_receiver_name(right, loop_var)?;
                        if lhs != out_name && rhs != out_name {
                            return Some("map_add");
                        }
                        None
                    }
                    BinOp::Mul => {
                        let lhs = self.indexed_receiver_name(left, loop_var)?;
                        let rhs = self.indexed_receiver_name(right, loop_var)?;
                        if lhs != out_name && rhs != out_name {
                            Some("map_mul")
                        } else {
                            None
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn is_fma_shape(&self, mul_expr: &Expr, add_expr: &Expr, loop_var: &str) -> bool {
        let Expr::Binary {
            op: BinOp::Mul,
            left,
            right,
        } = mul_expr
        else {
            return false;
        };

        self.indexed_receiver_name(left, loop_var).is_some()
            && self.indexed_receiver_name(right, loop_var).is_some()
            && self.indexed_receiver_name(add_expr, loop_var).is_some()
    }

    fn indexed_receiver_name<'a>(&self, expr: &'a Expr, loop_var: &str) -> Option<&'a str> {
        let Expr::Index { receiver, index } = expr else {
            return None;
        };
        let Expr::Identifier(index_name) = index.as_ref() else {
            return None;
        };
        if index_name != loop_var {
            return None;
        }
        let Expr::Identifier(receiver_name) = receiver.as_ref() else {
            return None;
        };
        Some(receiver_name.as_str())
    }
}

impl CompilerPipeline {
    pub(super) fn emit_typed_explicit_simd_warnings(&self, hir_module: &hir::HirModule) {
        if self.simd_mode != SimdMode::Auto {
            return;
        }

        for line in self.collect_typed_explicit_simd_warning_lines(hir_module) {
            eprintln!("{line}");
        }
    }

    pub(super) fn collect_typed_explicit_simd_warning_lines(&self, hir_module: &hir::HirModule) -> Vec<String> {
        let mut lines = Vec::new();
        for function in &hir_module.functions {
            self.collect_typed_explicit_simd_warning_lines_from_stmts(
                &hir_module.types,
                &function.name,
                &function.body,
                &mut lines,
            );
        }
        lines
    }

    fn collect_typed_explicit_simd_warning_lines_from_stmts(
        &self,
        types: &hir::TypeRegistry,
        function_name: &str,
        stmts: &[HirStmt],
        lines: &mut Vec<String>,
    ) {
        for stmt in stmts {
            match stmt {
                HirStmt::For {
                    iterable,
                    body,
                    simd_requested,
                    ..
                } => {
                    if *simd_requested && self.classify_hir_simd_for_loop(types, iterable, body).is_none() {
                        lines.push(format!(
                            "warning: function={function_name}: explicit @simd on for-loop was not vectorized: no typed runtime-kernel lowering available"
                        ));
                    }
                    self.collect_typed_explicit_simd_warning_lines_from_stmts(types, function_name, body, lines);
                }
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    self.collect_typed_explicit_simd_warning_lines_from_stmts(types, function_name, then_block, lines);
                    if let Some(else_block) = else_block {
                        self.collect_typed_explicit_simd_warning_lines_from_stmts(
                            types,
                            function_name,
                            else_block,
                            lines,
                        );
                    }
                }
                HirStmt::While { body, .. } | HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
                    self.collect_typed_explicit_simd_warning_lines_from_stmts(types, function_name, body, lines);
                }
                _ => {}
            }
        }
    }

    pub(super) fn emit_typed_simd_report(&self, hir_module: &hir::HirModule) {
        if self.simd_mode != SimdMode::Report {
            return;
        }

        for line in self.collect_typed_simd_report_lines(hir_module) {
            eprintln!("{line}");
        }
    }

    pub(super) fn collect_typed_simd_report_lines(&self, hir_module: &hir::HirModule) -> Vec<String> {
        let mut lines = Vec::new();
        for function in &hir_module.functions {
            self.collect_typed_simd_report_lines_from_stmts(
                &hir_module.types,
                &function.name,
                &function.body,
                &mut lines,
            );
        }
        lines
    }

    fn collect_typed_simd_report_lines_from_stmts(
        &self,
        types: &hir::TypeRegistry,
        function_name: &str,
        stmts: &[HirStmt],
        lines: &mut Vec<String>,
    ) {
        for stmt in stmts {
            match stmt {
                HirStmt::For {
                    iterable,
                    body,
                    simd_requested,
                    ..
                } => {
                    if let Some(candidate) = self.classify_hir_simd_for_loop(types, iterable, body) {
                        lines.push(format!(
                            "simd-report: function={} for-loop; vectorized via runtime kernel {}",
                            function_name,
                            self.hir_simd_candidate_kernel_name(&candidate)
                        ));
                    } else if *simd_requested {
                        lines.push(format!(
                            "simd-report: function={} explicit @simd on for-loop; not vectorized: no typed runtime-kernel lowering available",
                            function_name
                        ));
                    }
                    self.collect_typed_simd_report_lines_from_stmts(types, function_name, body, lines);
                }
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    self.collect_typed_simd_report_lines_from_stmts(types, function_name, then_block, lines);
                    if let Some(else_block) = else_block {
                        self.collect_typed_simd_report_lines_from_stmts(types, function_name, else_block, lines);
                    }
                }
                HirStmt::While {
                    body, simd_requested, ..
                } => {
                    if *simd_requested {
                        lines.push(format!(
                            "simd-report: function={} explicit @simd on while-loop; not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                            function_name
                        ));
                    }
                    self.collect_typed_simd_report_lines_from_stmts(types, function_name, body, lines);
                }
                HirStmt::Loop { body, simd_requested } => {
                    if *simd_requested {
                        lines.push(format!(
                            "simd-report: function={} explicit @simd on loop; not vectorized: unsupported loop form (only canonical range for-loops are analyzed)",
                            function_name
                        ));
                    }
                    self.collect_typed_simd_report_lines_from_stmts(types, function_name, body, lines);
                }
                HirStmt::Defer { body } => {
                    self.collect_typed_simd_report_lines_from_stmts(types, function_name, body, lines);
                }
                _ => {}
            }
        }
    }

    fn hir_simd_candidate_kernel_name(&self, candidate: &HIRSimdLoopCandidate) -> &'static str {
        match candidate {
            HIRSimdLoopCandidate::MapAdd { kernel, .. } => kernel,
            HIRSimdLoopCandidate::MapMul { kernel, .. } => kernel,
            HIRSimdLoopCandidate::MapFma { kernel, .. } => kernel,
            HIRSimdLoopCandidate::ReductionSum { kernel, .. } => kernel,
            HIRSimdLoopCandidate::ReductionMin { kernel, .. } => kernel,
            HIRSimdLoopCandidate::ReductionMax { kernel, .. } => kernel,
            HIRSimdLoopCandidate::ReductionDot { kernel, .. } => kernel,
        }
    }

    fn rewrite_hir_simd_loops(&self, hir_module: &mut hir::HirModule) {
        if self.simd_mode != SimdMode::Auto {
            return;
        }

        for function in &mut hir_module.functions {
            self.rewrite_hir_simd_stmts(&hir_module.types, &mut function.body);
        }
    }

    fn rewrite_hir_simd_stmts(&self, types: &hir::TypeRegistry, stmts: &mut Vec<HirStmt>) {
        for stmt in stmts.iter_mut() {
            match stmt {
                HirStmt::For {
                    pattern,
                    iterable,
                    body,
                    simd_requested,
                    invariants,
                } => {
                    self.rewrite_hir_simd_stmts(types, body);
                    let fallback = HirStmt::For {
                        pattern: pattern.clone(),
                        iterable: iterable.clone(),
                        body: body.clone(),
                        simd_requested: *simd_requested,
                        invariants: invariants.clone(),
                    };
                    if let Some(candidate) = self.classify_hir_simd_for_loop(types, iterable, body) {
                        *stmt = self.lower_hir_simd_candidate(candidate, fallback);
                    }
                }
                HirStmt::If {
                    then_block, else_block, ..
                } => {
                    self.rewrite_hir_simd_stmts(types, then_block);
                    if let Some(else_block) = else_block {
                        self.rewrite_hir_simd_stmts(types, else_block);
                    }
                }
                HirStmt::While { body, .. } | HirStmt::Loop { body, .. } | HirStmt::Defer { body } => {
                    self.rewrite_hir_simd_stmts(types, body);
                }
                _ => {}
            }
        }
    }

    fn lower_hir_simd_candidate(&self, candidate: HIRSimdLoopCandidate, fallback: HirStmt) -> HirStmt {
        let (guard, lowered) = match candidate {
            HIRSimdLoopCandidate::MapAdd {
                kernel,
                out,
                lhs,
                rhs,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: out.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![lhs, rhs],
                        },
                        ty: out.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::MapMul {
                kernel,
                out,
                lhs,
                rhs,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: out.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![lhs, rhs],
                        },
                        ty: out.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::MapFma {
                kernel,
                out,
                a,
                b,
                c,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: out.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![a, b, c],
                        },
                        ty: out.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::ReductionSum {
                kernel,
                target,
                input,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: target.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![input],
                        },
                        ty: target.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::ReductionMin {
                kernel,
                target,
                input,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: target.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![input],
                        },
                        ty: target.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::ReductionMax {
                kernel,
                target,
                input,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: target.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![input],
                        },
                        ty: target.ty,
                    },
                },
            ),
            HIRSimdLoopCandidate::ReductionDot {
                kernel,
                target,
                lhs,
                rhs,
                guard,
            } => (
                guard,
                HirStmt::Assign {
                    target: target.clone(),
                    value: HirExpr {
                        kind: HirExprKind::BuiltinCall {
                            name: kernel.to_string(),
                            args: vec![lhs, rhs],
                        },
                        ty: target.ty,
                    },
                },
            ),
        };

        if let Some(condition) = guard {
            HirStmt::If {
                condition,
                then_block: vec![lowered],
                else_block: Some(vec![fallback]),
            }
        } else {
            lowered
        }
    }

    fn classify_hir_simd_for_loop(
        &self,
        types: &hir::TypeRegistry,
        iterable: &HirExpr,
        body: &[HirStmt],
    ) -> Option<HIRSimdLoopCandidate> {
        let HirExprKind::BuiltinCall { name, args } = &iterable.kind else {
            return None;
        };
        if name != "rt_range" || args.len() != 2 {
            return None;
        }
        if !matches!(args[0].kind, HirExprKind::Integer(0)) {
            return None;
        }
        if body.len() != 1 {
            return None;
        }

        let HirStmt::Assign { target, value } = &body[0] else {
            return None;
        };
        if let Some(reduction) = self.classify_hir_simd_reduction(types, &args[1], target, value) {
            return Some(reduction);
        }

        let HirExprKind::Index { receiver: out, .. } = &target.kind else {
            return None;
        };
        let out = out.as_ref().clone();

        let out_layout = self.float_array_layout(types, &out)?;

        let HirExprKind::Binary { op, left, right } = &value.kind else {
            return None;
        };

        match op {
            HirBinOp::Add => {
                if let Some((a, b, c)) = self.hir_fma_operands(left, right) {
                    let a_layout = self.float_array_layout(types, a)?;
                    let b_layout = self.float_array_layout(types, b)?;
                    let c_layout = self.float_array_layout(types, c)?;
                    if a_layout != out_layout
                        || b_layout != out_layout
                        || c_layout != out_layout
                        || out == *a
                        || out == *b
                        || out == *c
                    {
                        return None;
                    }
                    let guard = self.build_simd_bound_guard(types, &args[1], [&out, a, b, c])?;
                    let kernel = match out_layout.0 {
                        TypeId::F32 => "rt_numeric_fma_f32",
                        TypeId::F64 => "rt_numeric_fma_f64",
                        _ => return None,
                    };
                    return Some(HIRSimdLoopCandidate::MapFma {
                        kernel,
                        out,
                        a: a.clone(),
                        b: b.clone(),
                        c: c.clone(),
                        guard,
                    });
                }

                let lhs = self.hir_indexed_array_receiver(left)?.clone();
                let rhs = self.hir_indexed_array_receiver(right)?.clone();
                let lhs_layout = self.float_array_layout(types, &lhs)?;
                let rhs_layout = self.float_array_layout(types, &rhs)?;
                if lhs_layout != out_layout || rhs_layout != out_layout || out == lhs || out == rhs {
                    return None;
                }
                let guard = self.build_simd_bound_guard(types, &args[1], [&out, &lhs, &rhs])?;
                let kernel = match out_layout.0 {
                    TypeId::F32 => "rt_numeric_add_f32",
                    TypeId::F64 => "rt_numeric_add_f64",
                    _ => return None,
                };
                Some(HIRSimdLoopCandidate::MapAdd {
                    kernel,
                    out,
                    lhs,
                    rhs,
                    guard,
                })
            }
            HirBinOp::Mul => {
                let lhs = self.hir_indexed_array_receiver(left)?.clone();
                let rhs = self.hir_indexed_array_receiver(right)?.clone();
                let lhs_layout = self.float_array_layout(types, &lhs)?;
                let rhs_layout = self.float_array_layout(types, &rhs)?;
                if lhs_layout != out_layout || rhs_layout != out_layout || out == lhs || out == rhs {
                    return None;
                }
                let guard = self.build_simd_bound_guard(types, &args[1], [&out, &lhs, &rhs])?;
                let kernel = match out_layout.0 {
                    TypeId::F32 => "rt_numeric_mul_f32",
                    TypeId::F64 => "rt_numeric_mul_f64",
                    _ => return None,
                };
                Some(HIRSimdLoopCandidate::MapMul {
                    kernel,
                    out,
                    lhs,
                    rhs,
                    guard,
                })
            }
            _ => None,
        }
    }

    fn classify_hir_simd_reduction(
        &self,
        types: &hir::TypeRegistry,
        range_end: &HirExpr,
        target: &HirExpr,
        value: &HirExpr,
    ) -> Option<HIRSimdLoopCandidate> {
        let HirExprKind::Local(target_idx) = target.kind else {
            return None;
        };
        match &value.kind {
            HirExprKind::Binary {
                op: HirBinOp::Add,
                left,
                right,
            } => {
                if let Some((lhs, rhs)) = self.hir_dot_reduction_operands(target_idx, left, right) {
                    let lhs = lhs.clone();
                    let rhs = rhs.clone();
                    let (lhs_ty, _) = self.float_array_layout(types, &lhs)?;
                    let (rhs_ty, _) = self.float_array_layout(types, &rhs)?;
                    if lhs_ty != rhs_ty || target.ty != lhs_ty {
                        return None;
                    }
                    let guard = self.build_simd_bound_guard(types, range_end, [&lhs, &rhs])?;
                    let kernel = match lhs_ty {
                        TypeId::F32 => "rt_numeric_dot_f32",
                        TypeId::F64 => "rt_numeric_dot_f64",
                        _ => return None,
                    };
                    return Some(HIRSimdLoopCandidate::ReductionDot {
                        kernel,
                        target: target.clone(),
                        lhs,
                        rhs,
                        guard,
                    });
                }

                let input = if matches!(left.kind, HirExprKind::Local(idx) if idx == target_idx) {
                    self.hir_indexed_array_receiver(right)?
                } else if matches!(right.kind, HirExprKind::Local(idx) if idx == target_idx) {
                    self.hir_indexed_array_receiver(left)?
                } else {
                    return None;
                };

                let (element_ty, _) = self.float_array_layout(types, input)?;
                if target.ty != element_ty {
                    return None;
                }
                let guard = self.build_simd_bound_guard(types, range_end, [input])?;
                let kernel = match element_ty {
                    TypeId::F32 => "rt_numeric_sum_f32",
                    TypeId::F64 => "rt_numeric_sum_f64",
                    _ => return None,
                };

                Some(HIRSimdLoopCandidate::ReductionSum {
                    kernel,
                    target: target.clone(),
                    input: input.clone(),
                    guard,
                })
            }
            HirExprKind::BuiltinCall { name, args } if args.len() == 2 && (name == "min" || name == "max") => {
                let input = if matches!(args[0].kind, HirExprKind::Local(idx) if idx == target_idx) {
                    self.hir_indexed_array_receiver(&args[1])?
                } else if matches!(args[1].kind, HirExprKind::Local(idx) if idx == target_idx) {
                    self.hir_indexed_array_receiver(&args[0])?
                } else {
                    return None;
                };

                let (element_ty, _) = self.float_array_layout(types, input)?;
                if target.ty != TypeId::F32 || element_ty != TypeId::F32 {
                    return None;
                }
                let guard = self.build_simd_bound_guard(types, range_end, [input])?;
                let candidate = if name == "min" {
                    HIRSimdLoopCandidate::ReductionMin {
                        kernel: "rt_numeric_min_f32",
                        target: target.clone(),
                        input: input.clone(),
                        guard,
                    }
                } else {
                    HIRSimdLoopCandidate::ReductionMax {
                        kernel: "rt_numeric_max_f32",
                        target: target.clone(),
                        input: input.clone(),
                        guard,
                    }
                };
                Some(candidate)
            }
            _ => None,
        }
    }

    fn hir_dot_reduction_operands<'a>(
        &self,
        target_idx: usize,
        left: &'a HirExpr,
        right: &'a HirExpr,
    ) -> Option<(&'a HirExpr, &'a HirExpr)> {
        if matches!(left.kind, HirExprKind::Local(idx) if idx == target_idx) {
            return self.hir_mul_indexed_array_operands(right);
        }
        if matches!(right.kind, HirExprKind::Local(idx) if idx == target_idx) {
            return self.hir_mul_indexed_array_operands(left);
        }
        None
    }

    fn hir_mul_indexed_array_operands<'a>(&self, expr: &'a HirExpr) -> Option<(&'a HirExpr, &'a HirExpr)> {
        let HirExprKind::Binary {
            op: HirBinOp::Mul,
            left,
            right,
        } = &expr.kind
        else {
            return None;
        };
        Some((
            self.hir_indexed_array_receiver(left)?,
            self.hir_indexed_array_receiver(right)?,
        ))
    }

    fn build_simd_bound_guard<const N: usize>(
        &self,
        types: &hir::TypeRegistry,
        end: &HirExpr,
        receivers: [&HirExpr; N],
    ) -> Option<Option<HirExpr>> {
        let mut guard_terms = Vec::new();
        let mut seen = Vec::new();

        for receiver in receivers {
            let (_, size) = self.float_array_layout(types, receiver)?;
            let requires_guard = self.receiver_bound_requires_guard(end, receiver, size)?;
            if requires_guard && !seen.iter().any(|existing: &HirExpr| existing == receiver) {
                seen.push(receiver.clone());
                guard_terms.push(self.make_eq_expr(self.make_len_expr(receiver.clone()), end.clone()));
            }
        }

        let mut guard = None;
        for term in guard_terms {
            guard = Some(match guard {
                Some(existing) => self.make_bool_and(existing, term),
                None => term,
            });
        }
        Some(guard)
    }

    fn hir_fma_operands<'a>(
        &self,
        lhs: &'a HirExpr,
        rhs: &'a HirExpr,
    ) -> Option<(&'a HirExpr, &'a HirExpr, &'a HirExpr)> {
        if let HirExprKind::Binary {
            op: HirBinOp::Mul,
            left,
            right,
        } = &lhs.kind
        {
            let addend = self.hir_indexed_array_receiver(rhs)?;
            return Some((
                self.hir_indexed_array_receiver(left)?,
                self.hir_indexed_array_receiver(right)?,
                addend,
            ));
        }
        if let HirExprKind::Binary {
            op: HirBinOp::Mul,
            left,
            right,
        } = &rhs.kind
        {
            let addend = self.hir_indexed_array_receiver(lhs)?;
            return Some((
                self.hir_indexed_array_receiver(left)?,
                self.hir_indexed_array_receiver(right)?,
                addend,
            ));
        }
        None
    }

    fn hir_indexed_array_receiver<'a>(&self, expr: &'a HirExpr) -> Option<&'a HirExpr> {
        let HirExprKind::Index { receiver, index } = &expr.kind else {
            return None;
        };
        if !matches!(index.kind, HirExprKind::Local(_) | HirExprKind::Integer(_)) {
            return None;
        }
        Some(receiver.as_ref())
    }

    fn receiver_bound_requires_guard(&self, end: &HirExpr, receiver: &HirExpr, size: Option<usize>) -> Option<bool> {
        match (&end.kind, size) {
            (HirExprKind::Integer(value), Some(size)) if *value == size as i64 => Some(false),
            (HirExprKind::BuiltinCall { name, args }, _)
                if (name == "len" || name == "rt_array_len") && args.len() == 1 && args[0] == *receiver =>
            {
                Some(false)
            }
            (
                HirExprKind::MethodCall {
                    receiver: end_receiver,
                    method,
                    args,
                    ..
                },
                _,
            ) if method == "len" && args.is_empty() && end_receiver.as_ref() == receiver => Some(false),
            (HirExprKind::Integer(_), None) => None,
            (HirExprKind::Local(_), _) => Some(true),
            (HirExprKind::BuiltinCall { name, args }, _)
                if (name == "len" || name == "rt_array_len") && args.len() == 1 =>
            {
                Some(true)
            }
            (HirExprKind::MethodCall { method, args, .. }, _) if method == "len" && args.is_empty() => Some(true),
            _ => None,
        }
    }

    fn make_len_expr(&self, receiver: HirExpr) -> HirExpr {
        HirExpr {
            kind: HirExprKind::BuiltinCall {
                name: "rt_array_len".to_string(),
                args: vec![receiver],
            },
            ty: TypeId::I64,
        }
    }

    fn make_eq_expr(&self, left: HirExpr, right: HirExpr) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Binary {
                op: HirBinOp::Eq,
                left: Box::new(left),
                right: Box::new(right),
            },
            ty: TypeId::BOOL,
        }
    }

    fn make_bool_and(&self, left: HirExpr, right: HirExpr) -> HirExpr {
        HirExpr {
            kind: HirExprKind::Binary {
                op: HirBinOp::And,
                left: Box::new(left),
                right: Box::new(right),
            },
            ty: TypeId::BOOL,
        }
    }

    fn float_array_layout(&self, types: &hir::TypeRegistry, expr: &HirExpr) -> Option<(TypeId, Option<usize>)> {
        match types.get(expr.ty)? {
            HirType::Array {
                element: TypeId::F32,
                size,
            } => Some((TypeId::F32, *size)),
            HirType::Array {
                element: TypeId::F64,
                size,
            } => Some((TypeId::F64, *size)),
            _ => None,
        }
    }

    /// Process HIR module through architecture checks, verification, and MIR lowering.
    /// This is the common logic shared by both type_check_and_lower variants.
    fn process_hir_to_mir(&mut self, mut hir_module: hir::HirModule) -> Result<mir::MirModule, CompileError> {
        // Emit HIR if requested (LLM-friendly #886)
        if let Some(path) = &self.emit_hir {
            crate::ir_export::export_hir(&hir_module, path.as_deref()).map_err(|e| {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNSUPPORTED_FEATURE)
                    .with_help("ensure the HIR export feature is properly configured");
                CompileError::semantic_with_context(format!("HIR export failed: {}", e), ctx)
            })?;
        }

        // Check architecture rules if any are defined (#1026-1035)
        if !hir_module.arch_rules.is_empty() {
            let arch_config = crate::arch_rules::ArchRulesConfig::from_hir_rules(&hir_module.arch_rules);
            let checker = crate::arch_rules::ArchRulesChecker::new(arch_config);
            let violations = checker.check_module(&hir_module);

            if !violations.is_empty() {
                let msg = violations
                    .iter()
                    .map(|v| format!("Architecture violation: {}", v.message))
                    .collect::<Vec<_>>()
                    .join("\n");
                let ctx = ErrorContext::new()
                    .with_code(codes::INVALID_OPERATION)
                    .with_help("ensure your module structure complies with defined architecture rules");
                return Err(CompileError::semantic_with_context(msg, ctx));
            }
        }

        // Check verification constraints (#1840-1909)
        let mut verifier = VerificationChecker::new(self.verification_strict);
        verifier.check_module(&hir_module);

        if verifier.has_violations() {
            self.verification_violations = verifier.violations().to_vec();

            if self.verification_strict {
                let msg = verifier.error_messages().join("\n");
                return Err(crate::error::factory::verification_errors(&msg));
            } else {
                // Log warnings but continue
                for violation in verifier.violations() {
                    tracing::warn!("{}", violation);
                }
            }
        }

        self.emit_typed_explicit_simd_warnings(&hir_module);
        self.emit_typed_simd_report(&hir_module);
        self.rewrite_hir_simd_loops(&mut hir_module);

        // Lower HIR to MIR with contract mode, DI config, and coverage (#674)
        let di_config = self.project.as_ref().and_then(|p| p.di_config.clone());
        let mut mir_module = mir::lower_to_mir_full(&hir_module, self.contract_mode, di_config, self.coverage_enabled)
            .map_err(|e| crate::error::factory::mir_lowering_failed(&e))?;

        // Ghost erasure pass: remove ghost variables before codegen
        let (ghost_stats, ghost_errors) = mir::erase_ghost_from_module(&mut mir_module);

        if !ghost_errors.is_empty() {
            let msg = ghost_errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n");
            return Err(crate::error::factory::ghost_erasure_errors(&msg));
        }

        if ghost_stats.ghost_params_erased > 0 || ghost_stats.ghost_locals_erased > 0 {
            tracing::debug!(
                "Ghost erasure: {} params, {} locals, {} instructions erased",
                ghost_stats.ghost_params_erased,
                ghost_stats.ghost_locals_erased,
                ghost_stats.instructions_erased
            );
        }

        // Emit MIR if requested (LLM-friendly #887)
        if let Some(path) = &self.emit_mir {
            crate::ir_export::export_mir(&mir_module, path.as_deref()).map_err(|e| {
                let ctx = ErrorContext::new()
                    .with_code(codes::UNSUPPORTED_FEATURE)
                    .with_help("ensure the MIR export feature is properly configured");
                CompileError::semantic_with_context(format!("MIR export failed: {}", e), ctx)
            })?;
        }

        Ok(mir_module)
    }

    /// Type check and lower AST to MIR.
    ///
    /// This is a common pipeline step extracted from compile_source_to_memory_native
    /// and compile_source_to_memory_native_for_target.
    pub(super) fn type_check_and_lower(
        &mut self,
        ast_module: &simple_parser::ast::Module,
    ) -> Result<mir::MirModule, CompileError> {
        // Clear previous verification violations
        self.verification_violations.clear();
        self.emit_explicit_simd_warnings(ast_module);
        self.emit_simd_report(ast_module);

        // Type check (lenient - log errors but don't fail for bootstrap)
        if let Err(e) = type_check(&ast_module.items) {
            eprintln!("warning: type check: {:?} (continuing)", e);
        }

        // Lower AST to HIR (using lenient mode for bootstrap)
        let hir_module = hir::lower_lenient(ast_module).map_err(convert_lower_error)?;

        // Process HIR to MIR using common logic
        self.process_hir_to_mir(hir_module)
    }

    /// Type check and lower AST to MIR with module resolution support.
    ///
    /// This variant enables compile-time type checking for imports by loading
    /// type definitions from imported modules.
    ///
    /// # Arguments
    /// * `ast_module` - The AST module to lower
    /// * `source_file` - Path to the source file (for resolving relative imports)
    pub(super) fn type_check_and_lower_with_context(
        &mut self,
        ast_module: &simple_parser::ast::Module,
        source_file: &Path,
    ) -> Result<mir::MirModule, CompileError> {
        self.type_check_and_lower_with_context_and_project_hint(ast_module, source_file, None)
    }

    /// Type check and lower AST to MIR with module resolution support and an optional
    /// external project hint used for native single-file probes outside the repo tree.
    pub(super) fn type_check_and_lower_with_context_and_project_hint(
        &mut self,
        ast_module: &simple_parser::ast::Module,
        source_file: &Path,
        project_hint: Option<&Path>,
    ) -> Result<mir::MirModule, CompileError> {
        // Clear previous verification violations
        self.verification_violations.clear();
        self.emit_explicit_simd_warnings(ast_module);
        self.emit_simd_report(ast_module);

        // Type check (lenient - log errors but don't fail for bootstrap)
        if let Err(e) = type_check(&ast_module.items) {
            eprintln!("warning: type check: {:?} (continuing)", e);
        }

        // Lower AST to HIR with module resolution support (using lenient mode for bootstrap)
        let hir_module = hir::lower_with_context_lenient_and_project_hint(ast_module, source_file, project_hint)
            .map_err(convert_lower_error)?;

        // Process HIR to MIR using common logic
        self.process_hir_to_mir(hir_module)
    }

    /// Type check and lower AST to MIR with strict memory safety checking.
    ///
    /// This variant uses strict mode where memory safety warnings become errors.
    /// Use for production builds after bootstrap.
    #[allow(dead_code)] // reason: reachable via FFI or future entry point; not yet wired
    pub(super) fn type_check_and_lower_with_context_strict(
        &mut self,
        ast_module: &simple_parser::ast::Module,
        source_file: &Path,
    ) -> Result<mir::MirModule, CompileError> {
        self.type_check_and_lower_with_context_strict_and_project_hint(ast_module, source_file, None)
    }

    /// Strict lowering variant with an optional external project hint used for
    /// temp native probes compiled outside the repo tree.
    #[allow(dead_code)] // reason: reachable via FFI or future entry point; not yet wired
    pub(super) fn type_check_and_lower_with_context_strict_and_project_hint(
        &mut self,
        ast_module: &simple_parser::ast::Module,
        source_file: &Path,
        project_hint: Option<&Path>,
    ) -> Result<mir::MirModule, CompileError> {
        // Clear previous verification violations
        self.verification_violations.clear();
        self.emit_explicit_simd_warnings(ast_module);
        self.emit_simd_report(ast_module);

        // Type check (lenient - log errors but don't fail for bootstrap)
        if let Err(e) = type_check(&ast_module.items) {
            eprintln!("warning: type check: {:?} (continuing)", e);
        }

        // Lower AST to HIR with module resolution support (strict mode)
        let hir_module = hir::lower_with_context_and_project_hint(ast_module, source_file, project_hint)
            .map_err(convert_lower_error)?;

        // Process HIR to MIR using common logic
        self.process_hir_to_mir(hir_module)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::codegen::Codegen;
    use crate::import_loader::load_module_with_imports;
    use object::{Object, ObjectSymbol, SymbolKind, SymbolSection};
    use simple_parser::ast::Node;
    use std::collections::HashSet;
    use std::fs;
    use tempfile::tempdir_in;

    #[test]
    fn imported_static_methods_survive_lowering_with_context() {
        let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .canonicalize()
            .expect("repo root");
        let temp = tempdir_in(&repo_root).expect("tempdir in repo");
        let entry = temp.path().join("native_import_probe.spl");
        fs::write(
            &entry,
            "use app.svim.core.*\n\nfn main() -> i64:\n    var session = SvimSession.new()\n    session.execute_named(\"set-mode\", \"insert\", 1, \"\")\n    session.current_cursor().col\n",
        )
        .expect("write entry");

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).expect("load imports");
        let stripped = simple_parser::ast::Module {
            name: loaded.name,
            items: loaded
                .items
                .into_iter()
                .filter(|item| {
                    !matches!(
                        item,
                        Node::UseStmt(_)
                            | Node::MultiUse(_)
                            | Node::CommonUseStmt(_)
                            | Node::ExportUseStmt(_)
                            | Node::StructuredExportStmt(_)
                            | Node::AutoImportStmt(_)
                    )
                })
                .collect(),
        };

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        let mir = pipeline
            .type_check_and_lower_with_context(&stripped, &entry)
            .expect("lower with context");

        let imported = mir
            .functions
            .iter()
            .find(|func| func.name == "SvimSession.new")
            .expect("expected imported static method to be present in MIR");
        assert!(
            !imported.blocks.is_empty(),
            "expected imported static method to keep its body in MIR"
        );
    }

    #[test]
    fn native_object_defines_imported_static_method_symbol() {
        let repo_root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("..")
            .canonicalize()
            .expect("repo root");
        let temp = tempdir_in(&repo_root).expect("tempdir in repo");
        let entry = temp.path().join("native_import_probe.spl");
        fs::write(
            &entry,
            "use app.svim.core.*\n\nfn main() -> i64:\n    var session = SvimSession.new()\n    session.execute_named(\"set-mode\", \"insert\", 1, \"\")\n    session.current_cursor().col\n",
        )
        .expect("write entry");

        let loaded = load_module_with_imports(&entry, &mut HashSet::new()).expect("load imports");
        let stripped = simple_parser::ast::Module {
            name: loaded.name,
            items: loaded
                .items
                .into_iter()
                .filter(|item| {
                    !matches!(
                        item,
                        Node::UseStmt(_)
                            | Node::MultiUse(_)
                            | Node::CommonUseStmt(_)
                            | Node::ExportUseStmt(_)
                            | Node::StructuredExportStmt(_)
                            | Node::AutoImportStmt(_)
                    )
                })
                .collect(),
        };

        let mut pipeline = CompilerPipeline::new().expect("pipeline");
        let mir = pipeline
            .type_check_and_lower_with_context(&stripped, &entry)
            .expect("lower with context");

        let mut codegen = Codegen::for_target(simple_common::target::Target::host()).expect("codegen");
        codegen.set_entry_module(true);
        let object = codegen.compile_module(&mir).expect("compile object");
        let file = object::File::parse(&*object).expect("parse object");

        let all_symbols: Vec<String> = file
            .symbols()
            .filter_map(|symbol| symbol.name().ok().map(|name| name.to_string()))
            .collect();
        let symbol = file
            .symbols()
            .find(|symbol| symbol.name().ok() == Some("SvimSession_dot_new"))
            .unwrap_or_else(|| {
                let related: Vec<String> = all_symbols
                    .iter()
                    .filter(|name| name.contains("SvimSession") || name.contains("session"))
                    .cloned()
                    .collect();
                panic!("SvimSession_dot_new symbol missing; related symbols: {:?}", related);
            });
        assert_eq!(symbol.kind(), SymbolKind::Text, "expected text symbol");
        assert!(
            !matches!(symbol.section(), SymbolSection::Undefined),
            "expected imported static method symbol to be defined in the object"
        );
    }
}
