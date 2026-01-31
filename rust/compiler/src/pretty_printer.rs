//! AST-based pretty printer for Simple language.
//!
//! This module provides proper code formatting by traversing the AST
//! instead of using text-based heuristics.

use simple_parser::ast::*;
use simple_parser::token::{NumericSuffix, Span};

/// Pretty printer configuration
#[derive(Debug, Clone)]
pub struct PrettyConfig {
    pub indent_size: usize,
    pub max_line_length: usize,
}

impl Default for PrettyConfig {
    fn default() -> Self {
        Self {
            indent_size: 4,
            max_line_length: 100,
        }
    }
}

/// Pretty printer for AST nodes
pub struct PrettyPrinter {
    config: PrettyConfig,
    indent_level: usize,
    output: String,
}

impl PrettyPrinter {
    pub fn new(config: PrettyConfig) -> Self {
        Self {
            config,
            indent_level: 0,
            output: String::new(),
        }
    }

    pub fn with_default() -> Self {
        Self::new(PrettyConfig::default())
    }

    /// Get the current indentation string
    fn indent(&self) -> String {
        " ".repeat(self.indent_level * self.config.indent_size)
    }

    /// Write a line with current indentation
    fn write_line(&mut self, text: &str) {
        self.output.push_str(&self.indent());
        self.output.push_str(text);
        self.output.push('\n');
    }

    /// Write text without indentation
    fn write(&mut self, text: &str) {
        self.output.push_str(text);
    }

    /// Write indentation only
    fn write_indent(&mut self) {
        self.output.push_str(&self.indent());
    }

    /// Increase indentation level
    fn indent_inc(&mut self) {
        self.indent_level += 1;
    }

    /// Decrease indentation level
    fn indent_dec(&mut self) {
        if self.indent_level > 0 {
            self.indent_level -= 1;
        }
    }

    /// Pretty print a module
    pub fn print_module(&mut self, module: &Module) -> String {
        // Reset state
        self.output.clear();
        self.indent_level = 0;

        // Module doesn't have a doc field, so skip doc comment

        // Print module items with appropriate spacing
        for (i, item) in module.items.iter().enumerate() {
            if i > 0 {
                // Add blank line between top-level items
                self.output.push('\n');
            }
            self.print_node(item);
        }

        self.output.clone()
    }

    /// Pretty print a single AST node
    pub fn print_node(&mut self, node: &Node) {
        match node {
            Node::Function(f) => self.print_function(f),
            Node::Struct(s) => self.print_struct(s),
            Node::Class(c) => self.print_class(c),
            Node::Enum(e) => self.print_enum(e),
            Node::Trait(t) => self.print_trait(t),
            Node::Impl(i) => self.print_impl(i),
            Node::Let(l) => self.print_let(l),
            Node::Const(c) => self.print_const(c),
            Node::Assignment(a) => self.print_assignment(a),
            Node::Return(r) => self.print_return(r),
            Node::If(i) => self.print_if(i),
            Node::Match(m) => self.print_match(m),
            Node::For(f) => self.print_for(f),
            Node::While(w) => self.print_while(w),
            Node::Loop(l) => self.print_loop(l),
            Node::Break(b) => self.print_break(b),
            Node::Continue(c) => self.print_continue(c),
            Node::Pass(_) => self.write_line("pass"),
            Node::Skip(skip_stmt) => match &skip_stmt.body {
                SkipBody::Standalone => self.write_line("skip"),
                SkipBody::Block(block) => {
                    self.write_line("skip:");
                    self.indent_level += 1;
                    for stmt in &block.statements {
                        self.print_node(stmt);
                    }
                    self.indent_level -= 1;
                }
            },
            Node::Expression(e) => {
                self.write_indent();
                self.print_expr(e);
                self.output.push('\n');
            }
            Node::UseStmt(u) => self.print_use(u),
            Node::ModDecl(m) => self.print_mod_decl(m),
            _ => {
                // TODO: Implement other node types
                self.write_line(&format!("# TODO: Pretty print {:?}", node));
            }
        }
    }

    fn print_doc_comment(&mut self, doc: &DocComment) {
        self.write_line("\"\"\"");
        for line in doc.content.lines() {
            self.write_line(line);
        }
        self.write_line("\"\"\"");
        self.output.push('\n');
    }

    fn print_function(&mut self, func: &FunctionDef) {
        // Doc comment
        if let Some(ref doc) = func.doc_comment {
            self.print_doc_comment(doc);
        }

        // Decorators
        for decorator in &func.decorators {
            self.write_indent();
            self.write("@");
            self.print_expr(&decorator.name);
            self.output.push('\n');
        }

        // Function signature
        self.write_indent();

        // Static keyword
        if func.is_static {
            self.write("static ");
        }

        // Function keyword (or `me` for mutable methods)
        if func.is_me_method {
            self.write("me ");
        } else {
            self.write("fn ");
        }
        self.write(&func.name);

        // Type parameters (generic_params are Vec<String>)
        if !func.generic_params.is_empty() {
            self.write("<");
            for (i, param) in func.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write(">");
        }

        // Parameters
        self.write("(");
        for (i, param) in func.params.iter().enumerate() {
            if i > 0 {
                self.write(", ");
            }
            self.print_param(param);
        }
        self.write(")");

        // Return type
        if let Some(ref ret_type) = func.return_type {
            self.write(" -> ");
            self.print_type(ret_type);
        }

        self.write(":");
        self.output.push('\n');

        // Body
        self.indent_inc();
        if func.body.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &func.body.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();
    }

    fn print_struct(&mut self, struct_def: &StructDef) {
        if let Some(ref doc) = struct_def.doc_comment {
            self.print_doc_comment(doc);
        }

        self.write_indent();
        self.write("struct ");
        self.write(&struct_def.name);

        // Type parameters (generic_params are Vec<String>)
        if !struct_def.generic_params.is_empty() {
            self.write("<");
            for (i, param) in struct_def.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write(">");
        }

        self.write(":");
        self.output.push('\n');

        // Fields
        self.indent_inc();
        for field in &struct_def.fields {
            self.print_field(field);
        }
        self.indent_dec();
    }

    fn print_class(&mut self, class_def: &ClassDef) {
        if let Some(ref doc) = class_def.doc_comment {
            self.print_doc_comment(doc);
        }

        self.write_indent();
        self.write("class ");
        self.write(&class_def.name);

        // Type parameters (generic_params are Vec<String>)
        if !class_def.generic_params.is_empty() {
            self.write("<");
            for (i, param) in class_def.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write(">");
        }

        self.write(":");
        self.output.push('\n');

        // Fields and methods
        self.indent_inc();

        // Fields first
        for field in &class_def.fields {
            self.print_field(field);
        }

        // Methods
        if !class_def.methods.is_empty() {
            if !class_def.fields.is_empty() {
                self.output.push('\n');
            }
            for method in &class_def.methods {
                self.print_function(method);
                self.output.push('\n');
            }
        }

        self.indent_dec();
    }

    fn print_enum(&mut self, enum_def: &EnumDef) {
        if let Some(ref doc) = enum_def.doc_comment {
            self.print_doc_comment(doc);
        }

        self.write_indent();
        self.write("enum ");
        self.write(&enum_def.name);

        // Type parameters (generic_params are Vec<String>)
        if !enum_def.generic_params.is_empty() {
            self.write("<");
            for (i, param) in enum_def.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write(">");
        }

        self.write(":");
        self.output.push('\n');

        // Variants
        self.indent_inc();
        for variant in &enum_def.variants {
            self.print_enum_variant(variant);
        }
        self.indent_dec();
    }

    fn print_trait(&mut self, trait_def: &TraitDef) {
        if let Some(ref doc) = trait_def.doc_comment {
            self.print_doc_comment(doc);
        }

        self.write_indent();
        self.write("trait ");
        self.write(&trait_def.name);

        // Type parameters (generic_params are Vec<String>)
        if !trait_def.generic_params.is_empty() {
            self.write("<");
            for (i, param) in trait_def.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write(">");
        }

        self.write(":");
        self.output.push('\n');

        // Methods
        self.indent_inc();
        for method in &trait_def.methods {
            self.print_function(method);
            self.output.push('\n');
        }
        self.indent_dec();
    }

    fn print_impl(&mut self, impl_block: &ImplBlock) {
        self.write_indent();
        self.write("impl ");

        // Type parameters (generic_params are Vec<String>)
        if !impl_block.generic_params.is_empty() {
            self.write("<");
            for (i, param) in impl_block.generic_params.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                self.write(param);
            }
            self.write("> ");
        }

        self.print_type(&impl_block.target_type);

        if let Some(ref trait_name) = impl_block.trait_name {
            self.write(" for ");
            self.write(trait_name);
        }

        self.write(":");
        self.output.push('\n');

        // Methods
        self.indent_inc();
        for method in &impl_block.methods {
            self.print_function(method);
            self.output.push('\n');
        }
        self.indent_dec();
    }

    fn print_let(&mut self, let_stmt: &LetStmt) {
        self.write_indent();
        self.write(match let_stmt.mutability {
            Mutability::Mutable => "var ",
            Mutability::Immutable => "val ",
        });

        // Print pattern (for now, just handle simple identifier patterns)
        self.print_pattern(&let_stmt.pattern);

        if let Some(ref type_ann) = let_stmt.ty {
            self.write(": ");
            self.print_type(type_ann);
        }

        if let Some(ref value) = let_stmt.value {
            self.write(" = ");
            self.print_expr(value);
        }

        self.output.push('\n');
    }

    fn print_const(&mut self, const_stmt: &ConstStmt) {
        self.write_indent();
        self.write("const ");
        self.write(&const_stmt.name);

        if let Some(ref type_ann) = const_stmt.ty {
            self.write(": ");
            self.print_type(type_ann);
        }

        self.write(" = ");
        self.print_expr(&const_stmt.value);
        self.output.push('\n');
    }

    fn print_assignment(&mut self, assign: &AssignmentStmt) {
        self.write_indent();
        self.print_expr(&assign.target);
        self.write(" = ");
        self.print_expr(&assign.value);
        self.output.push('\n');
    }

    fn print_return(&mut self, ret: &ReturnStmt) {
        self.write_indent();
        self.write("return");
        if let Some(ref value) = ret.value {
            self.write(" ");
            self.print_expr(value);
        }
        self.output.push('\n');
    }

    fn print_if(&mut self, if_stmt: &IfStmt) {
        self.write_indent();
        self.write("if ");
        self.print_expr(&if_stmt.condition);
        self.write(":");
        self.output.push('\n');

        // Then block
        self.indent_inc();
        if if_stmt.then_block.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &if_stmt.then_block.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();

        // Else block
        if let Some(ref else_block) = if_stmt.else_block {
            self.write_line("else:");
            self.indent_inc();
            if else_block.statements.is_empty() {
                self.write_line("pass");
            } else {
                for node in &else_block.statements {
                    self.print_node(node);
                }
            }
            self.indent_dec();
        }
    }

    fn print_match(&mut self, match_stmt: &MatchStmt) {
        self.write_indent();
        self.write("match ");
        self.print_expr(&match_stmt.subject);
        self.write(":");
        self.output.push('\n');

        self.indent_inc();
        for arm in &match_stmt.arms {
            self.print_match_arm(arm);
        }
        self.indent_dec();
    }

    fn print_match_arm(&mut self, arm: &MatchArm) {
        self.write_indent();
        self.write("case ");
        self.print_pattern(&arm.pattern);

        if let Some(ref guard) = arm.guard {
            self.write(" if ");
            self.print_expr(guard);
        }

        self.write(":");
        self.output.push('\n');

        self.indent_inc();
        if arm.body.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &arm.body.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();
    }

    fn print_for(&mut self, for_stmt: &ForStmt) {
        self.write_indent();
        self.write("for ");
        self.print_pattern(&for_stmt.pattern);
        self.write(" in ");
        self.print_expr(&for_stmt.iterable);
        self.write(":");
        self.output.push('\n');

        self.indent_inc();
        if for_stmt.body.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &for_stmt.body.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();
    }

    fn print_while(&mut self, while_stmt: &WhileStmt) {
        self.write_indent();
        self.write("while ");
        self.print_expr(&while_stmt.condition);
        self.write(":");
        self.output.push('\n');

        self.indent_inc();
        if while_stmt.body.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &while_stmt.body.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();
    }

    fn print_loop(&mut self, loop_stmt: &LoopStmt) {
        self.write_line("loop:");

        self.indent_inc();
        if loop_stmt.body.statements.is_empty() {
            self.write_line("pass");
        } else {
            for node in &loop_stmt.body.statements {
                self.print_node(node);
            }
        }
        self.indent_dec();
    }

    fn print_break(&mut self, break_stmt: &BreakStmt) {
        self.write_indent();
        self.write("break");
        if let Some(ref value) = break_stmt.value {
            self.write(" ");
            self.print_expr(value);
        }
        self.output.push('\n');
    }

    fn print_continue(&mut self, _: &ContinueStmt) {
        self.write_line("continue");
    }

    fn print_use(&mut self, use_stmt: &UseStmt) {
        self.write_indent();
        self.write("use ");
        // ModulePath has segments: Vec<String>
        self.write(&use_stmt.path.segments.join("::"));
        self.output.push('\n');
    }

    fn print_mod_decl(&mut self, mod_decl: &ModDecl) {
        self.write_indent();
        self.write("mod ");
        self.write(&mod_decl.name);
        self.output.push('\n');
    }

    fn print_field(&mut self, field: &Field) {
        self.write_indent();
        self.write(&field.name);
        self.write(": ");
        self.print_type(&field.ty);
        self.output.push('\n');
    }

    fn print_enum_variant(&mut self, variant: &EnumVariant) {
        self.write_indent();
        self.write(&variant.name);

        if let Some(ref fields) = variant.fields {
            self.write("(");
            for (i, field) in fields.iter().enumerate() {
                if i > 0 {
                    self.write(", ");
                }
                if let Some(ref name) = field.name {
                    self.write(name);
                    self.write(": ");
                }
                self.print_type(&field.ty);
            }
            self.write(")");
        }

        self.output.push('\n');
    }

    // Type parameters are now just strings, so this method is not needed
    // We print them directly in the calling code

    fn print_param(&mut self, param: &Parameter) {
        self.write(&param.name);
        if let Some(ref type_ann) = param.ty {
            self.write(": ");
            self.print_type(type_ann);
        }
        if let Some(ref default) = param.default {
            self.write(" = ");
            self.print_expr(default);
        }
    }

    fn print_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Identifier(name) => self.write(name),
            Pattern::MutIdentifier(name) => {
                self.write("mut ");
                self.write(name);
            }
            Pattern::MoveIdentifier(name) => {
                self.write("move ");
                self.write(name);
            }
            Pattern::Wildcard => self.write("_"),
            Pattern::Literal(expr) => self.print_expr(expr),
            Pattern::Tuple(patterns) => {
                self.write("(");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_pattern(p);
                }
                self.write(")");
            }
            Pattern::Array(patterns) => {
                self.write("[");
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_pattern(p);
                }
                self.write("]");
            }
            Pattern::Struct { name, fields } => {
                self.write(name);
                self.write(" { ");
                for (i, (field_name, field_pattern)) in fields.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(field_name);
                    self.write(": ");
                    self.print_pattern(field_pattern);
                }
                self.write(" }");
            }
            Pattern::Enum { name, variant, payload } => {
                self.write(name);
                self.write("::");
                self.write(variant);
                if let Some(patterns) = payload {
                    self.write("(");
                    for (i, p) in patterns.iter().enumerate() {
                        if i > 0 {
                            self.write(", ");
                        }
                        self.print_pattern(p);
                    }
                    self.write(")");
                }
            }
            Pattern::Or(patterns) => {
                for (i, p) in patterns.iter().enumerate() {
                    if i > 0 {
                        self.write(" | ");
                    }
                    self.print_pattern(p);
                }
            }
            Pattern::Typed { pattern, ty } => {
                self.print_pattern(pattern);
                self.write(": ");
                self.print_type(ty);
            }
            Pattern::Range { start, end, inclusive } => {
                self.print_expr(start);
                if *inclusive {
                    self.write("..=");
                } else {
                    self.write("..");
                }
                self.print_expr(end);
            }
            Pattern::Rest => self.write("..."),
        }
    }

    fn print_type(&mut self, ty: &Type) {
        match ty {
            Type::Simple(name) => self.write(name),
            Type::Generic { name, args } => {
                self.write(name);
                self.write("<");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_type(arg);
                }
                self.write(">");
            }
            Type::Capability { capability, inner } => {
                self.write(&format!("{:?}", capability));
                self.write(" ");
                self.print_type(inner);
            }
            Type::Pointer { kind, inner } => {
                self.write(&format!("{:?}", kind));
                self.write(" ");
                self.print_type(inner);
            }
            Type::Function { params, ret } => {
                self.write("fn(");
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_type(param);
                }
                self.write(")");
                if let Some(ret_type) = ret {
                    self.write(" -> ");
                    self.print_type(ret_type);
                }
            }
            Type::Tuple(elements) => {
                self.write("(");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_type(elem);
                }
                self.write(")");
            }
            Type::Optional(inner) => {
                self.print_type(inner);
                self.write("?");
            }
            Type::Array { element, size } => {
                self.write("[");
                self.print_type(element);
                if let Some(size_expr) = size {
                    self.write("; ");
                    self.print_expr(size_expr);
                }
                self.write("]");
            }
            Type::Union(types) => {
                for (i, t) in types.iter().enumerate() {
                    if i > 0 {
                        self.write(" | ");
                    }
                    self.print_type(t);
                }
            }
            Type::DynTrait(name) => {
                self.write("dyn ");
                self.write(name);
            }
            _ => self.write("/* unknown type */"),
        }
    }

    fn print_expr(&mut self, expr: &Expr) {
        match expr {
            Expr::Identifier(name) => self.write(name),
            Expr::Integer(n) => {
                self.write(&n.to_string());
            }
            Expr::TypedInteger(n, suffix) => {
                self.write(&n.to_string());
                match suffix {
                    NumericSuffix::I8 => self.write("i8"),
                    NumericSuffix::I16 => self.write("i16"),
                    NumericSuffix::I32 => self.write("i32"),
                    NumericSuffix::I64 => self.write("i64"),
                    NumericSuffix::U8 => self.write("u8"),
                    NumericSuffix::U16 => self.write("u16"),
                    NumericSuffix::U32 => self.write("u32"),
                    NumericSuffix::U64 => self.write("u64"),
                    NumericSuffix::F32 => self.write("f32"),
                    NumericSuffix::F64 => self.write("f64"),
                    NumericSuffix::Unit(unit) => {
                        self.write("_");
                        self.write(unit);
                    }
                }
            }
            Expr::Float(f) => {
                self.write(&f.to_string());
            }
            Expr::TypedFloat(f, suffix) => {
                self.write(&f.to_string());
                match suffix {
                    NumericSuffix::F32 => self.write("f32"),
                    NumericSuffix::F64 => self.write("f64"),
                    NumericSuffix::Unit(unit) => {
                        self.write("_");
                        self.write(unit);
                    }
                    _ => {}
                }
            }
            Expr::String(s) => {
                self.write("\"");
                self.write(&s.replace('"', "\\\""));
                self.write("\"");
            }
            Expr::Bool(b) => self.write(if *b { "true" } else { "false" }),
            Expr::Array(elements) => {
                self.write("[");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem);
                }
                self.write("]");
            }
            Expr::Dict(entries) => {
                self.write("{");
                for (i, (key, value)) in entries.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(key);
                    self.write(": ");
                    self.print_expr(value);
                }
                self.write("}");
            }
            Expr::Tuple(elements) => {
                self.write("(");
                for (i, elem) in elements.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.print_expr(elem);
                }
                self.write(")");
            }
            Expr::Binary { left, op, right, .. } => {
                use simple_parser::ast::BinOp;
                self.print_expr(left);
                self.write(" ");
                self.write(match op {
                    BinOp::Add => "+", BinOp::Sub => "-", BinOp::Mul => "*",
                    BinOp::Div => "/", BinOp::Mod => "%", BinOp::Pow => "**",
                    BinOp::MatMul => "@",
                    BinOp::Eq => "==", BinOp::NotEq => "!=",
                    BinOp::Lt => "<", BinOp::Gt => ">",
                    BinOp::LtEq => "<=", BinOp::GtEq => ">=",
                    BinOp::And => "and", BinOp::Or => "or",
                    BinOp::AndSuspend => "and~", BinOp::OrSuspend => "or~",
                    BinOp::BitAnd => "&", BinOp::BitOr => "|", BinOp::BitXor => "xor",
                    BinOp::ShiftLeft => "<<", BinOp::ShiftRight => ">>",
                    BinOp::Is => "is", BinOp::In => "in", BinOp::NotIn => "not in",
                    BinOp::PipeForward => "|>", BinOp::Parallel => "//",
                });
                self.write(" ");
                self.print_expr(right);
            }
            Expr::Unary { op, operand, .. } => {
                use simple_parser::ast::UnaryOp;
                self.write(match op {
                    UnaryOp::Neg => "-", UnaryOp::Not => "not ",
                    UnaryOp::BitNot => "~", UnaryOp::Ref => "&",
                    UnaryOp::RefMut => "&mut ", UnaryOp::Deref => "*",
                    UnaryOp::ChannelRecv => "<-", UnaryOp::Move => "move ",
                });
                self.print_expr(operand);
            }
            Expr::Call { callee, args } => {
                self.print_expr(callee);
                self.write("(");
                for (i, arg) in args.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    if let Some(ref name) = arg.name {
                        self.write(name);
                        self.write(": ");
                    }
                    self.print_expr(&arg.value);
                }
                self.write(")");
            }
            Expr::FieldAccess { receiver, field } => {
                self.print_expr(receiver);
                self.write(".");
                self.write(field);
            }
            Expr::Index { receiver, index } => {
                self.print_expr(receiver);
                self.write("[");
                self.print_expr(index);
                self.write("]");
            }
            Expr::Lambda { params, body, .. } => {
                self.write("\\");
                for (i, param) in params.iter().enumerate() {
                    if i > 0 {
                        self.write(", ");
                    }
                    self.write(&param.name);
                    if let Some(ref ty) = param.ty {
                        self.write(": ");
                        self.print_type(ty);
                    }
                }
                self.write(": ");
                self.print_expr(body);
            }
            _ => self.write("/* complex expr */"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::Parser;

    #[test]
    fn test_pretty_print_function() {
        let source = "fn add(a: i32, b: i32) -> i32:\n    return a + b";
        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();

        let mut printer = PrettyPrinter::with_default();
        let output = printer.print_module(&module);

        assert!(output.contains("fn add"));
        // Parser may represent return as implicit (last expr) or explicit
        assert!(output.contains("a + b"), "output was: {}", output);
    }

    #[test]
    fn test_pretty_print_class() {
        let source = "class Point:\n    x: i32\n    y: i32";
        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();

        let mut printer = PrettyPrinter::with_default();
        let output = printer.print_module(&module);

        assert!(output.contains("class Point"));
        assert!(output.contains("x: i32"));
        assert!(output.contains("y: i32"));
    }
}
