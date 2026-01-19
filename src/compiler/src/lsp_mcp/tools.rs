//! LSP MCP Tool Implementations

use crate::lsp_mcp::types::*;
use simple_parser::ast::{Block, ClassDef, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef, Type};
use simple_parser::token::Span;
use simple_parser::Parser;
use std::collections::HashMap;
use std::path::Path;

/// LSP MCP Tools - provides code intelligence operations
pub struct LspMcpTools {
    file_cache: HashMap<String, Vec<Node>>,
    source_cache: HashMap<String, String>,
}

impl Default for LspMcpTools {
    fn default() -> Self {
        Self::new()
    }
}

impl LspMcpTools {
    pub fn new() -> Self {
        Self {
            file_cache: HashMap::new(),
            source_cache: HashMap::new(),
        }
    }

    fn parse_and_cache(&mut self, path: &str, source: &str) -> Result<Vec<Node>, String> {
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => {
                self.source_cache.insert(path.to_string(), source.to_string());
                let items = module.items;
                self.file_cache.insert(path.to_string(), items.clone());
                Ok(items)
            }
            Err(e) => Err(e.to_string()),
        }
    }

    fn get_or_parse(&mut self, path: &str, source: &str) -> Result<Vec<Node>, String> {
        if let Some(cached) = self.file_cache.get(path) {
            return Ok(cached.clone());
        }
        self.parse_and_cache(path, source)
    }

    pub fn invalidate(&mut self, path: &str) {
        self.file_cache.remove(path);
        self.source_cache.remove(path);
    }

    pub fn go_to_definition(&mut self, path: &str, source: &str, line: u32, character: u32) -> Option<Location> {
        let nodes = self.get_or_parse(path, source).ok()?;
        let symbol_name = find_symbol_at_position(source, line, character)?;
        find_definition_in_nodes(&nodes, &symbol_name, path)
    }

    pub fn find_references(
        &mut self,
        path: &str,
        source: &str,
        line: u32,
        character: u32,
        include_declaration: bool,
    ) -> Vec<ReferenceLocation> {
        let mut references = Vec::new();
        let nodes = match self.get_or_parse(path, source) {
            Ok(n) => n,
            Err(_) => return references,
        };
        let symbol_name = match find_symbol_at_position(source, line, character) {
            Some(name) => name,
            None => return references,
        };
        if include_declaration {
            if let Some(def_loc) = find_definition_in_nodes(&nodes, &symbol_name, path) {
                references.push(ReferenceLocation::definition(def_loc.uri, def_loc.range));
            }
        }
        collect_references_in_nodes(&nodes, &symbol_name, path, &mut references);
        references
    }

    pub fn hover(&mut self, path: &str, source: &str, line: u32, character: u32) -> Option<HoverInfo> {
        let nodes = self.get_or_parse(path, source).ok()?;
        let symbol_name = find_symbol_at_position(source, line, character)?;
        generate_hover_info(&nodes, &symbol_name)
    }

    pub fn document_symbols(&mut self, path: &str, source: &str) -> Vec<SymbolInfo> {
        let nodes = match self.get_or_parse(path, source) {
            Ok(n) => n,
            Err(_) => return Vec::new(),
        };
        extract_symbols_from_nodes(&nodes)
    }

    pub fn diagnostics(&mut self, path: &str, source: &str, include_warnings: bool) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => {
                self.source_cache.insert(path.to_string(), source.to_string());
                self.file_cache.insert(path.to_string(), module.items.clone());
                if include_warnings {
                    collect_semantic_warnings(&module.items, &mut diagnostics);
                }
            }
            Err(err) => {
                let span = err.span().unwrap_or_else(|| Span::new(0, 1, 1, 1));
                let range = Range::from_span(span.line, span.column, span.line, span.column + (span.end - span.start));
                diagnostics.push(Diagnostic::error(range, err.to_string()));
            }
        }
        diagnostics
    }
}

fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

fn find_symbol_at_position(source: &str, line: u32, character: u32) -> Option<String> {
    let lines: Vec<&str> = source.lines().collect();
    let line_idx = line as usize;
    if line_idx >= lines.len() {
        return None;
    }
    let line_text = lines[line_idx];
    let char_idx = character as usize;
    if char_idx >= line_text.len() {
        return None;
    }
    let chars: Vec<char> = line_text.chars().collect();
    let mut start = char_idx;
    while start > 0 && is_identifier_char(chars[start - 1]) {
        start -= 1;
    }
    let mut end = char_idx;
    while end < chars.len() && is_identifier_char(chars[end]) {
        end += 1;
    }
    if start == end {
        return None;
    }
    Some(chars[start..end].iter().collect())
}

fn find_definition_in_nodes(nodes: &[Node], name: &str, file_path: &str) -> Option<Location> {
    let uri = file_uri(file_path);
    for node in nodes {
        match node {
            Node::Function(func) if func.name == name => {
                return Some(Location::new(&uri, span_to_range(&func.span)));
            }
            Node::Class(class) if class.name == name => {
                return Some(Location::new(&uri, span_to_range(&class.span)));
            }
            Node::Struct(s) if s.name == name => {
                return Some(Location::new(&uri, span_to_range(&s.span)));
            }
            Node::Enum(e) if e.name == name => {
                return Some(Location::new(&uri, span_to_range(&e.span)));
            }
            Node::Trait(t) if t.name == name => {
                return Some(Location::new(&uri, span_to_range(&t.span)));
            }
            Node::Class(class) => {
                for method in &class.methods {
                    if method.name == name {
                        return Some(Location::new(&uri, span_to_range(&method.span)));
                    }
                }
            }
            Node::Let(let_stmt) => {
                if let Some(pattern_name) = extract_pattern_name(&let_stmt.pattern) {
                    if pattern_name == name {
                        return Some(Location::new(&uri, span_to_range(&let_stmt.span)));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn collect_references_in_nodes(nodes: &[Node], name: &str, file_path: &str, references: &mut Vec<ReferenceLocation>) {
    let uri = file_uri(file_path);
    for node in nodes {
        collect_references_in_node(node, name, &uri, references);
    }
}

fn collect_references_in_node(node: &Node, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
    match node {
        Node::Function(func) => {
            collect_references_in_block(&func.body, name, uri, references);
        }
        Node::Class(class) => {
            for method in &class.methods {
                collect_references_in_block(&method.body, name, uri, references);
            }
        }
        Node::Expression(expr) => {
            collect_references_in_expr(expr, name, uri, references);
        }
        Node::Let(let_stmt) => {
            if let Some(value) = &let_stmt.value {
                collect_references_in_expr(value, name, uri, references);
            }
        }
        Node::Assignment(assign) => {
            collect_references_in_expr(&assign.target, name, uri, references);
            collect_references_in_expr(&assign.value, name, uri, references);
        }
        Node::If(if_stmt) => {
            collect_references_in_expr(&if_stmt.condition, name, uri, references);
            collect_references_in_block(&if_stmt.then_block, name, uri, references);
            if let Some(else_block) = &if_stmt.else_block {
                collect_references_in_block(else_block, name, uri, references);
            }
        }
        Node::While(while_stmt) => {
            collect_references_in_expr(&while_stmt.condition, name, uri, references);
            collect_references_in_block(&while_stmt.body, name, uri, references);
        }
        Node::For(for_stmt) => {
            collect_references_in_expr(&for_stmt.iterable, name, uri, references);
            collect_references_in_block(&for_stmt.body, name, uri, references);
        }
        Node::Return(ret_stmt) => {
            if let Some(value) = &ret_stmt.value {
                collect_references_in_expr(value, name, uri, references);
            }
        }
        _ => {}
    }
}

fn collect_references_in_block(block: &Block, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
    for stmt in &block.statements {
        collect_references_in_node(stmt, name, uri, references);
    }
}

fn collect_references_in_expr(expr: &Expr, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
    match expr {
        Expr::Identifier(ident) if ident == name => {
            let range = Range::single_line(0, 0, name.len() as u32);
            references.push(ReferenceLocation::reference(uri.to_string(), range));
        }
        Expr::Call { callee, args } => {
            collect_references_in_expr(callee, name, uri, references);
            for arg in args {
                collect_references_in_expr(&arg.value, name, uri, references);
            }
        }
        Expr::MethodCall { receiver, args, .. } => {
            collect_references_in_expr(receiver, name, uri, references);
            for arg in args {
                collect_references_in_expr(&arg.value, name, uri, references);
            }
        }
        Expr::Binary { left, right, .. } => {
            collect_references_in_expr(left, name, uri, references);
            collect_references_in_expr(right, name, uri, references);
        }
        Expr::Unary { operand, .. } => {
            collect_references_in_expr(operand, name, uri, references);
        }
        Expr::FieldAccess { receiver, .. } => {
            collect_references_in_expr(receiver, name, uri, references);
        }
        Expr::Index { receiver, index } => {
            collect_references_in_expr(receiver, name, uri, references);
            collect_references_in_expr(index, name, uri, references);
        }
        Expr::Array(elements) => {
            for elem in elements {
                collect_references_in_expr(elem, name, uri, references);
            }
        }
        Expr::Tuple(elements) => {
            for elem in elements {
                collect_references_in_expr(elem, name, uri, references);
            }
        }
        Expr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_references_in_expr(condition, name, uri, references);
            collect_references_in_expr(then_branch, name, uri, references);
            if let Some(else_br) = else_branch {
                collect_references_in_expr(else_br, name, uri, references);
            }
        }
        Expr::Lambda { body, .. } => {
            collect_references_in_expr(body, name, uri, references);
        }
        Expr::Await(future) => {
            collect_references_in_expr(future, name, uri, references);
        }
        Expr::StructInit { fields, .. } => {
            for (_, value) in fields {
                collect_references_in_expr(value, name, uri, references);
            }
        }
        _ => {}
    }
}

fn generate_hover_info(nodes: &[Node], name: &str) -> Option<HoverInfo> {
    for node in nodes {
        match node {
            Node::Function(func) if func.name == name => {
                let sig = format_function_signature(func);
                let markdown = format!("```simple\n{}\n```", sig);
                return Some(HoverInfo::new(HoverContents::markdown(markdown)));
            }
            Node::Class(class) if class.name == name => {
                let sig = format_class_signature(class);
                let markdown = format!("```simple\n{}\n```", sig);
                return Some(HoverInfo::new(HoverContents::markdown(markdown)));
            }
            Node::Struct(s) if s.name == name => {
                let sig = format_struct_signature(s);
                let markdown = format!("```simple\n{}\n```", sig);
                return Some(HoverInfo::new(HoverContents::markdown(markdown)));
            }
            Node::Enum(e) if e.name == name => {
                let sig = format_enum_signature(e);
                let markdown = format!("```simple\n{}\n```", sig);
                return Some(HoverInfo::new(HoverContents::markdown(markdown)));
            }
            Node::Trait(t) if t.name == name => {
                let sig = format_trait_signature(t);
                let markdown = format!("```simple\n{}\n```", sig);
                return Some(HoverInfo::new(HoverContents::markdown(markdown)));
            }
            Node::Class(class) => {
                for method in &class.methods {
                    if method.name == name {
                        let sig = format_function_signature(method);
                        let markdown = format!("```simple\n{}\n```\n\nMethod of `{}`", sig, class.name);
                        return Some(HoverInfo::new(HoverContents::markdown(markdown)));
                    }
                }
            }
            _ => {}
        }
    }
    None
}

fn extract_symbols_from_nodes(nodes: &[Node]) -> Vec<SymbolInfo> {
    let mut symbols = Vec::new();
    for node in nodes {
        match node {
            Node::Function(func) => {
                symbols.push(SymbolInfo::new(
                    &func.name,
                    SymbolKind::Function,
                    span_to_range(&func.span),
                ));
            }
            Node::Class(class) => {
                let mut class_symbol = SymbolInfo::new(&class.name, SymbolKind::Class, span_to_range(&class.span));
                let mut children = Vec::new();
                for method in &class.methods {
                    children.push(
                        SymbolInfo::new(&method.name, SymbolKind::Method, span_to_range(&method.span))
                            .with_container(&class.name),
                    );
                }
                for field in &class.fields {
                    children.push(
                        SymbolInfo::new(&field.name, SymbolKind::Field, span_to_range(&field.span))
                            .with_container(&class.name),
                    );
                }
                class_symbol = class_symbol.with_children(children);
                symbols.push(class_symbol);
            }
            Node::Struct(s) => {
                let mut struct_symbol = SymbolInfo::new(&s.name, SymbolKind::Struct, span_to_range(&s.span));
                let mut fields = Vec::new();
                for field in &s.fields {
                    fields.push(
                        SymbolInfo::new(&field.name, SymbolKind::Field, span_to_range(&field.span))
                            .with_container(&s.name),
                    );
                }
                struct_symbol = struct_symbol.with_children(fields);
                symbols.push(struct_symbol);
            }
            Node::Enum(e) => {
                let mut enum_symbol = SymbolInfo::new(&e.name, SymbolKind::Enum, span_to_range(&e.span));
                let mut variants = Vec::new();
                for variant in &e.variants {
                    variants.push(
                        SymbolInfo::new(&variant.name, SymbolKind::EnumMember, span_to_range(&variant.span))
                            .with_container(&e.name),
                    );
                }
                enum_symbol = enum_symbol.with_children(variants);
                symbols.push(enum_symbol);
            }
            Node::Trait(t) => {
                let mut trait_symbol = SymbolInfo::new(&t.name, SymbolKind::Interface, span_to_range(&t.span));
                let mut methods = Vec::new();
                for method in &t.methods {
                    methods.push(
                        SymbolInfo::new(&method.name, SymbolKind::Method, span_to_range(&method.span))
                            .with_container(&t.name),
                    );
                }
                trait_symbol = trait_symbol.with_children(methods);
                symbols.push(trait_symbol);
            }
            Node::Let(let_stmt) => {
                if let Some(name) = extract_pattern_name(&let_stmt.pattern) {
                    symbols.push(SymbolInfo::new(
                        name,
                        SymbolKind::Variable,
                        span_to_range(&let_stmt.span),
                    ));
                }
            }
            _ => {}
        }
    }
    symbols
}

fn collect_semantic_warnings(nodes: &[Node], diagnostics: &mut Vec<Diagnostic>) {
    for node in nodes {
        match node {
            Node::Function(func) => {
                if func.params.len() > 10 {
                    diagnostics.push(
                        Diagnostic::warning(
                            span_to_range(&func.span),
                            format!("Function '{}' has many parameters", func.name),
                        )
                        .with_code("W001"),
                    );
                }
            }
            Node::Class(class) => {
                if class.methods.is_empty() && class.fields.is_empty() {
                    diagnostics.push(
                        Diagnostic::warning(
                            span_to_range(&class.span),
                            format!("Class '{}' has no fields or methods", class.name),
                        )
                        .with_code("W002"),
                    );
                }
            }
            _ => {}
        }
    }
}

fn span_to_range(span: &Span) -> Range {
    Range::from_span(span.line, span.column, span.line, span.column + (span.end - span.start))
}

/// Convert a file path to a file:// URI
pub fn file_uri(path: &str) -> String {
    if path.starts_with("file://") {
        path.to_string()
    } else {
        let abs_path = Path::new(path)
            .canonicalize()
            .map(|p| p.to_string_lossy().to_string())
            .unwrap_or_else(|_| path.to_string());
        format!("file://{}", abs_path)
    }
}

fn extract_pattern_name(pattern: &simple_parser::ast::Pattern) -> Option<&str> {
    match pattern {
        simple_parser::ast::Pattern::Identifier(name) => Some(name),
        _ => None,
    }
}

fn format_function_signature(func: &FunctionDef) -> String {
    let vis = if func.visibility.is_public() { "pub " } else { "" };
    let async_kw = if func
        .effects
        .iter()
        .any(|e| matches!(e, simple_parser::ast::Effect::Async))
    {
        "async "
    } else {
        ""
    };
    let params: Vec<String> = func
        .params
        .iter()
        .map(|p| {
            if let Some(ty) = &p.ty {
                format!("{}: {}", p.name, type_to_string(ty))
            } else {
                p.name.clone()
            }
        })
        .collect();
    let ret = func
        .return_type
        .as_ref()
        .map(|t| format!(" -> {}", type_to_string(t)))
        .unwrap_or_default();
    format!("{}{}fn {}({}){}", vis, async_kw, func.name, params.join(", "), ret)
}

fn format_class_signature(class: &ClassDef) -> String {
    let vis = if class.visibility.is_public() { "pub " } else { "" };
    let fields: Vec<String> = class
        .fields
        .iter()
        .map(|f| format!("    {}: {}", f.name, type_to_string(&f.ty)))
        .collect();
    let methods: Vec<String> = class
        .methods
        .iter()
        .map(|m| format!("    fn {}(...)", m.name))
        .collect();
    format!(
        "{}class {}:\n{}\n{}",
        vis,
        class.name,
        fields.join("\n"),
        methods.join("\n")
    )
}

fn format_struct_signature(s: &StructDef) -> String {
    let vis = if s.visibility.is_public() { "pub " } else { "" };
    let fields: Vec<String> = s
        .fields
        .iter()
        .map(|f| format!("    {}: {}", f.name, type_to_string(&f.ty)))
        .collect();
    format!("{}struct {}:\n{}", vis, s.name, fields.join("\n"))
}

fn format_enum_signature(e: &EnumDef) -> String {
    let vis = if e.visibility.is_public() { "pub " } else { "" };
    let variants: Vec<String> = e.variants.iter().map(|v| format!("    {}", v.name)).collect();
    format!("{}enum {}:\n{}", vis, e.name, variants.join("\n"))
}

fn format_trait_signature(t: &TraitDef) -> String {
    let vis = if t.visibility.is_public() { "pub " } else { "" };
    let methods: Vec<String> = t.methods.iter().map(|m| format!("    fn {}(...)", m.name)).collect();
    format!("{}trait {}:\n{}", vis, t.name, methods.join("\n"))
}

fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!(
                    "{}<{}>",
                    name,
                    args.iter().map(type_to_string).collect::<Vec<_>>().join(", ")
                )
            }
        }
        Type::Array { element, .. } => format!("[{}]", type_to_string(element)),
        Type::Optional(inner) => format!("{}?", type_to_string(inner)),
        Type::Tuple(types) => format!("({})", types.iter().map(type_to_string).collect::<Vec<_>>().join(", ")),
        Type::Function { params, ret } => {
            let params_str = params.iter().map(type_to_string).collect::<Vec<_>>().join(", ");
            let ret_str = ret
                .as_ref()
                .map(|r| type_to_string(r))
                .unwrap_or_else(|| "void".to_string());
            format!("fn({}) -> {}", params_str, ret_str)
        }
        Type::Pointer { inner, .. } => format!("*{}", type_to_string(inner)),
        Type::Union(types) => types.iter().map(type_to_string).collect::<Vec<_>>().join(" | "),
        Type::DynTrait(name) => format!("dyn {}", name),
        Type::Capability { inner, .. } => type_to_string(inner),
        _ => "unknown".to_string(),
    }
}
