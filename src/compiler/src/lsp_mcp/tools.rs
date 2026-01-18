//! LSP MCP Tool Implementations
//!
//! Implements LSP-like code intelligence tools for MCP protocol.
//! Uses the Simple language parser and compiler infrastructure.

use crate::lsp_mcp::types::*;
use simple_parser::ast::{Block, ClassDef, EnumDef, Expr, FunctionDef, Node, StructDef, TraitDef, Type};
use simple_parser::token::Span;
use simple_parser::Parser;
use std::collections::HashMap;
use std::path::Path;

/// LSP MCP Tools - provides code intelligence operations
pub struct LspMcpTools {
    /// Cache of parsed files (path -> AST)
    file_cache: HashMap<String, Vec<Node>>,
    /// Cache of source text (path -> source)
    source_cache: HashMap<String, String>,
}

impl Default for LspMcpTools {
    fn default() -> Self {
        Self::new()
    }
}

impl LspMcpTools {
    /// Create new LSP MCP tools instance
    pub fn new() -> Self {
        Self {
            file_cache: HashMap::new(),
            source_cache: HashMap::new(),
        }
    }

    /// Parse a file and cache the result
    pub fn parse_file(&mut self, path: &str, source: &str) -> Result<&[Node], String> {
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => {
                self.source_cache.insert(path.to_string(), source.to_string());
                self.file_cache.insert(path.to_string(), module.items);
                Ok(self.file_cache.get(path).unwrap())
            }
            Err(e) => Err(e.to_string()),
        }
    }

    /// Get cached AST or parse file
    pub fn get_or_parse(&mut self, path: &str, source: &str) -> Result<&[Node], String> {
        if !self.file_cache.contains_key(path) {
            self.parse_file(path, source)?;
        }
        Ok(self.file_cache.get(path).unwrap())
    }

    /// Clear cache for a file
    pub fn invalidate(&mut self, path: &str) {
        self.file_cache.remove(path);
        self.source_cache.remove(path);
    }

    /// Find definition of symbol at position
    pub fn go_to_definition(&mut self, path: &str, source: &str, line: u32, character: u32) -> Option<Location> {
        let nodes = self.get_or_parse(path, source).ok()?;

        // Find symbol at position
        let symbol_name = self.find_symbol_at_position(source, line, character)?;

        // Search for definition in AST
        self.find_definition_in_nodes(nodes, &symbol_name, path)
    }

    /// Find all references to symbol at position
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

        // Find symbol at position
        let symbol_name = match self.find_symbol_at_position(source, line, character) {
            Some(name) => name,
            None => return references,
        };

        // Find definition first
        if include_declaration {
            if let Some(def_loc) = self.find_definition_in_nodes(nodes, &symbol_name, path) {
                references.push(ReferenceLocation::definition(def_loc.uri, def_loc.range));
            }
        }

        // Find all references in AST
        self.collect_references_in_nodes(nodes, &symbol_name, path, &mut references);

        references
    }

    /// Get hover information for symbol at position
    pub fn hover(&mut self, path: &str, source: &str, line: u32, character: u32) -> Option<HoverInfo> {
        let nodes = self.get_or_parse(path, source).ok()?;

        // Find symbol at position
        let symbol_name = self.find_symbol_at_position(source, line, character)?;

        // Find definition and generate hover info
        self.generate_hover_info(nodes, &symbol_name)
    }

    /// Get all symbols in a document
    pub fn document_symbols(&mut self, path: &str, source: &str) -> Vec<SymbolInfo> {
        let nodes = match self.get_or_parse(path, source) {
            Ok(n) => n,
            Err(_) => return Vec::new(),
        };

        self.extract_symbols_from_nodes(nodes)
    }

    /// Get diagnostics (parse errors and semantic warnings)
    pub fn diagnostics(&mut self, path: &str, source: &str, include_warnings: bool) -> Vec<Diagnostic> {
        let mut diagnostics = Vec::new();

        // Try parsing and collect errors
        let mut parser = Parser::new(source);
        match parser.parse() {
            Ok(module) => {
                // Cache successful parse
                self.source_cache.insert(path.to_string(), source.to_string());
                self.file_cache.insert(path.to_string(), module.items.clone());

                // Run additional semantic checks if warnings requested
                if include_warnings {
                    self.collect_semantic_warnings(&module.items, &mut diagnostics);
                }
            }
            Err(err) => {
                // Convert parse error to diagnostic
                let span = err.span().unwrap_or_else(|| Span::new(0, 1, 1, 1));
                let range = Range::from_span(span.line, span.column, span.line, span.column + (span.end - span.start));

                diagnostics.push(Diagnostic::error(range, err.to_string()));
            }
        }

        diagnostics
    }

    // === Helper methods ===

    /// Find symbol name at given position in source text
    fn find_symbol_at_position(&self, source: &str, line: u32, character: u32) -> Option<String> {
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

        // Find word boundaries
        let chars: Vec<char> = line_text.chars().collect();

        // Find start of identifier
        let mut start = char_idx;
        while start > 0 && is_identifier_char(chars[start - 1]) {
            start -= 1;
        }

        // Find end of identifier
        let mut end = char_idx;
        while end < chars.len() && is_identifier_char(chars[end]) {
            end += 1;
        }

        if start == end {
            return None;
        }

        Some(chars[start..end].iter().collect())
    }

    /// Find definition of a symbol in AST nodes
    fn find_definition_in_nodes(&self, nodes: &[Node], name: &str, file_path: &str) -> Option<Location> {
        let uri = path_to_uri(file_path);

        for node in nodes {
            match node {
                Node::Function(func) if func.name == name => {
                    let range = span_to_range(&func.span);
                    return Some(Location::new(&uri, range));
                }
                Node::Class(class) if class.name == name => {
                    let range = span_to_range(&class.span);
                    return Some(Location::new(&uri, range));
                }
                Node::Struct(s) if s.name == name => {
                    let range = span_to_range(&s.span);
                    return Some(Location::new(&uri, range));
                }
                Node::Enum(e) if e.name == name => {
                    let range = span_to_range(&e.span);
                    return Some(Location::new(&uri, range));
                }
                Node::Trait(t) if t.name == name => {
                    let range = span_to_range(&t.span);
                    return Some(Location::new(&uri, range));
                }
                Node::Class(class) => {
                    // Check methods in class
                    for method in &class.methods {
                        if method.name == name {
                            let range = span_to_range(&method.span);
                            return Some(Location::new(&uri, range));
                        }
                    }
                }
                Node::Let(let_stmt) => {
                    // Check variable binding
                    if let Some(pattern_name) = extract_pattern_name(&let_stmt.pattern) {
                        if pattern_name == name {
                            let range = span_to_range(&let_stmt.span);
                            return Some(Location::new(&uri, range));
                        }
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Collect all references to a symbol
    fn collect_references_in_nodes(
        &self,
        nodes: &[Node],
        name: &str,
        file_path: &str,
        references: &mut Vec<ReferenceLocation>,
    ) {
        let uri = path_to_uri(file_path);

        for node in nodes {
            self.collect_references_in_node(node, name, &uri, references);
        }
    }

    fn collect_references_in_node(&self, node: &Node, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
        match node {
            Node::Function(func) => {
                // Check body
                self.collect_references_in_block(&func.body, name, uri, references);
            }
            Node::Class(class) => {
                for method in &class.methods {
                    self.collect_references_in_block(&method.body, name, uri, references);
                }
            }
            Node::Expression(expr) => {
                self.collect_references_in_expr(expr, name, uri, references);
            }
            Node::Let(let_stmt) => {
                if let Some(value) = &let_stmt.value {
                    self.collect_references_in_expr(value, name, uri, references);
                }
            }
            Node::Assignment(assign) => {
                self.collect_references_in_expr(&assign.target, name, uri, references);
                self.collect_references_in_expr(&assign.value, name, uri, references);
            }
            Node::If(if_stmt) => {
                self.collect_references_in_expr(&if_stmt.condition, name, uri, references);
                self.collect_references_in_block(&if_stmt.then_block, name, uri, references);
                if let Some(else_block) = &if_stmt.else_block {
                    self.collect_references_in_block(else_block, name, uri, references);
                }
            }
            Node::While(while_stmt) => {
                self.collect_references_in_expr(&while_stmt.condition, name, uri, references);
                self.collect_references_in_block(&while_stmt.body, name, uri, references);
            }
            Node::For(for_stmt) => {
                self.collect_references_in_expr(&for_stmt.iterable, name, uri, references);
                self.collect_references_in_block(&for_stmt.body, name, uri, references);
            }
            Node::Return(ret_stmt) => {
                if let Some(value) = &ret_stmt.value {
                    self.collect_references_in_expr(value, name, uri, references);
                }
            }
            _ => {}
        }
    }

    fn collect_references_in_block(&self, block: &Block, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
        for stmt in &block.statements {
            self.collect_references_in_node(stmt, name, uri, references);
        }
    }

    fn collect_references_in_expr(&self, expr: &Expr, name: &str, uri: &str, references: &mut Vec<ReferenceLocation>) {
        match expr {
            Expr::Identifier(ident) if ident == name => {
                // Found a reference - use a placeholder range since Expr doesn't have span directly
                // In a real implementation, we'd need span information on expressions
                let range = Range::single_line(0, 0, name.len() as u32);
                references.push(ReferenceLocation::reference(uri.to_string(), range));
            }
            Expr::Call { callee, args } => {
                self.collect_references_in_expr(callee, name, uri, references);
                for arg in args {
                    self.collect_references_in_expr(&arg.value, name, uri, references);
                }
            }
            Expr::MethodCall { receiver, args, .. } => {
                self.collect_references_in_expr(receiver, name, uri, references);
                for arg in args {
                    self.collect_references_in_expr(&arg.value, name, uri, references);
                }
            }
            Expr::Binary { left, right, .. } => {
                self.collect_references_in_expr(left, name, uri, references);
                self.collect_references_in_expr(right, name, uri, references);
            }
            Expr::Unary { operand, .. } => {
                self.collect_references_in_expr(operand, name, uri, references);
            }
            Expr::FieldAccess { receiver, .. } => {
                self.collect_references_in_expr(receiver, name, uri, references);
            }
            Expr::Index { receiver, index } => {
                self.collect_references_in_expr(receiver, name, uri, references);
                self.collect_references_in_expr(index, name, uri, references);
            }
            Expr::Array(elements) => {
                for elem in elements {
                    self.collect_references_in_expr(elem, name, uri, references);
                }
            }
            Expr::Tuple(elements) => {
                for elem in elements {
                    self.collect_references_in_expr(elem, name, uri, references);
                }
            }
            Expr::If {
                condition,
                then_branch,
                else_branch,
                ..
            } => {
                self.collect_references_in_expr(condition, name, uri, references);
                self.collect_references_in_expr(then_branch, name, uri, references);
                if let Some(else_br) = else_branch {
                    self.collect_references_in_expr(else_br, name, uri, references);
                }
            }
            Expr::Lambda { body, .. } => {
                self.collect_references_in_expr(body, name, uri, references);
            }
            Expr::Await(future) => {
                self.collect_references_in_expr(future, name, uri, references);
            }
            Expr::StructInit { fields, .. } => {
                for (_, value) in fields {
                    self.collect_references_in_expr(value, name, uri, references);
                }
            }
            _ => {}
        }
    }

    /// Generate hover information for a symbol
    fn generate_hover_info(&self, nodes: &[Node], name: &str) -> Option<HoverInfo> {
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
                    // Check methods
                    for method in &class.methods {
                        if method.name == name {
                            let sig = format_function_signature(method);
                            let markdown = format!(
                                "```simple\n{}\n```\n\nMethod of `{}`",
                                sig, class.name
                            );
                            return Some(HoverInfo::new(HoverContents::markdown(markdown)));
                        }
                    }
                }
                _ => {}
            }
        }

        None
    }

    /// Extract symbol information from AST nodes
    fn extract_symbols_from_nodes(&self, nodes: &[Node]) -> Vec<SymbolInfo> {
        let mut symbols = Vec::new();

        for node in nodes {
            match node {
                Node::Function(func) => {
                    let range = span_to_range(&func.span);
                    symbols.push(SymbolInfo::new(&func.name, SymbolKind::Function, range));
                }
                Node::Class(class) => {
                    let range = span_to_range(&class.span);
                    let mut class_symbol = SymbolInfo::new(&class.name, SymbolKind::Class, range);

                    // Add methods as children
                    let mut method_symbols = Vec::new();
                    for method in &class.methods {
                        let method_range = span_to_range(&method.span);
                        method_symbols.push(
                            SymbolInfo::new(&method.name, SymbolKind::Method, method_range)
                                .with_container(&class.name),
                        );
                    }

                    // Add fields as children
                    for field in &class.fields {
                        let field_range = span_to_range(&field.span);
                        method_symbols.push(
                            SymbolInfo::new(&field.name, SymbolKind::Field, field_range).with_container(&class.name),
                        );
                    }

                    class_symbol = class_symbol.with_children(method_symbols);
                    symbols.push(class_symbol);
                }
                Node::Struct(s) => {
                    let range = span_to_range(&s.span);
                    let mut struct_symbol = SymbolInfo::new(&s.name, SymbolKind::Struct, range);

                    // Add fields
                    let mut field_symbols = Vec::new();
                    for field in &s.fields {
                        let field_range = span_to_range(&field.span);
                        field_symbols
                            .push(SymbolInfo::new(&field.name, SymbolKind::Field, field_range).with_container(&s.name));
                    }
                    struct_symbol = struct_symbol.with_children(field_symbols);
                    symbols.push(struct_symbol);
                }
                Node::Enum(e) => {
                    let range = span_to_range(&e.span);
                    let mut enum_symbol = SymbolInfo::new(&e.name, SymbolKind::Enum, range);

                    // Add variants
                    let mut variant_symbols = Vec::new();
                    for variant in &e.variants {
                        let variant_range = span_to_range(&variant.span);
                        variant_symbols.push(
                            SymbolInfo::new(&variant.name, SymbolKind::EnumMember, variant_range)
                                .with_container(&e.name),
                        );
                    }
                    enum_symbol = enum_symbol.with_children(variant_symbols);
                    symbols.push(enum_symbol);
                }
                Node::Trait(t) => {
                    let range = span_to_range(&t.span);
                    let mut trait_symbol = SymbolInfo::new(&t.name, SymbolKind::Interface, range);

                    // Add methods
                    let mut method_symbols = Vec::new();
                    for method in &t.methods {
                        let method_range = span_to_range(&method.span);
                        method_symbols.push(
                            SymbolInfo::new(&method.name, SymbolKind::Method, method_range).with_container(&t.name),
                        );
                    }
                    trait_symbol = trait_symbol.with_children(method_symbols);
                    symbols.push(trait_symbol);
                }
                Node::Let(let_stmt) => {
                    if let Some(name) = extract_pattern_name(&let_stmt.pattern) {
                        let range = span_to_range(&let_stmt.span);
                        symbols.push(SymbolInfo::new(name, SymbolKind::Variable, range));
                    }
                }
                _ => {}
            }
        }

        symbols
    }

    /// Collect semantic warnings from AST
    fn collect_semantic_warnings(&self, nodes: &[Node], diagnostics: &mut Vec<Diagnostic>) {
        for node in nodes {
            match node {
                Node::Function(func) => {
                    // Check for unused parameters (simplified check)
                    if func.params.len() > 10 {
                        let range = span_to_range(&func.span);
                        diagnostics.push(
                            Diagnostic::warning(range, format!("Function '{}' has many parameters", func.name))
                                .with_code("W001"),
                        );
                    }
                }
                Node::Class(class) => {
                    // Check for classes with no methods
                    if class.methods.is_empty() && class.fields.is_empty() {
                        let range = span_to_range(&class.span);
                        diagnostics.push(
                            Diagnostic::warning(
                                range,
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
}

// === Utility functions ===

/// Check if character is valid in identifier
fn is_identifier_char(c: char) -> bool {
    c.is_alphanumeric() || c == '_'
}

/// Convert span to range
fn span_to_range(span: &Span) -> Range {
    Range::from_span(span.line, span.column, span.line, span.column + (span.end - span.start))
}

/// Convert file path to URI
fn path_to_uri(path: &str) -> String {
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

/// Extract name from pattern (simplified)
fn extract_pattern_name(pattern: &simple_parser::ast::Pattern) -> Option<&str> {
    match pattern {
        simple_parser::ast::Pattern::Identifier(name) => Some(name),
        _ => None,
    }
}

/// Format function signature for hover
fn format_function_signature(func: &FunctionDef) -> String {
    let vis = if func.visibility.is_public() { "pub " } else { "" };
    let async_kw = if func.effects.iter().any(|e| matches!(e, simple_parser::ast::Effect::Async)) {
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

/// Format class signature for hover
fn format_class_signature(class: &ClassDef) -> String {
    let vis = if class.visibility.is_public() { "pub " } else { "" };
    let fields: Vec<String> = class.fields.iter().map(|f| format!("    {}: {}", f.name, type_to_string(&f.ty))).collect();

    let methods: Vec<String> = class.methods.iter().map(|m| format!("    fn {}(...)", m.name)).collect();

    format!(
        "{}class {}:\n{}\n{}",
        vis,
        class.name,
        fields.join("\n"),
        methods.join("\n")
    )
}

/// Format struct signature for hover
fn format_struct_signature(s: &StructDef) -> String {
    let vis = if s.visibility.is_public() { "pub " } else { "" };
    let fields: Vec<String> = s.fields.iter().map(|f| format!("    {}: {}", f.name, type_to_string(&f.ty))).collect();

    format!("{}struct {}:\n{}", vis, s.name, fields.join("\n"))
}

/// Format enum signature for hover
fn format_enum_signature(e: &EnumDef) -> String {
    let vis = if e.visibility.is_public() { "pub " } else { "" };
    let variants: Vec<String> = e.variants.iter().map(|v| format!("    {}", v.name)).collect();

    format!("{}enum {}:\n{}", vis, e.name, variants.join("\n"))
}

/// Format trait signature for hover
fn format_trait_signature(t: &TraitDef) -> String {
    let vis = if t.visibility.is_public() { "pub " } else { "" };
    let methods: Vec<String> = t.methods.iter().map(|m| format!("    fn {}(...)", m.name)).collect();

    format!("{}trait {}:\n{}", vis, t.name, methods.join("\n"))
}

/// Convert Type AST to string
fn type_to_string(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            if args.is_empty() {
                name.clone()
            } else {
                format!("{}<{}>", name, args.iter().map(type_to_string).collect::<Vec<_>>().join(", "))
            }
        }
        Type::Array { element, .. } => format!("[{}]", type_to_string(element)),
        Type::Optional(inner) => format!("{}?", type_to_string(inner)),
        Type::Tuple(types) => format!("({})", types.iter().map(type_to_string).collect::<Vec<_>>().join(", ")),
        Type::Function { params, ret } => {
            let params_str = params.iter().map(type_to_string).collect::<Vec<_>>().join(", ");
            let ret_str = ret.as_ref().map(|r| type_to_string(r)).unwrap_or_else(|| "void".to_string());
            format!("fn({}) -> {}", params_str, ret_str)
        }
        Type::Pointer { inner, .. } => format!("*{}", type_to_string(inner)),
        Type::Union(types) => types.iter().map(type_to_string).collect::<Vec<_>>().join(" | "),
        Type::DynTrait(name) => format!("dyn {}", name),
        Type::Capability { inner, .. } => type_to_string(inner),
        _ => "unknown".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_file() {
        let mut tools = LspMcpTools::new();
        let source = r#"
fn hello() -> text:
    return "Hello"
"#;

        let result = tools.parse_file("test.spl", source);
        assert!(result.is_ok());
    }

    #[test]
    fn test_document_symbols() {
        let mut tools = LspMcpTools::new();
        let source = r#"
pub fn calculate(x: i64, y: i64) -> i64:
    return x + y

pub struct Point:
    pub x: i64
    pub y: i64

pub class User:
    pub name: text
"#;

        let symbols = tools.document_symbols("test.spl", source);
        assert!(symbols.len() >= 3);

        let names: Vec<_> = symbols.iter().map(|s| s.name.as_str()).collect();
        assert!(names.contains(&"calculate"));
        assert!(names.contains(&"Point"));
        assert!(names.contains(&"User"));
    }

    #[test]
    fn test_hover() {
        let mut tools = LspMcpTools::new();
        let source = r#"
pub fn greet(name: text) -> text:
    return "Hello, " + name
"#;

        // Position in "greet" function name
        let hover = tools.hover("test.spl", source, 1, 7);
        assert!(hover.is_some());

        let info = hover.unwrap();
        assert!(info.contents.value.contains("fn greet"));
    }

    #[test]
    fn test_diagnostics() {
        let mut tools = LspMcpTools::new();

        // Valid source - no errors
        let valid_source = r#"
fn test():
    pass
"#;
        let diags = tools.diagnostics("test.spl", valid_source, false);
        assert!(diags.is_empty());

        // Invalid source - should have error
        let invalid_source = "fn incomplete(";
        let diags = tools.diagnostics("test.spl", invalid_source, false);
        assert!(!diags.is_empty());
    }

    #[test]
    fn test_find_symbol_at_position() {
        let tools = LspMcpTools::new();
        let source = "fn hello_world():";

        // Position at 'h' in 'hello_world'
        let symbol = tools.find_symbol_at_position(source, 0, 3);
        assert_eq!(symbol, Some("hello_world".to_string()));

        // Position at 'f' in 'fn'
        let symbol2 = tools.find_symbol_at_position(source, 0, 0);
        assert_eq!(symbol2, Some("fn".to_string()));
    }
}
