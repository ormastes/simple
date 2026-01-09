//! Minimal Code Preview (MCP) Generator
//!
//! Generates token-efficient, collapsed code representations for LLM consumption.
//! Reduces token usage by 90%+ while preserving semantic information.
//!
//! **Spec:** `doc/spec/basic_mcp.md`
//! **Features:** #880-919 (LLM-Friendly Features)
//!
//! # Format
//!
//! - **Block Marks:** C>, F>, T>, P>, V• (left margin)
//! - **Collapsed:** Bodies shown as `{ … }` inline
//! - **Expanded:** Full Simple syntax with indentation
//! - **Output:** JSON with single `text` field

use serde::{Deserialize, Serialize};
use simple_parser::ast::{
    ClassDef, FunctionDef, Node, Parameter, TraitDef, Type, Visibility,
};
use std::collections::BTreeMap;

/// MCP output format
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpOutput {
    /// Collapsed MCP text (required)
    pub text: String,
    /// Optional metadata (non-default)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub meta: Option<McpMetadata>,
}

/// Optional metadata for MCP output
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpMetadata {
    /// Always "mcp"
    pub mode: String,
    /// Line number format: "plain" | "zpad"
    #[serde(skip_serializing_if = "Option::is_none")]
    pub line_numbers: Option<String>,
    /// Show coverage overlays (default: false)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub show_coverage: Option<bool>,
    /// Show block end guides (default: false)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub show_block_guides: Option<bool>,
}

/// MCP generation mode
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum McpMode {
    /// Collapsed (default) - bodies as { … }
    Collapsed,
    /// Expanded - full syntax with indentation
    Expanded,
}

/// What to expand in a symbol
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ExpandWhat {
    /// Just the signature
    Signature,
    /// The body/implementation
    Body,
    /// Documentation comments
    Docs,
    /// Everything
    All,
}

/// MCP generator
pub struct McpGenerator {
    /// Current indentation level
    indent: usize,
    /// Show only public symbols (default: true)
    public_only: bool,
    /// Show coverage info
    show_coverage: bool,
    /// Show block guides
    show_block_guides: bool,
}

impl Default for McpGenerator {
    fn default() -> Self {
        Self::new()
    }
}

impl McpGenerator {
    /// Create a new MCP generator with default settings
    pub fn new() -> Self {
        Self {
            indent: 0,
            public_only: true,
            show_coverage: false,
            show_block_guides: false,
        }
    }

    /// Set whether to show only public symbols
    pub fn public_only(mut self, public_only: bool) -> Self {
        self.public_only = public_only;
        self
    }

    /// Set whether to show coverage info
    pub fn show_coverage(mut self, show_coverage: bool) -> Self {
        self.show_coverage = show_coverage;
        self
    }

    /// Set whether to show block guides
    pub fn show_block_guides(mut self, show_block_guides: bool) -> Self {
        self.show_block_guides = show_block_guides;
        self
    }

    /// Generate collapsed MCP output from AST nodes
    pub fn generate(&self, nodes: &[Node]) -> McpOutput {
        let mut lines = Vec::new();

        for node in nodes {
            self.process_node(node, &mut lines, McpMode::Collapsed);
        }

        McpOutput {
            text: lines.join("\n"),
            meta: self.build_metadata(),
        }
    }

    /// Generate MCP output with specific expansion
    pub fn generate_with_expansion(
        &self,
        nodes: &[Node],
        selector: &str,
        what: ExpandWhat,
    ) -> McpOutput {
        let mut lines = Vec::new();

        for node in nodes {
            self.process_node_with_expansion(
                node,
                &mut lines,
                selector,
                what,
            );
        }

        McpOutput {
            text: lines.join("\n"),
            meta: self.build_metadata(),
        }
    }

    fn build_metadata(&self) -> Option<McpMetadata> {
        if !self.show_coverage && !self.show_block_guides {
            None
        } else {
            Some(McpMetadata {
                mode: "mcp".to_string(),
                line_numbers: None,
                show_coverage: if self.show_coverage { Some(true) } else { None },
                show_block_guides: if self.show_block_guides { Some(true) } else { None },
            })
        }
    }

    fn process_node(&self, node: &Node, lines: &mut Vec<String>, mode: McpMode) {
        match node {
            Node::Function(func) => {
                if self.should_show(&func.visibility) {
                    self.format_function(func, lines, mode);
                }
            }
            Node::Class(class) => {
                if self.should_show(&class.visibility) {
                    self.format_class(class, lines, mode);
                }
            }
            Node::Trait(trait_def) => {
                self.format_trait(trait_def, lines, mode);
            }
            _ => {}
        }
    }

    fn process_node_with_expansion(
        &self,
        node: &Node,
        lines: &mut Vec<String>,
        selector: &str,
        what: ExpandWhat,
    ) {
        match node {
            Node::Function(func) => {
                if self.should_show(&func.visibility) {
                    let mode = if func.name == selector {
                        McpMode::Expanded
                    } else {
                        McpMode::Collapsed
                    };
                    self.format_function(func, lines, mode);
                }
            }
            Node::Class(class) => {
                if self.should_show(&class.visibility) {
                    let mode = if class.name == selector {
                        McpMode::Expanded
                    } else {
                        McpMode::Collapsed
                    };
                    self.format_class(class, lines, mode);
                }
            }
            Node::Trait(trait_def) => {
                let mode = if trait_def.name == selector {
                    McpMode::Expanded
                } else {
                    McpMode::Collapsed
                };
                self.format_trait(trait_def, lines, mode);
            }
            _ => {}
        }
    }

    fn should_show(&self, visibility: &Visibility) -> bool {
        !self.public_only || visibility.is_public()
    }

    fn format_function(&self, func: &FunctionDef, lines: &mut Vec<String>, mode: McpMode) {
        let mark = match mode {
            McpMode::Collapsed => "F>",
            McpMode::Expanded => "F▼",
        };

        let vis = if func.visibility.is_public() { "pub " } else { "" };
        let name = &func.name;

        match mode {
            McpMode::Collapsed => {
                // Collapsed: F> pub fn name { … }
                lines.push(format!("{} {}fn {} {{ … }}", mark, vis, name));
            }
            McpMode::Expanded => {
                // Expanded: F▼ pub fn name(params) -> ret:
                let params = self.format_params(&func.params);
                let ret = func
                    .return_type
                    .as_ref()
                    .map(|t| format!(" -> {}", self.format_type(t)))
                    .unwrap_or_default();

                lines.push(format!("{}  {}fn {}({}){} {{", mark, vis, name, params, ret));
                lines.push("    # Implementation".to_string());
                lines.push("    …".to_string());
                lines.push("}".to_string());

                if self.show_block_guides {
                    lines.push(format!("V• end fn {}", name));
                }
            }
        }
    }

    fn format_class(&self, class: &ClassDef, lines: &mut Vec<String>, mode: McpMode) {
        let mark = match mode {
            McpMode::Collapsed => "C>",
            McpMode::Expanded => "C▼",
        };

        let vis = if class.visibility.is_public() { "pub " } else { "" };
        let name = &class.name;

        match mode {
            McpMode::Collapsed => {
                // Collapsed: C> pub class Name { … }
                lines.push(format!("{} {}class {} {{ … }}", mark, vis, name));

                // Virtual info: show method names
                let methods: Vec<_> = class
                    .methods
                    .iter()
                    .filter(|m| self.should_show(&m.visibility))
                    .map(|m| m.name.as_str())
                    .collect();

                if !methods.is_empty() {
                    lines.push(format!("V• pub methods: {}", methods.join(", ")));
                }
            }
            McpMode::Expanded => {
                // Expanded: C▼ pub class Name:
                lines.push(format!("{} {}class {}:", mark, vis, name));

                // Show fields
                for field in &class.fields {
                    let field_name = &field.name;
                    let ty = format!(": {}", self.format_type(&field.ty));
                    lines.push(format!("    {}{}", field_name, ty));
                }

                // Show methods (collapsed)
                for method in &class.methods {
                    if self.should_show(&method.visibility) {
                        lines.push(format!("    pub fn {} {{ … }}", method.name));
                    }
                }

                if self.show_block_guides {
                    lines.push(format!("V• end class {}", name));
                }
            }
        }
    }

    fn format_trait(&self, trait_def: &TraitDef, lines: &mut Vec<String>, mode: McpMode) {
        let mark = match mode {
            McpMode::Collapsed => "T>",
            McpMode::Expanded => "T▼",
        };

        let name = &trait_def.name;

        match mode {
            McpMode::Collapsed => {
                // Collapsed: T> trait Name { … }
                lines.push(format!("{} trait {} {{ … }}", mark, name));
            }
            McpMode::Expanded => {
                // Expanded: T▼ trait Name:
                lines.push(format!("{} trait {}:", mark, name));

                // Show required methods
                for method in &trait_def.methods {
                    let params = self.format_params(&method.params);
                    let ret = method
                        .return_type
                        .as_ref()
                        .map(|t| format!(" -> {}", self.format_type(t)))
                        .unwrap_or_default();
                    lines.push(format!("    fn {}({}){}", method.name, params, ret));
                }

                if self.show_block_guides {
                    lines.push(format!("V• end trait {}", name));
                }
            }
        }
    }

    fn format_params(&self, params: &[Parameter]) -> String {
        params
            .iter()
            .map(|p| {
                if let Some(ty) = &p.ty {
                    format!("{}: {}", p.name, self.format_type(ty))
                } else {
                    p.name.clone()
                }
            })
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn format_type(&self, ty: &Type) -> String {
        match ty {
            Type::Simple(name) => name.clone(),
            Type::Generic { name, args } => {
                if args.len() > 2 {
                    format!("{}<…>", name)
                } else {
                    format!(
                        "{}<{}>",
                        name,
                        args.iter()
                            .map(|t| self.format_type(t))
                            .collect::<Vec<_>>()
                            .join(", ")
                    )
                }
            }
            Type::Array { element, .. } => {
                format!("[{}]", self.format_type(element))
            }
            Type::Optional(inner) => {
                format!("{}?", self.format_type(inner))
            }
            Type::Pointer { inner, .. } => {
                format!("*{}", self.format_type(inner))
            }
            Type::Tuple(types) => {
                format!(
                    "({})",
                    types
                        .iter()
                        .map(|t| self.format_type(t))
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
            _ => "…".to_string(),
        }
    }
}

/// MCP Tools API
pub struct McpTools {
    generator: McpGenerator,
}

impl McpTools {
    pub fn new() -> Self {
        Self {
            generator: McpGenerator::new(),
        }
    }

    /// Read file in MCP format
    pub fn read_file(&self, nodes: &[Node]) -> Result<String, serde_json::Error> {
        let output = self.generator.generate(nodes);
        serde_json::to_string_pretty(&output)
    }

    /// Expand a specific symbol
    pub fn expand_at(
        &self,
        nodes: &[Node],
        selector: &str,
        what: ExpandWhat,
    ) -> Result<String, serde_json::Error> {
        let output = self.generator.generate_with_expansion(nodes, selector, what);
        serde_json::to_string_pretty(&output)
    }

    /// Search for symbols (simplified version)
    pub fn search(&self, nodes: &[Node], query: &str, public_only: bool) -> Vec<String> {
        let mut results = Vec::new();

        for node in nodes {
            match node {
                Node::Function(func) => {
                    if func.name.contains(query) {
                        if !public_only || func.visibility.is_public() {
                            results.push(func.name.clone());
                        }
                    }
                }
                Node::Class(class) => {
                    if class.name.contains(query) {
                        if !public_only || class.visibility.is_public() {
                            results.push(class.name.clone());
                        }
                    }
                }
                Node::Trait(trait_def) => {
                    if trait_def.name.contains(query) {
                        results.push(trait_def.name.clone());
                    }
                }
                _ => {}
            }
        }

        results
    }
}

impl Default for McpTools {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use simple_parser::ast::*;

    fn make_public_function(name: &str) -> Node {
        use simple_parser::ast::{Block, Mutability};
        use simple_parser::token::Span;
        Node::Function(FunctionDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
            visibility: Visibility::Public,
            params: vec![
                Parameter {
                    span: Span::new(0, 0, 0, 0),
                    name: "name".to_string(),
                    ty: Some(Type::Simple("String".to_string())),
                    default: None,
                    mutability: Mutability::Immutable,
                    inject: false,
                },
            ],
            return_type: Some(Type::Simple("bool".to_string())),
            where_clause: vec![],
            body: Block::default(),
            decorators: vec![],
            generic_params: vec![],
            effects: vec![],
            attributes: vec![],
            doc_comment: None,
            contract: None,
            is_abstract: false,
            is_sync: false,
            bounds_block: None,
        })
    }

    fn make_public_class(name: &str) -> Node {
        use simple_parser::ast::{Block, Field, Mutability};
        use simple_parser::token::Span;
        Node::Class(ClassDef {
            span: Span::new(0, 0, 0, 0),
            name: name.to_string(),
            visibility: Visibility::Public,
            fields: vec![
                Field {
                    span: Span::new(0, 0, 0, 0),
                    name: "name".to_string(),
                    ty: Type::Simple("String".to_string()),
                    default: None,
                    mutability: Mutability::Mutable,
                    visibility: Visibility::Public,
                },
                Field {
                    span: Span::new(0, 0, 0, 0),
                    name: "age".to_string(),
                    ty: Type::Simple("i64".to_string()),
                    default: None,
                    mutability: Mutability::Mutable,
                    visibility: Visibility::Public,
                },
            ],
            methods: vec![FunctionDef {
                span: Span::new(0, 0, 0, 0),
                name: "login".to_string(),
                visibility: Visibility::Public,
                params: vec![],
                return_type: Some(Type::Simple("bool".to_string())),
                where_clause: vec![],
                body: Block::default(),
                decorators: vec![],
                generic_params: vec![],
                effects: vec![],
                attributes: vec![],
                doc_comment: None,
                contract: None,
                is_abstract: false,
                is_sync: false,
                bounds_block: None,
            }],
            parent: None,
            generic_params: vec![],
            where_clause: vec![],
            effects: vec![],
            attributes: vec![],
            doc_comment: None,
            invariant: None,
            macro_invocations: vec![],
            mixins: vec![],
        })
    }

    #[test]
    fn test_collapsed_function() {
        let gen = McpGenerator::new();
        let nodes = vec![make_public_function("login")];
        let output = gen.generate(&nodes);

        assert!(output.text.contains("F> pub fn login { … }"));
    }

    #[test]
    fn test_collapsed_class() {
        let gen = McpGenerator::new();
        let nodes = vec![make_public_class("User")];
        let output = gen.generate(&nodes);

        assert!(output.text.contains("C> pub class User { … }"));
        assert!(output.text.contains("V• pub methods: login"));
    }

    #[test]
    fn test_expanded_function() {
        let gen = McpGenerator::new();
        let nodes = vec![make_public_function("login")];
        let output = gen.generate_with_expansion(&nodes, "login", ExpandWhat::All);

        assert!(output.text.contains("F▼"));
        assert!(output.text.contains("pub fn login(name: String) -> bool"));
    }

    #[test]
    fn test_expanded_class() {
        let gen = McpGenerator::new();
        let nodes = vec![make_public_class("User")];
        let output = gen.generate_with_expansion(&nodes, "User", ExpandWhat::All);

        assert!(output.text.contains("C▼ pub class User:"));
        assert!(output.text.contains("name: String"));
        assert!(output.text.contains("age: i64"));
    }

    #[test]
    fn test_json_output() {
        let gen = McpGenerator::new();
        let nodes = vec![make_public_function("login")];
        let output = gen.generate(&nodes);

        let json = serde_json::to_string(&output).unwrap();
        assert!(json.contains("\"text\""));
        assert!(json.contains("F> pub fn login { … }"));
    }

    #[test]
    fn test_search() {
        let tools = McpTools::new();
        let nodes = vec![
            make_public_function("login"),
            make_public_function("logout"),
            make_public_class("User"),
        ];

        let results = tools.search(&nodes, "log", true);
        assert_eq!(results.len(), 2);
        assert!(results.contains(&"login".to_string()));
        assert!(results.contains(&"logout".to_string()));
    }

    #[test]
    fn test_block_guides() {
        let gen = McpGenerator::new().show_block_guides(true);
        let nodes = vec![make_public_function("login")];
        let output = gen.generate_with_expansion(&nodes, "login", ExpandWhat::All);

        assert!(output.text.contains("V• end fn login"));
        assert!(output.meta.is_some());
        assert_eq!(output.meta.unwrap().show_block_guides, Some(true));
    }
}
