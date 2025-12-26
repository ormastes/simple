//! API Documentation Generator
//!
//! Generates documentation from parsed AST with doc comments.
//!
//! # Usage
//!
//! ```ignore
//! use simple_parser::{Parser, doc_gen};
//!
//! let source = r#"
//! /** Adds two numbers */
//! fn add(x: Int, y: Int) -> Int:
//!     return x + y
//! "#;
//!
//! let mut parser = Parser::new(source);
//! let module = parser.parse().unwrap();
//! let docs = doc_gen::generate(&module);
//! println!("{}", docs.to_markdown());
//! ```

use crate::ast::*;
use std::collections::HashMap;

/// A documented item extracted from the AST
#[derive(Debug, Clone)]
pub struct DocItem {
    pub kind: DocItemKind,
    pub name: String,
    pub doc: String,
    pub signature: String,
    pub visibility: Visibility,
}

#[derive(Debug, Clone, PartialEq)]
pub enum DocItemKind {
    Function,
    Struct,
    Class,
    Enum,
    Trait,
}

/// Collection of documented items from a module
#[derive(Debug, Default)]
pub struct ModuleDocs {
    pub name: Option<String>,
    pub items: Vec<DocItem>,
}

impl ModuleDocs {
    /// Group items by kind for documentation generation
    fn group_items(
        &self,
    ) -> (
        Vec<&DocItem>,
        Vec<&DocItem>,
        Vec<&DocItem>,
        Vec<&DocItem>,
        Vec<&DocItem>,
    ) {
        let functions: Vec<_> = self
            .items
            .iter()
            .filter(|i| i.kind == DocItemKind::Function)
            .collect();
        let structs: Vec<_> = self
            .items
            .iter()
            .filter(|i| i.kind == DocItemKind::Struct)
            .collect();
        let classes: Vec<_> = self
            .items
            .iter()
            .filter(|i| i.kind == DocItemKind::Class)
            .collect();
        let enums: Vec<_> = self
            .items
            .iter()
            .filter(|i| i.kind == DocItemKind::Enum)
            .collect();
        let traits: Vec<_> = self
            .items
            .iter()
            .filter(|i| i.kind == DocItemKind::Trait)
            .collect();

        (functions, structs, classes, enums, traits)
    }

    /// Generate Markdown documentation
    pub fn to_markdown(&self) -> String {
        let mut out = String::new();

        // Module header
        if let Some(name) = &self.name {
            out.push_str(&format!("# Module `{}`\n\n", name));
        } else {
            out.push_str("# API Documentation\n\n");
        }

        // Group items by kind
        let (functions, structs, classes, enums, traits) = self.group_items();

        // Traits
        if !traits.is_empty() {
            out.push_str("## Traits\n\n");
            for item in traits {
                out.push_str(&format_item_markdown(item));
            }
        }

        // Structs
        if !structs.is_empty() {
            out.push_str("## Structs\n\n");
            for item in structs {
                out.push_str(&format_item_markdown(item));
            }
        }

        // Classes
        if !classes.is_empty() {
            out.push_str("## Classes\n\n");
            for item in classes {
                out.push_str(&format_item_markdown(item));
            }
        }

        // Enums
        if !enums.is_empty() {
            out.push_str("## Enums\n\n");
            for item in enums {
                out.push_str(&format_item_markdown(item));
            }
        }

        // Functions
        if !functions.is_empty() {
            out.push_str("## Functions\n\n");
            for item in functions {
                out.push_str(&format_item_markdown(item));
            }
        }

        out
    }

    /// Generate HTML documentation
    pub fn to_html(&self) -> String {
        let mut out = String::new();

        out.push_str("<!DOCTYPE html>\n<html>\n<head>\n");
        out.push_str("<meta charset=\"utf-8\">\n");
        out.push_str("<style>\n");
        out.push_str("body { font-family: system-ui, sans-serif; max-width: 800px; margin: 0 auto; padding: 2rem; }\n");
        out.push_str("pre { background: #f5f5f5; padding: 1rem; overflow-x: auto; }\n");
        out.push_str("code { font-family: monospace; }\n");
        out.push_str(
            ".item { margin-bottom: 2rem; border-bottom: 1px solid #eee; padding-bottom: 1rem; }\n",
        );
        out.push_str(".visibility { color: #666; font-size: 0.9em; }\n");
        out.push_str("</style>\n");

        // Title
        if let Some(name) = &self.name {
            out.push_str(&format!("<title>Module {}</title>\n", name));
        } else {
            out.push_str("<title>API Documentation</title>\n");
        }
        out.push_str("</head>\n<body>\n");

        // Header
        if let Some(name) = &self.name {
            out.push_str(&format!("<h1>Module <code>{}</code></h1>\n", name));
        } else {
            out.push_str("<h1>API Documentation</h1>\n");
        }

        // Group items by kind
        let (functions, structs, classes, enums, traits) = self.group_items();

        if !traits.is_empty() {
            out.push_str("<h2>Traits</h2>\n");
            for item in traits {
                out.push_str(&format_item_html(item));
            }
        }

        if !structs.is_empty() {
            out.push_str("<h2>Structs</h2>\n");
            for item in structs {
                out.push_str(&format_item_html(item));
            }
        }

        if !classes.is_empty() {
            out.push_str("<h2>Classes</h2>\n");
            for item in classes {
                out.push_str(&format_item_html(item));
            }
        }

        if !enums.is_empty() {
            out.push_str("<h2>Enums</h2>\n");
            for item in enums {
                out.push_str(&format_item_html(item));
            }
        }

        if !functions.is_empty() {
            out.push_str("<h2>Functions</h2>\n");
            for item in functions {
                out.push_str(&format_item_html(item));
            }
        }

        out.push_str("</body>\n</html>");
        out
    }
}

fn format_item_markdown(item: &DocItem) -> String {
    let mut out = String::new();

    let vis = match item.visibility {
        Visibility::Public => "pub ",
        Visibility::Private => "",
    };

    out.push_str(&format!("### `{}{}`\n\n", vis, item.name));
    out.push_str(&format!("```\n{}\n```\n\n", item.signature));

    if !item.doc.is_empty() {
        out.push_str(&item.doc);
        out.push_str("\n\n");
    }

    out
}

fn format_item_html(item: &DocItem) -> String {
    let mut out = String::new();

    let vis = match item.visibility {
        Visibility::Public => "<span class=\"visibility\">pub</span> ",
        Visibility::Private => "",
    };

    out.push_str("<div class=\"item\">\n");
    out.push_str(&format!(
        "<h3>{}<code>{}</code></h3>\n",
        vis,
        html_escape(&item.name)
    ));
    out.push_str(&format!(
        "<pre><code>{}</code></pre>\n",
        html_escape(&item.signature)
    ));

    if !item.doc.is_empty() {
        out.push_str(&format!("<p>{}</p>\n", html_escape(&item.doc)));
    }

    out.push_str("</div>\n");
    out
}

fn html_escape(s: &str) -> String {
    s.replace('&', "&amp;")
        .replace('<', "&lt;")
        .replace('>', "&gt;")
        .replace('"', "&quot;")
}

/// Registry for examples tables used in doc interpolation.
/// Maps examples name to formatted table content.
#[derive(Debug, Default, Clone)]
pub struct ExamplesRegistry {
    tables: HashMap<String, String>,
}

impl ExamplesRegistry {
    /// Create a new empty registry.
    pub fn new() -> Self {
        Self::default()
    }

    /// Register an examples table with its formatted content.
    pub fn register(&mut self, name: impl Into<String>, content: impl Into<String>) {
        self.tables.insert(name.into(), content.into());
    }

    /// Get the content for an examples table.
    pub fn get(&self, name: &str) -> Option<&String> {
        self.tables.get(name)
    }

    /// Expand all `${examples name}` interpolations in a doc string.
    pub fn expand(&self, doc: &str) -> String {
        let doc_comment = DocComment::new(doc.to_string());
        doc_comment.expand(|name| self.tables.get(name).cloned())
    }

    /// Expand interpolations in a DocComment.
    pub fn expand_doc_comment(&self, doc: &DocComment) -> String {
        doc.expand(|name| self.tables.get(name).cloned())
    }
}

/// Format an examples table as a Markdown table.
/// Takes headers and rows, returns formatted Markdown.
pub fn format_examples_as_markdown(headers: &[String], rows: &[Vec<String>]) -> String {
    if headers.is_empty() {
        return String::new();
    }

    let mut result = String::new();

    // Header row
    result.push_str("| ");
    result.push_str(&headers.join(" | "));
    result.push_str(" |\n");

    // Separator row
    result.push_str("|");
    for _ in headers {
        result.push_str(" --- |");
    }
    result.push('\n');

    // Data rows
    for row in rows {
        result.push_str("| ");
        result.push_str(&row.join(" | "));
        result.push_str(" |\n");
    }

    result
}

/// Format an examples table as an HTML table.
pub fn format_examples_as_html(headers: &[String], rows: &[Vec<String>]) -> String {
    if headers.is_empty() {
        return String::new();
    }

    let mut result = String::from("<table>\n<thead>\n<tr>\n");

    // Header row
    for header in headers {
        result.push_str(&format!("<th>{}</th>\n", html_escape(header)));
    }
    result.push_str("</tr>\n</thead>\n<tbody>\n");

    // Data rows
    for row in rows {
        result.push_str("<tr>\n");
        for cell in row {
            result.push_str(&format!("<td>{}</td>\n", html_escape(cell)));
        }
        result.push_str("</tr>\n");
    }

    result.push_str("</tbody>\n</table>\n");
    result
}

/// Generate documentation from a parsed module
pub fn generate(module: &Module) -> ModuleDocs {
    let mut docs = ModuleDocs {
        name: module.name.clone(),
        items: Vec::new(),
    };

    for item in &module.items {
        if let Some(doc_item) = extract_doc_item(item) {
            docs.items.push(doc_item);
        }
    }

    docs
}

fn extract_doc_item(node: &Node) -> Option<DocItem> {
    match node {
        Node::Function(f) => {
            let doc = f
                .doc_comment
                .as_ref()
                .map(|d| d.content.clone())
                .unwrap_or_default();
            Some(DocItem {
                kind: DocItemKind::Function,
                name: f.name.clone(),
                doc,
                signature: format_function_signature(f),
                visibility: f.visibility.clone(),
            })
        }
        Node::Struct(s) => {
            let doc = s
                .doc_comment
                .as_ref()
                .map(|d| d.content.clone())
                .unwrap_or_default();
            Some(DocItem {
                kind: DocItemKind::Struct,
                name: s.name.clone(),
                doc,
                signature: format_struct_signature(s),
                visibility: s.visibility.clone(),
            })
        }
        Node::Class(c) => {
            let doc = c
                .doc_comment
                .as_ref()
                .map(|d| d.content.clone())
                .unwrap_or_default();
            Some(DocItem {
                kind: DocItemKind::Class,
                name: c.name.clone(),
                doc,
                signature: format_class_signature(c),
                visibility: c.visibility.clone(),
            })
        }
        Node::Enum(e) => {
            let doc = e
                .doc_comment
                .as_ref()
                .map(|d| d.content.clone())
                .unwrap_or_default();
            Some(DocItem {
                kind: DocItemKind::Enum,
                name: e.name.clone(),
                doc,
                signature: format_enum_signature(e),
                visibility: e.visibility.clone(),
            })
        }
        Node::Trait(t) => {
            let doc = t
                .doc_comment
                .as_ref()
                .map(|d| d.content.clone())
                .unwrap_or_default();
            Some(DocItem {
                kind: DocItemKind::Trait,
                name: t.name.clone(),
                doc,
                signature: format_trait_signature(t),
                visibility: t.visibility.clone(),
            })
        }
        _ => None,
    }
}

fn format_function_signature(f: &FunctionDef) -> String {
    let mut sig = String::new();

    if f.visibility == Visibility::Public {
        sig.push_str("pub ");
    }

    // Show effect decorators
    for effect in &f.effects {
        sig.push('@');
        sig.push_str(effect.decorator_name());
        sig.push(' ');
    }

    sig.push_str("fn ");
    sig.push_str(&f.name);

    // Generic params
    if !f.generic_params.is_empty() {
        sig.push('<');
        sig.push_str(&f.generic_params.join(", "));
        sig.push('>');
    }

    // Parameters
    sig.push('(');
    let params: Vec<String> = f
        .params
        .iter()
        .map(|p| {
            let mut param = String::new();
            if p.mutability == Mutability::Mutable {
                param.push_str("mut ");
            }
            param.push_str(&p.name);
            if let Some(ty) = &p.ty {
                param.push_str(": ");
                param.push_str(&format_type(ty));
            }
            param
        })
        .collect();
    sig.push_str(&params.join(", "));
    sig.push(')');

    // Return type
    if let Some(ret) = &f.return_type {
        sig.push_str(" -> ");
        sig.push_str(&format_type(ret));
    }

    sig
}

fn format_struct_signature(s: &StructDef) -> String {
    let mut sig = String::new();

    if s.visibility == Visibility::Public {
        sig.push_str("pub ");
    }

    sig.push_str("struct ");
    sig.push_str(&s.name);

    if !s.generic_params.is_empty() {
        sig.push('<');
        sig.push_str(&s.generic_params.join(", "));
        sig.push('>');
    }

    sig
}

fn format_class_signature(c: &ClassDef) -> String {
    let mut sig = String::new();

    if c.visibility == Visibility::Public {
        sig.push_str("pub ");
    }

    sig.push_str("class ");
    sig.push_str(&c.name);

    if !c.generic_params.is_empty() {
        sig.push('<');
        sig.push_str(&c.generic_params.join(", "));
        sig.push('>');
    }

    sig
}

fn format_enum_signature(e: &EnumDef) -> String {
    let mut sig = String::new();

    if e.visibility == Visibility::Public {
        sig.push_str("pub ");
    }

    sig.push_str("enum ");
    sig.push_str(&e.name);

    if !e.generic_params.is_empty() {
        sig.push('<');
        sig.push_str(&e.generic_params.join(", "));
        sig.push('>');
    }

    sig
}

fn format_trait_signature(t: &TraitDef) -> String {
    let mut sig = String::new();

    if t.visibility == Visibility::Public {
        sig.push_str("pub ");
    }

    sig.push_str("trait ");
    sig.push_str(&t.name);

    if !t.generic_params.is_empty() {
        sig.push('<');
        sig.push_str(&t.generic_params.join(", "));
        sig.push('>');
    }

    sig
}

fn format_type(ty: &Type) -> String {
    match ty {
        Type::Simple(name) => name.clone(),
        Type::Generic { name, args } => {
            format!(
                "{}<{}>",
                name,
                args.iter().map(format_type).collect::<Vec<_>>().join(", ")
            )
        }
        Type::Array { element, size } => match size {
            Some(_) => format!("[{}; _]", format_type(element)),
            None => format!("[{}]", format_type(element)),
        },
        Type::Tuple(types) => format!(
            "({})",
            types.iter().map(format_type).collect::<Vec<_>>().join(", ")
        ),
        Type::Optional(inner) => format!("{}?", format_type(inner)),
        Type::Function { params, ret } => {
            let params_str = params
                .iter()
                .map(format_type)
                .collect::<Vec<_>>()
                .join(", ");
            match ret {
                Some(ret) => format!("fn({}) -> {}", params_str, format_type(ret)),
                None => format!("fn({})", params_str),
            }
        }
        Type::Pointer { kind, inner } => match kind {
            PointerKind::Unique => format!("&{}", format_type(inner)),
            PointerKind::Shared => format!("*{}", format_type(inner)),
            PointerKind::Weak => format!("-{}", format_type(inner)),
            PointerKind::Handle => format!("+{}", format_type(inner)),
            PointerKind::Borrow => format!("&{}", format_type(inner)),
            PointerKind::BorrowMut => format!("&mut {}", format_type(inner)),
        },
        Type::Union(types) => types
            .iter()
            .map(format_type)
            .collect::<Vec<_>>()
            .join(" | "),
        Type::DynTrait(trait_name) => format!("dyn {}", trait_name),
        Type::Constructor { target, args } => match args {
            Some(args) => format!(
                "Constructor[{}, ({})]",
                format_type(target),
                args.iter().map(format_type).collect::<Vec<_>>().join(", ")
            ),
            None => format!("Constructor[{}]", format_type(target)),
        },
        Type::Simd { lanes, element } => format!("vec[{}, {}]", lanes, format_type(element)),
        Type::Capability { capability, inner } => {
            use crate::ast::ReferenceCapability;
            let prefix = match capability {
                ReferenceCapability::Shared => "",
                ReferenceCapability::Exclusive => "mut ",
                ReferenceCapability::Isolated => "iso ",
            };
            format!("{}{}", prefix, format_type(inner))
        }
        Type::UnitWithRepr {
            name,
            repr,
            constraints,
        } => {
            let mut result = name.clone();
            if let Some(r) = repr {
                result.push(':');
                result.push_str(&r.to_string());
            }
            if let Some((start, end)) = constraints.range {
                result.push_str(&format!(" where range: {}..{}", start, end));
            }
            result
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::Parser;

    #[test]
    fn test_generate_function_docs() {
        let source = r#"/** Adds two numbers together */
fn add(x: Int, y: Int) -> Int:
    return x + y"#;

        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();
        let docs = generate(&module);

        assert_eq!(docs.items.len(), 1);
        assert_eq!(docs.items[0].name, "add");
        assert_eq!(docs.items[0].doc, "Adds two numbers together");
        assert_eq!(docs.items[0].kind, DocItemKind::Function);
    }

    #[test]
    fn test_generate_markdown() {
        let source =
            "/** Adds two numbers */\npub fn add(x: Int, y: Int) -> Int:\n    return x + y";

        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();
        let docs = generate(&module);
        let md = docs.to_markdown();

        assert!(md.contains("## Functions"));
        assert!(md.contains("`pub add`"));
        assert!(md.contains("Adds two numbers"));
    }

    #[test]
    fn test_generate_html() {
        let source = r#"/** Test function */
fn test():
    pass"#;

        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();
        let docs = generate(&module);
        let html = docs.to_html();

        assert!(html.contains("<!DOCTYPE html>"));
        assert!(html.contains("<h2>Functions</h2>"));
        assert!(html.contains("Test function"));
    }

    #[test]
    fn test_function_signature_format() {
        let source = "pub async fn fetch(url: String, timeout: Int?) -> String:\n    return url";
        let mut parser = Parser::new(source);
        let module = parser.parse().unwrap();
        let docs = generate(&module);

        assert!(docs.items[0].signature.contains("pub"));
        assert!(docs.items[0].signature.contains("async"));
        assert!(docs.items[0].signature.contains("fetch"));
    }
}
