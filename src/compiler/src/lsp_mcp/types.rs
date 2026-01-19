//! LSP MCP Type Definitions
//!
//! Types for exposing LSP functionality via MCP protocol.
//! Based on LSP specification with JSON serialization support.

use serde::{Deserialize, Serialize};

/// Position in a text document (0-based)
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Position {
    /// Line number (0-based)
    pub line: u32,
    /// Character offset (0-based)
    pub character: u32,
}

impl Position {
    pub fn new(line: u32, character: u32) -> Self {
        Self { line, character }
    }

    /// Convert from 1-based line/column to 0-based position
    pub fn from_one_based(line: usize, column: usize) -> Self {
        Self {
            line: line.saturating_sub(1) as u32,
            character: column.saturating_sub(1) as u32,
        }
    }
}

/// Range in a text document
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
pub struct Range {
    /// Start position (inclusive)
    pub start: Position,
    /// End position (exclusive)
    pub end: Position,
}

impl Range {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }

    /// Create a range from span data (1-based line/column)
    pub fn from_span(start_line: usize, start_col: usize, end_line: usize, end_col: usize) -> Self {
        Self {
            start: Position::from_one_based(start_line, start_col),
            end: Position::from_one_based(end_line, end_col),
        }
    }

    /// Create a single-line range
    pub fn single_line(line: u32, start_char: u32, end_char: u32) -> Self {
        Self {
            start: Position::new(line, start_char),
            end: Position::new(line, end_char),
        }
    }
}

/// Location in a document (URI + range)
#[derive(Debug, Clone, PartialEq, Eq, Serialize, Deserialize)]
pub struct Location {
    /// Document URI
    pub uri: String,
    /// Range within the document
    pub range: Range,
}

impl Location {
    pub fn new(uri: impl Into<String>, range: Range) -> Self {
        Self { uri: uri.into(), range }
    }
}

/// Symbol kind enumeration
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum SymbolKind {
    File,
    Module,
    Namespace,
    Package,
    Class,
    Method,
    Property,
    Field,
    Constructor,
    Enum,
    Interface,
    Function,
    Variable,
    Constant,
    String,
    Number,
    Boolean,
    Array,
    Object,
    Key,
    Null,
    EnumMember,
    Struct,
    Event,
    Operator,
    TypeParameter,
}

impl SymbolKind {
    /// Convert to LSP symbol kind number
    pub fn to_lsp_number(&self) -> u32 {
        match self {
            SymbolKind::File => 1,
            SymbolKind::Module => 2,
            SymbolKind::Namespace => 3,
            SymbolKind::Package => 4,
            SymbolKind::Class => 5,
            SymbolKind::Method => 6,
            SymbolKind::Property => 7,
            SymbolKind::Field => 8,
            SymbolKind::Constructor => 9,
            SymbolKind::Enum => 10,
            SymbolKind::Interface => 11,
            SymbolKind::Function => 12,
            SymbolKind::Variable => 13,
            SymbolKind::Constant => 14,
            SymbolKind::String => 15,
            SymbolKind::Number => 16,
            SymbolKind::Boolean => 17,
            SymbolKind::Array => 18,
            SymbolKind::Object => 19,
            SymbolKind::Key => 20,
            SymbolKind::Null => 21,
            SymbolKind::EnumMember => 22,
            SymbolKind::Struct => 23,
            SymbolKind::Event => 24,
            SymbolKind::Operator => 25,
            SymbolKind::TypeParameter => 26,
        }
    }
}

/// Information about a symbol in a document
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct SymbolInfo {
    /// Symbol name
    pub name: String,
    /// Symbol kind
    pub kind: SymbolKind,
    /// Range of the entire symbol definition
    pub range: Range,
    /// Range of the symbol name (for highlighting)
    pub selection_range: Range,
    /// Optional container name (e.g., class name for a method)
    #[serde(skip_serializing_if = "Option::is_none")]
    pub container_name: Option<String>,
    /// Child symbols (for hierarchical structure)
    #[serde(skip_serializing_if = "Vec::is_empty", default)]
    pub children: Vec<SymbolInfo>,
}

impl SymbolInfo {
    pub fn new(name: impl Into<String>, kind: SymbolKind, range: Range) -> Self {
        Self {
            name: name.into(),
            kind,
            range,
            selection_range: range,
            container_name: None,
            children: Vec::new(),
        }
    }

    pub fn with_selection_range(mut self, selection_range: Range) -> Self {
        self.selection_range = selection_range;
        self
    }

    pub fn with_container(mut self, container: impl Into<String>) -> Self {
        self.container_name = Some(container.into());
        self
    }

    pub fn with_children(mut self, children: Vec<SymbolInfo>) -> Self {
        self.children = children;
        self
    }
}

/// Hover information content
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HoverContents {
    /// Content kind (e.g., "markdown", "plaintext")
    pub kind: String,
    /// The actual content
    pub value: String,
}

impl HoverContents {
    pub fn markdown(value: impl Into<String>) -> Self {
        Self {
            kind: "markdown".to_string(),
            value: value.into(),
        }
    }

    pub fn plaintext(value: impl Into<String>) -> Self {
        Self {
            kind: "plaintext".to_string(),
            value: value.into(),
        }
    }
}

/// Hover information result
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct HoverInfo {
    /// Hover contents
    pub contents: HoverContents,
    /// Optional range for the hover
    #[serde(skip_serializing_if = "Option::is_none")]
    pub range: Option<Range>,
}

impl HoverInfo {
    pub fn new(contents: HoverContents) -> Self {
        Self { contents, range: None }
    }

    pub fn with_range(mut self, range: Range) -> Self {
        self.range = Some(range);
        self
    }
}

/// Diagnostic severity levels
#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DiagnosticSeverity {
    Error,
    Warning,
    Information,
    Hint,
}

impl DiagnosticSeverity {
    /// Convert to LSP severity number
    pub fn to_lsp_number(&self) -> u32 {
        match self {
            DiagnosticSeverity::Error => 1,
            DiagnosticSeverity::Warning => 2,
            DiagnosticSeverity::Information => 3,
            DiagnosticSeverity::Hint => 4,
        }
    }
}

/// Diagnostic information
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Diagnostic {
    /// Range of the diagnostic
    pub range: Range,
    /// Severity level
    pub severity: DiagnosticSeverity,
    /// Error/warning code
    #[serde(skip_serializing_if = "Option::is_none")]
    pub code: Option<String>,
    /// Source of the diagnostic (e.g., "simple-compiler")
    #[serde(skip_serializing_if = "Option::is_none")]
    pub source: Option<String>,
    /// Diagnostic message
    pub message: String,
}

impl Diagnostic {
    pub fn error(range: Range, message: impl Into<String>) -> Self {
        Self {
            range,
            severity: DiagnosticSeverity::Error,
            code: None,
            source: Some("simple-compiler".to_string()),
            message: message.into(),
        }
    }

    pub fn warning(range: Range, message: impl Into<String>) -> Self {
        Self {
            range,
            severity: DiagnosticSeverity::Warning,
            code: None,
            source: Some("simple-compiler".to_string()),
            message: message.into(),
        }
    }

    pub fn with_code(mut self, code: impl Into<String>) -> Self {
        self.code = Some(code.into());
        self
    }
}

/// Reference context for find references
#[derive(Debug, Clone, Copy, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ReferenceContext {
    /// The symbol definition
    Definition,
    /// A reference to the symbol
    Reference,
    /// A read access
    Read,
    /// A write access
    Write,
}

/// Reference location with context
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ReferenceLocation {
    /// Location of the reference
    #[serde(flatten)]
    pub location: Location,
    /// Context of the reference
    pub context: ReferenceContext,
}

impl ReferenceLocation {
    pub fn new(location: Location, context: ReferenceContext) -> Self {
        Self { location, context }
    }

    pub fn definition(uri: impl Into<String>, range: Range) -> Self {
        Self {
            location: Location::new(uri, range),
            context: ReferenceContext::Definition,
        }
    }

    pub fn reference(uri: impl Into<String>, range: Range) -> Self {
        Self {
            location: Location::new(uri, range),
            context: ReferenceContext::Reference,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_position_from_one_based() {
        let pos = Position::from_one_based(1, 1);
        assert_eq!(pos.line, 0);
        assert_eq!(pos.character, 0);

        let pos2 = Position::from_one_based(10, 5);
        assert_eq!(pos2.line, 9);
        assert_eq!(pos2.character, 4);
    }

    #[test]
    fn test_range_single_line() {
        let range = Range::single_line(5, 0, 10);
        assert_eq!(range.start.line, 5);
        assert_eq!(range.start.character, 0);
        assert_eq!(range.end.line, 5);
        assert_eq!(range.end.character, 10);
    }

    #[test]
    fn test_symbol_info_builder() {
        let symbol = SymbolInfo::new("test_function", SymbolKind::Function, Range::single_line(0, 0, 10))
            .with_container("TestClass");

        assert_eq!(symbol.name, "test_function");
        assert_eq!(symbol.kind, SymbolKind::Function);
        assert_eq!(symbol.container_name, Some("TestClass".to_string()));
    }

    #[test]
    fn test_diagnostic_builder() {
        let diag = Diagnostic::error(Range::single_line(0, 0, 5), "Test error").with_code("E001");

        assert_eq!(diag.severity, DiagnosticSeverity::Error);
        assert_eq!(diag.message, "Test error");
        assert_eq!(diag.code, Some("E001".to_string()));
    }

    #[test]
    fn test_json_serialization() {
        let location = Location::new("file:///test.spl", Range::single_line(0, 0, 10));
        let json = serde_json::to_string(&location).unwrap();
        assert!(json.contains("file:///test.spl"));

        let parsed: Location = serde_json::from_str(&json).unwrap();
        assert_eq!(parsed.uri, location.uri);
    }
}
