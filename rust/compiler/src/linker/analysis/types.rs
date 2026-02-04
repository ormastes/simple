//! Symbol analysis type definitions

/// Symbol reference kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RefKind {
    /// Direct call reference.
    Call,
    /// Address-of reference.
    AddressOf,
    /// Data reference.
    Data,
    /// Type reference.
    Type,
}

/// Symbol visibility.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SymbolVisibility {
    /// Exported (public) symbol.
    Export,
    /// Imported (external) symbol.
    Import,
    /// Local (private) symbol.
    Local,
    /// Hidden (internal linkage).
    Hidden,
}

/// Information about a symbol for analysis.
#[derive(Debug, Clone)]
pub struct SymbolInfo {
    pub name: String,
    pub visibility: SymbolVisibility,
}
