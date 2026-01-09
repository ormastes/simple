//! Module system statement parsing
//!
//! This module handles parsing of module system statements including:
//! - Module paths and import targets
//! - use and import statements
//! - mod declarations
//! - common use, export use, auto import
//! - requires capabilities

use crate::ast::*;
use crate::error::ParseError;
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    /// Parse a module path: crate.sys.http.router
    /// Returns the segments as a vector
    pub(crate) fn parse_module_path(&mut self) -> Result<ModulePath, ParseError> {
        let mut segments = Vec::new();

        // Handle relative imports (Python-style):
        // import .. as parent         -> [".."]
        // import ..sibling             -> ["..", "sibling"]
        // import ...grandparent        -> ["...", "grandparent"] (not yet supported, but future-proof)
        while self.check(&TokenKind::DoubleDot) {
            self.advance();
            segments.push("..".to_string());
        }

        // If we only have DoubleDots and hit end-of-path markers, we're done
        if !segments.is_empty() {
            // Check if this is a bare ".." import (import .. as name)
            if self.check(&TokenKind::As) || self.check(&TokenKind::Newline) || self.is_at_end() {
                return Ok(ModulePath::new(segments));
            }
            // Otherwise, we have DoubleDots followed by a path (import ..sibling)
            // Continue to parse the remaining path
        }

        // First segment (could be 'crate' keyword or identifier)
        if segments.is_empty() {
            if self.check(&TokenKind::Crate) {
                self.advance();
                segments.push("crate".to_string());
            } else {
                // Use expect_path_segment to allow keywords like 'unit', 'test', etc.
                segments.push(self.expect_path_segment()?);
            }
        } else {
            // We already have DoubleDots, now get the first real segment
            segments.push(self.expect_path_segment()?);
        }

        // Parse dot-separated segments
        while self.check(&TokenKind::Dot) {
            self.advance();

            // Check for glob: module.*
            if self.check(&TokenKind::Star) {
                break; // Stop, let caller handle *
            }

            // Check for group: module.{A, B}
            if self.check(&TokenKind::LBrace) {
                break; // Stop, let caller handle {}
            }

            // Use expect_path_segment to allow keywords as path segments
            segments.push(self.expect_path_segment()?);
        }

        Ok(ModulePath::new(segments))
    }

    /// Parse an import target: single item, alias, group, or glob
    /// Called after the module path is parsed
    pub(crate) fn parse_import_target(
        &mut self,
        last_segment: Option<String>,
    ) -> Result<ImportTarget, ParseError> {
        // Check for glob: *
        if self.check(&TokenKind::Star) {
            self.advance();
            return Ok(ImportTarget::Glob);
        }

        // Check for group: {A, B, C}
        if self.check(&TokenKind::LBrace) {
            self.advance();
            let mut targets = Vec::new();

            while !self.check(&TokenKind::RBrace) {
                // Use expect_path_segment to allow keywords like 'to', 'context' as import names
                let name = self.expect_path_segment()?;
                let target = if self.check(&TokenKind::As) {
                    self.advance();
                    let alias = self.expect_path_segment()?;
                    ImportTarget::Aliased { name, alias }
                } else {
                    ImportTarget::Single(name)
                };
                targets.push(target);

                if !self.check(&TokenKind::RBrace) {
                    self.expect(&TokenKind::Comma)?;
                }
            }
            self.expect(&TokenKind::RBrace)?;
            return Ok(ImportTarget::Group(targets));
        }

        // Single item (already parsed as last segment of path)
        if let Some(name) = last_segment {
            // Check for alias: as NewName
            if self.check(&TokenKind::As) {
                self.advance();
                let alias = self.expect_identifier()?;
                return Ok(ImportTarget::Aliased { name, alias });
            }
            return Ok(ImportTarget::Single(name));
        }

        Err(ParseError::unexpected_token(
            "import target",
            format!("{:?}", self.current.kind),
            self.current.span,
        ))
    }

    /// Parse use statement: use crate.module.Item
    /// use crate.module.{A, B}
    /// use crate.module.*
    /// use crate.module.Item as Alias
    /// use type crate.module.Item (type-only import)
    pub(crate) fn parse_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Use)?;

        // Check for 'type' keyword after 'use'
        let is_type_only = if self.check(&TokenKind::Type) {
            self.advance();
            true
        } else {
            false
        };

        self.parse_use_or_import_body(start_span, is_type_only)
    }

    /// Parse import statement (alias for use): import module.Item
    /// This is syntactic sugar for `use` - both work identically.
    /// import type module.Item is also supported.
    pub(crate) fn parse_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Import)?;

        // Check for 'type' keyword after 'import'
        let is_type_only = if self.check(&TokenKind::Type) {
            self.advance();
            true
        } else {
            false
        };

        self.parse_use_or_import_body(start_span, is_type_only)
    }

    /// Common body for use/import statements
    pub(super) fn parse_use_or_import_body(
        &mut self,
        start_span: Span,
        is_type_only: bool,
    ) -> Result<Node, ParseError> {
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
            is_type_only,
        }))
    }

    /// Parse mod declaration: mod name or pub mod name
    pub(crate) fn parse_mod(
        &mut self,
        visibility: Visibility,
        attributes: Vec<Attribute>,
    ) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mod)?;
        let name = self.expect_identifier()?;
        Ok(Node::ModDecl(ModDecl {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            name,
            visibility,
            attributes,
        }))
    }

    /// Parse common use: common use crate.module.*
    pub(crate) fn parse_common_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Common)?;
        self.expect(&TokenKind::Use)?;
        let (path, target) = self.parse_use_path_and_target()?;
        Ok(Node::CommonUseStmt(CommonUseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
        }))
    }

    /// Parse export use: export use router.Router
    pub(crate) fn parse_export_use(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Export)?;

        // Check for two syntaxes:
        // 1. export use X (traditional)
        // 2. export X, Y from module (JS/Python style)
        if self.check(&TokenKind::Use) {
            // Traditional: export use X
            self.advance();
            let (path, target) = self.parse_use_path_and_target()?;
            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target,
            }))
        } else if self.check(&TokenKind::LBrace) {
            // Style 3: export { X, Y, Z } from module (JS-style with braces)
            self.advance(); // consume '{'

            let mut items = Vec::new();
            // Skip leading newlines inside braces
            self.skip_newlines();

            while !self.check(&TokenKind::RBrace) {
                // Use expect_path_segment to allow keywords like 'let', 'mock' in exports
                items.push(self.expect_path_segment()?);

                // Skip newlines after item
                self.skip_newlines();

                if !self.check(&TokenKind::RBrace) {
                    // Allow trailing comma before closing brace
                    if self.check(&TokenKind::Comma) {
                        self.advance();
                        self.skip_newlines();
                    }
                }
            }
            self.expect(&TokenKind::RBrace)?;

            // 'from' should follow
            self.expect(&TokenKind::From)?;

            // Parse module path
            let module_path = self.parse_module_path()?;

            // Create export use statement with group import
            let targets: Vec<ImportTarget> = items
                .into_iter()
                .map(|name| ImportTarget::Single(name))
                .collect();

            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: module_path,
                target: ImportTarget::Group(targets),
            }))
        } else {
            // Two styles:
            // 1. export X, Y, Z from module (with 'from')
            // 2. export X, Y, Z (bare export, no 'from')

            // Parse list of identifiers
            // Use expect_path_segment to allow keywords like 'let', 'mock' in exports
            let mut items = Vec::new();
            items.push(self.expect_path_segment()?);

            while self.check(&TokenKind::Comma) {
                self.advance(); // consume ','
                items.push(self.expect_path_segment()?);
            }

            // Check if 'from' keyword is present
            if self.check(&TokenKind::From) {
                // Style 1: export X, Y from module
                self.advance(); // consume 'from'

                // Parse module path
                let module_path = self.parse_module_path()?;

                // Create export use statement with group import
                let targets: Vec<ImportTarget> = items
                    .into_iter()
                    .map(|name| ImportTarget::Single(name))
                    .collect();

                Ok(Node::ExportUseStmt(ExportUseStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    path: module_path,
                    target: ImportTarget::Group(targets),
                }))
            } else {
                // Style 2: bare export (export X, Y, Z)
                // Create export use statement with empty path
                // This marks the symbols for export without importing them
                let targets: Vec<ImportTarget> = items
                    .into_iter()
                    .map(|name| ImportTarget::Single(name))
                    .collect();

                Ok(Node::ExportUseStmt(ExportUseStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    path: ModulePath::new(Vec::new()), // Empty path for bare exports
                    target: ImportTarget::Group(targets),
                }))
            }
        }
    }

    /// Parse auto import: auto import router.route
    pub(crate) fn parse_auto_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Auto)?;
        self.expect(&TokenKind::Import)?;

        let path = self.parse_module_path()?;

        // Last segment is the macro name
        let mut segments = path.segments;
        let macro_name = segments.pop().unwrap_or_default();

        Ok(Node::AutoImportStmt(AutoImportStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path: ModulePath::new(segments),
            macro_name,
        }))
    }

    /// Parse requires capabilities statement: requires [pure, io, net]
    ///
    /// This declares the capabilities allowed in the current module.
    /// Must appear at the top of __init__.spl files.
    pub(crate) fn parse_requires_capabilities(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Requires)?;
        self.expect(&TokenKind::LBracket)?;

        let mut capabilities = Vec::new();

        // Parse capability list
        if !self.check(&TokenKind::RBracket) {
            loop {
                // Parse capability name as identifier
                let cap_name = self.expect_identifier()?;

                // Convert to Capability enum
                let capability = Capability::from_name(&cap_name).ok_or_else(|| {
                    ParseError::syntax_error_with_span(
                        format!(
                            "unknown capability '{}'. Valid capabilities: pure, io, net, fs, unsafe, gc",
                            cap_name
                        ),
                        self.previous.span,
                    )
                })?;

                capabilities.push(capability);

                // Check for comma or end
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Allow trailing comma
                    if self.check(&TokenKind::RBracket) {
                        break;
                    }
                } else {
                    break;
                }
            }
        }

        self.expect(&TokenKind::RBracket)?;

        Ok(Node::RequiresCapabilities(RequiresCapabilitiesStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            capabilities,
        }))
    }
}
