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
use crate::error_recovery::{ErrorHint, ErrorHintLevel};
use crate::parser_impl::core::Parser;
use crate::token::{Span, TokenKind};

impl<'a> Parser<'a> {
    /// Parse a module path: crate.sys.http.router
    /// Returns the segments as a vector
    pub(crate) fn parse_module_path(&mut self) -> Result<ModulePath, ParseError> {
        let mut segments = Vec::new();

        // Handle relative imports (Python-style):
        // import . as current          -> ["."] (current package)
        // import .sibling              -> [".", "sibling"]
        // import .. as parent          -> [".."]
        // import ..sibling             -> ["..", "sibling"]
        // import ...grandparent        -> ["...", "grandparent"] (not yet supported, but future-proof)

        // Handle single dot for same-directory imports: .definition
        if self.check(&TokenKind::Dot) {
            self.advance();
            segments.push(".".to_string());
            // The next segment should be the module name
            if !self.check(&TokenKind::Newline) && !self.is_at_end() && !self.check(&TokenKind::As) {
                segments.push(self.expect_path_segment()?);
                // Continue with remaining path segments
                while self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) {
                    if self.check(&TokenKind::DoubleColon) {
                        let warning = ErrorHint {
                            level: ErrorHintLevel::Warning,
                            message: "Deprecated: '::' in module paths".to_string(),
                            span: self.current.span,
                            suggestion: Some("Use '.' instead of '::'".to_string()),
                            help: Some("Example: use std.spec.* instead of use std::spec::*".to_string()),
                        };
                        self.error_hints.push(warning);
                    }
                    self.advance();

                    // Check for glob: module.*
                    if self.check(&TokenKind::Star) {
                        break; // Stop, let caller handle *
                    }

                    // Check for group: module.{A, B}
                    if self.check(&TokenKind::LBrace) {
                        break; // Stop, let caller handle {}
                    }

                    segments.push(self.expect_path_segment()?);
                }
            }
            return Ok(ModulePath::new(segments));
        }

        // Handle `...` (Ellipsis) as triple-dot relative import: ...grandparent
        while self.check(&TokenKind::Ellipsis) {
            self.advance();
            segments.push("...".to_string());
        }

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

        // Handle string-literal module paths: import "std/math", import "aes/utilities"
        if let TokenKind::FString(parts) = &self.current.kind {
            if parts.len() == 1 {
                if let crate::token::FStringToken::Literal(path_str) = &parts[0] {
                    let path_segments: Vec<String> = path_str.split('/').map(|s| s.to_string()).collect();
                    self.advance();
                    return Ok(ModulePath::new(path_segments));
                }
            }
        }
        if let TokenKind::String(path_str) = &self.current.kind {
            let path_segments: Vec<String> = path_str.split('/').map(|s| s.to_string()).collect();
            self.advance();
            return Ok(ModulePath::new(path_segments));
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

        // Parse dot-separated segments (also accept :: and / with deprecation warning)
        while self.check(&TokenKind::Dot) || self.check(&TokenKind::DoubleColon) || self.check(&TokenKind::Slash) {
            // Slash-separated path (legacy): import aes/utilities
            if self.check(&TokenKind::Slash) {
                self.advance();

                // Check for glob: module/*
                if self.check(&TokenKind::Star) {
                    break;
                }

                // Check for group: module/{A, B}
                if self.check(&TokenKind::LBrace) {
                    break;
                }

                segments.push(self.expect_path_segment()?);
                continue;
            }
            // Emit deprecation warning for '::' syntax
            if self.check(&TokenKind::DoubleColon) {
                let warning = ErrorHint {
                    level: ErrorHintLevel::Warning,
                    message: "Deprecated: '::' in module paths".to_string(),
                    span: self.current.span,
                    suggestion: Some("Use '.' instead of '::'".to_string()),
                    help: Some("Example: use std.spec.* instead of use std::spec::*".to_string()),
                };
                self.error_hints.push(warning);
            }
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
    pub(crate) fn parse_import_target(&mut self, last_segment: Option<String>) -> Result<ImportTarget, ParseError> {
        // Check for glob: *
        if self.check(&TokenKind::Star) {
            self.advance();
            return Ok(ImportTarget::Glob);
        }

        // Check for group: {A, B, C}
        if self.check(&TokenKind::LBrace) {
            self.advance();
            // Check for {*} glob pattern
            if self.check(&TokenKind::Star) {
                self.advance();
                self.expect(&TokenKind::RBrace)?;
                return Ok(ImportTarget::Glob);
            }
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
    /// DEPRECATED: Use `use` instead of `import`.
    /// import type module.Item is also supported.
    pub(crate) fn parse_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Emit deprecation warning for 'import' keyword
        let warning = ErrorHint {
            level: ErrorHintLevel::Warning,
            message: "Deprecated: 'import' keyword".to_string(),
            span: start_span,
            suggestion: Some("Use 'use' instead of 'import'".to_string()),
            help: Some("Example: use std.spec.* instead of import std.spec".to_string()),
        };
        self.error_hints.push(warning);

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

    /// Parse Python-style from-import: from module import Name or from module import {Name1, Name2}
    /// DEPRECATED: Use `use module.{...}` instead.
    /// Converts to use statement: from mmap import File -> use mmap.File
    pub(crate) fn parse_from_import(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;

        // Emit deprecation warning for 'from ... import' syntax
        let warning = ErrorHint {
            level: ErrorHintLevel::Warning,
            message: "Deprecated: 'from ... import' syntax".to_string(),
            span: start_span,
            suggestion: Some("Use 'use module.{...}' instead".to_string()),
            help: Some("Example: use mmap.{File, open} instead of from mmap import {File, open}".to_string()),
        };
        self.error_hints.push(warning);

        self.expect(&TokenKind::From)?;

        // Parse the module path (could be a single identifier or dotted path)
        let path = self.parse_module_path()?;

        // Expect 'import' keyword
        self.expect(&TokenKind::Import)?;

        // Parse what's being imported: single name, {group}, or *
        let target = if self.check(&TokenKind::Star) {
            self.advance();
            ImportTarget::Glob
        } else if self.check(&TokenKind::LBrace) {
            // Group import: from module import {A, B, C} or {*}
            self.advance();
            // Check for {*} glob pattern
            if self.check(&TokenKind::Star) {
                self.advance();
                self.expect(&TokenKind::RBrace)?;
                ImportTarget::Glob
            } else {
                let mut items = Vec::new();
                while !self.check(&TokenKind::RBrace) {
                    // Allow keywords as import names
                    let name = self.expect_path_segment()?;
                    if self.check(&TokenKind::As) {
                        self.advance();
                        let alias = self.expect_path_segment()?;
                        items.push(ImportTarget::Aliased { name, alias });
                    } else {
                        items.push(ImportTarget::Single(name));
                    }
                    if !self.check(&TokenKind::RBrace) {
                        self.expect(&TokenKind::Comma)?;
                    }
                }
                self.expect(&TokenKind::RBrace)?;
                ImportTarget::Group(items)
            } // end of non-glob group
        } else {
            // Single or comma-separated import: from module import A or from module import A, B, C
            let name = self.expect_path_segment()?;
            let first = if self.check(&TokenKind::As) {
                self.advance();
                let alias = self.expect_path_segment()?;
                ImportTarget::Aliased { name, alias }
            } else {
                ImportTarget::Single(name)
            };

            // Check for comma-separated list: from module import A, B, C
            if self.check(&TokenKind::Comma) {
                let mut items = vec![first];
                while self.check(&TokenKind::Comma) {
                    self.advance();
                    // Skip whitespace
                    while matches!(
                        self.current.kind,
                        TokenKind::Newline | TokenKind::Indent | TokenKind::Dedent
                    ) {
                        self.advance();
                    }
                    if self.is_at_end() {
                        break;
                    }
                    let item_name = self.expect_path_segment()?;
                    if self.check(&TokenKind::As) {
                        self.advance();
                        let alias = self.expect_path_segment()?;
                        items.push(ImportTarget::Aliased { name: item_name, alias });
                    } else {
                        items.push(ImportTarget::Single(item_name));
                    }
                }
                ImportTarget::Group(items)
            } else {
                first
            }
        };

        Ok(Node::UseStmt(UseStmt {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            path,
            target,
            is_type_only: false,
        }))
    }

    /// Common body for use/import statements
    pub(super) fn parse_use_or_import_body(
        &mut self,
        start_span: Span,
        is_type_only: bool,
    ) -> Result<Node, ParseError> {
        let (path, target) = self.parse_use_path_and_target()?;

        // Check for comma-separated imports: use a.B, c.D
        if self.check(&TokenKind::Comma) {
            // Multiple imports - collect into a MultiUse node
            let mut imports = vec![(path, target)];
            while self.check(&TokenKind::Comma) {
                self.advance(); // consume comma
                let (p, t) = self.parse_use_path_and_target()?;
                imports.push((p, t));
            }
            Ok(Node::MultiUse(MultiUse {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                imports,
                is_type_only,
            }))
        } else {
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
    }

    /// Parse mod declaration: mod name (external) or mod name: body (inline)
    /// External module: mod router
    /// Inline module: mod math:
    ///     fn add(a: i64, b: i64) -> i64:
    ///         a + b
    pub(crate) fn parse_mod(&mut self, visibility: Visibility, attributes: Vec<Attribute>) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::Mod)?;
        // Support dotted module paths: mod rules.helpers
        let mut name = self.expect_identifier()?;
        while self.check(&TokenKind::Dot) {
            self.advance();
            let segment = self.expect_path_segment()?;
            name = format!("{}.{}", name, segment);
        }

        // Check for inline module body
        let body = if self.check(&TokenKind::Colon) {
            self.advance(); // consume ':'
            self.expect(&TokenKind::Newline)?;
            self.expect(&TokenKind::Indent)?;

            let mut items = Vec::new();
            while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                // Skip newlines
                while self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    break;
                }
                items.push(self.parse_item()?);
            }
            if self.check(&TokenKind::Dedent) {
                self.advance();
            }
            Some(items)
        } else {
            None
        };

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
            body,
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

        // Handle bare `export` (no arguments) - used in conditional compilation blocks
        if self.check(&TokenKind::Newline) || self.check(&TokenKind::Dedent) || self.is_at_end() {
            return Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: ModulePath::new(Vec::new()),
                target: ImportTarget::Glob,
            }));
        }

        // Handle bare `export ()` — empty export list (no-op placeholder)
        if self.check(&TokenKind::LParen) {
            self.advance(); // consume '('
            self.expect(&TokenKind::RParen)?;
            return Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: ModulePath::new(Vec::new()),
                target: ImportTarget::Group(vec![]),
            }));
        }

        // Check for two syntaxes:
        // 1. export use X (traditional)
        // 2. export X, Y from module (JS/Python style)
        if self.check(&TokenKind::Use) {
            // Traditional: export use X
            self.advance();
            let (path, target) = self.parse_use_path_and_target()?;

            // Warn against glob exports - they expose too many interfaces
            if matches!(target, ImportTarget::Glob) {
                let warning = ErrorHint {
                    level: ErrorHintLevel::Warning,
                    message: "Avoid 'export use *' - exposes unnecessary interfaces".to_string(),
                    span: start_span,
                    suggestion: Some("Use explicit exports instead".to_string()),
                    help: Some("Example: export use module.{A, B, C} or export A, B from module".to_string()),
                };
                self.error_hints.push(warning);
            }

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
        } else if self.check(&TokenKind::Star) {
            // export * from module (glob re-export)
            // OR export * (bare — export all from current module)
            self.advance(); // consume '*'

            let module_path = if self.check(&TokenKind::From) {
                self.advance(); // consume 'from'
                self.parse_module_path()?
            } else {
                ModulePath::new(Vec::new()) // empty path = current module
            };

            Ok(Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path: module_path,
                target: ImportTarget::Glob,
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
            let targets: Vec<ImportTarget> = items.into_iter().map(|name| ImportTarget::Single(name)).collect();

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
            // Multiple styles:
            // 1. export module.* (re-export glob from submodule)
            // 2. export X, Y, Z from module (with 'from')
            // 3. export X, Y, Z (bare export, no 'from')

            // Parse first identifier
            // Use expect_path_segment to allow keywords like 'let', 'mock' in exports
            let first_item = self.expect_path_segment()?;

            // Check for dot (module path continuation)
            if self.check(&TokenKind::Dot) {
                // This is export module.* or export module.path.*
                // Parse as module path
                let mut segments = vec![first_item];

                while self.check(&TokenKind::Dot) {
                    self.advance(); // consume '.'

                    // Check for glob: module.*
                    if self.check(&TokenKind::Star) {
                        self.advance(); // consume '*'

                        // Warn against glob exports (but allow them - they're useful for re-exporting submodules)
                        let warning = ErrorHint {
                            level: ErrorHintLevel::Warning,
                            message: "Consider explicit exports to avoid exposing internal APIs".to_string(),
                            span: start_span,
                            suggestion: Some("Use 'export {A, B, C}' or 'export {A, B} from module' for better control".to_string()),
                            help: Some("Glob exports (export module.*) are acceptable for submodule re-exports in __init__.spl files".to_string()),
                        };
                        self.error_hints.push(warning);

                        return Ok(Node::ExportUseStmt(ExportUseStmt {
                            span: Span::new(
                                start_span.start,
                                self.previous.span.end,
                                start_span.line,
                                start_span.column,
                            ),
                            path: ModulePath::new(segments),
                            target: ImportTarget::Glob,
                        }));
                    }

                    // Check for group: export module.{A, B}
                    if self.check(&TokenKind::LBrace) {
                        // Parse the group items
                        self.advance(); // consume '{'

                        // Check for {*} glob pattern
                        if self.check(&TokenKind::Star) {
                            self.advance();
                            self.expect(&TokenKind::RBrace)?;
                            return Ok(Node::ExportUseStmt(ExportUseStmt {
                                span: Span::new(
                                    start_span.start,
                                    self.previous.span.end,
                                    start_span.line,
                                    start_span.column,
                                ),
                                path: ModulePath::new(segments),
                                target: ImportTarget::Glob,
                            }));
                        }

                        let mut targets = Vec::new();
                        self.skip_newlines();
                        while !self.check(&TokenKind::RBrace) {
                            let item_name = self.expect_path_segment()?;
                            let target = if self.check(&TokenKind::As) {
                                self.advance();
                                let alias = self.expect_path_segment()?;
                                ImportTarget::Aliased { name: item_name, alias }
                            } else {
                                ImportTarget::Single(item_name)
                            };
                            targets.push(target);
                            self.skip_newlines();
                            if !self.check(&TokenKind::RBrace) {
                                if self.check(&TokenKind::Comma) {
                                    self.advance();
                                    self.skip_newlines();
                                }
                            }
                        }
                        self.expect(&TokenKind::RBrace)?;
                        return Ok(Node::ExportUseStmt(ExportUseStmt {
                            span: Span::new(
                                start_span.start,
                                self.previous.span.end,
                                start_span.line,
                                start_span.column,
                            ),
                            path: ModulePath::new(segments),
                            target: ImportTarget::Group(targets),
                        }));
                    }

                    // Otherwise continue parsing path
                    segments.push(self.expect_path_segment()?);
                }

                // We have a dotted path like `export module.Item` or `export module.sub.Item`
                // Treat last segment as the exported item, rest as module path
                // Also handle comma-separated: `export module.Item, module.Item2`
                if segments.len() >= 2 {
                    let last_item = segments.pop().unwrap();
                    let module_path = ModulePath::new(segments.clone());
                    let mut targets = vec![ImportTarget::Single(last_item)];

                    // Check for comma-separated additional exports
                    while self.check(&TokenKind::Comma) {
                        self.advance(); // consume ','
                                        // Parse next dotted path or bare identifier
                        let next_item = self.expect_path_segment()?;
                        if self.check(&TokenKind::Dot) {
                            // Skip through module path to get to the item
                            // (assumes same module prefix for simplicity)
                            let mut _skip_segs = vec![next_item];
                            while self.check(&TokenKind::Dot) {
                                self.advance(); // consume '.'
                                _skip_segs.push(self.expect_path_segment()?);
                            }
                            // Last segment is the item
                            targets.push(ImportTarget::Single(_skip_segs.pop().unwrap()));
                        } else {
                            targets.push(ImportTarget::Single(next_item));
                        }
                    }

                    let target = if targets.len() == 1 {
                        targets.into_iter().next().unwrap()
                    } else {
                        ImportTarget::Group(targets)
                    };

                    return Ok(Node::ExportUseStmt(ExportUseStmt {
                        span: Span::new(
                            start_span.start,
                            self.previous.span.end,
                            start_span.line,
                            start_span.column,
                        ),
                        path: module_path,
                        target,
                    }));
                }

                // Single segment with no glob — shouldn't happen but error gracefully
                return Err(ParseError::syntax_error_with_span(
                    "Expected '.*', '{...}', or specific item after module path in export statement".to_string(),
                    self.current.span,
                ));
            }

            // Check for export assignment: export name = expr
            // This creates a const binding with export visibility
            if self.check(&TokenKind::Assign) {
                self.advance(); // consume '='
                let value = self.parse_expression()?;
                return Ok(Node::Const(ConstStmt {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    name: first_item,
                    ty: None,
                    value,
                    visibility: Visibility::Public,
                }));
            }

            // Not a module path - parse as identifier list
            let mut items = vec![first_item];

            let mut export_indent_depth = 0;
            while self.check(&TokenKind::Comma) {
                self.advance(); // consume ','
                                // Skip newlines and indents after comma to support multi-line export lists:
                                // export A, B,
                                //        C, D
                while self.check(&TokenKind::Newline) || self.check(&TokenKind::Indent) {
                    if self.check(&TokenKind::Indent) {
                        export_indent_depth += 1;
                    }
                    self.advance();
                }
                // If we hit dedent/EOF after trailing comma, stop
                if self.check(&TokenKind::Dedent) || self.is_at_end() || self.check(&TokenKind::From) {
                    break;
                }
                items.push(self.expect_path_segment()?);
            }
            // Consume matching dedents
            for _ in 0..export_indent_depth {
                if self.check(&TokenKind::Newline) {
                    self.advance();
                }
                if self.check(&TokenKind::Dedent) {
                    self.advance();
                }
            }

            // Check if 'from' keyword is present
            if self.check(&TokenKind::From) {
                // Style 2: export X, Y from module
                self.advance(); // consume 'from'

                // Parse module path
                let module_path = self.parse_module_path()?;

                // Create export use statement with group import
                let targets: Vec<ImportTarget> = items.into_iter().map(|name| ImportTarget::Single(name)).collect();

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
                // Style 3: bare export (export X, Y, Z)
                // Create export use statement with empty path
                // This marks the symbols for export without importing them
                let targets: Vec<ImportTarget> = items.into_iter().map(|name| ImportTarget::Single(name)).collect();

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

    /// Parse structured_export block:
    /// ```simple
    /// structured_export:
    ///     math.{sin, cos, tan}
    ///     util.format
    ///     MyClass
    /// ```
    /// Desugars to multiple ExportUseStmt nodes.
    pub(crate) fn parse_structured_export(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.expect(&TokenKind::StructuredExport)?;

        // Expect colon then indented block
        self.expect(&TokenKind::Colon)?;
        self.expect(&TokenKind::Newline)?;
        self.expect(&TokenKind::Indent)?;

        let mut entries = Vec::new();

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            // Parse a module path + optional target
            let (path, target) = self.parse_use_path_and_target()?;

            // Desugar to ExportUseStmt and push to pending_statements
            let export = Node::ExportUseStmt(ExportUseStmt {
                span: Span::new(
                    start_span.start,
                    self.previous.span.end,
                    start_span.line,
                    start_span.column,
                ),
                path,
                target,
            });
            entries.push(export);

            // Consume newline after entry
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        // Return the first entry, push rest to pending_statements
        if entries.is_empty() {
            // Empty structured_export block - return a pass node
            Ok(Node::Pass(PassStmt { span: start_span }))
        } else {
            // Push all but first to pending_statements for draining
            for entry in entries.drain(1..) {
                self.pending_statements.push(entry);
            }
            Ok(entries.into_iter().next().unwrap())
        }
    }
}
