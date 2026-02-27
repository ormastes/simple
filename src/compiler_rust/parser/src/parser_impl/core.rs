//! Core parser implementation
//!
//! This module contains the Parser struct, constructor methods, and main parse entry point.

use std::collections::VecDeque;

use crate::ast::*;
use crate::error::ParseError;
use crate::error_recovery::ErrorHint;
use crate::lexer::Lexer;
use crate::macro_registry::MacroRegistry;
use crate::token::{Span, Token, TokenKind};

/// Maximum iterations allowed in a single parsing loop before detecting a potential infinite loop.
/// This prevents hangs when the lexer doesn't emit proper tokens or token consumption fails.
pub const MAX_LOOP_ITERATIONS: usize = 100_000;

/// Parser mode controlling strictness of no-parentheses call syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum ParserMode {
    /// Normal mode: Allow nested no-paren calls (current behavior)
    #[default]
    Normal,
    /// Strict mode: Allow only ONE level of no-paren call.
    /// Inner function calls within arguments must use parentheses.
    /// Used for GPU kernel code to prevent ambiguity.
    Strict,
}

/// Debug mode for parser diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum DebugMode {
    /// No debug output
    #[default]
    Off,
    /// Basic debug output (function entry/exit)
    Basic,
    /// Verbose debug output (every token consumed)
    Verbose,
}

pub struct Parser<'a> {
    pub(crate) lexer: Lexer<'a>,
    pub(crate) current: Token,
    pub(crate) previous: Token,
    #[allow(dead_code)]
    source: &'a str,
    /// Buffer for lookahead tokens (used for multi-token peek operations)
    pub(crate) pending_tokens: VecDeque<Token>,
    /// Parser mode (Normal or Strict)
    pub(crate) mode: ParserMode,
    /// Depth of no-paren calls (for strict mode enforcement)
    pub(crate) no_paren_depth: u32,
    /// Debug mode for diagnostics
    pub(crate) debug_mode: DebugMode,
    /// Call depth for debug tracing
    pub(crate) debug_depth: usize,
    /// Macro registry for LL(1) macro integration
    pub(crate) macro_registry: MacroRegistry,
    /// Current scope for macro symbol registration (e.g., "module", "class:ClassName")
    pub(crate) current_scope: String,
    /// Collected error hints (helpful messages for common mistakes)
    pub(crate) error_hints: Vec<ErrorHint>,
    /// Count of INDENT tokens consumed during pattern parsing that need matching DEDENTs
    /// consumed after the match arm body. Reset to 0 after consuming the dedents.
    pub(crate) pattern_indent_count: usize,
    /// When true, postfix parsing won't consume `{ ... }` after field access.
    /// Used to prevent ambiguity in `if cond { body }` syntax.
    pub(crate) no_brace_postfix: bool,
    /// Buffer for statements produced by multi-node desugaring (e.g., structured_export)
    pub(crate) pending_statements: Vec<Node>,
    /// Count of INDENT tokens consumed during binary expression line continuation
    /// that need matching DEDENTs consumed after the expression.
    pub(crate) binary_indent_count: usize,
    /// Count of unmatched DEDENTs from multi-line expression continuation.
    /// When `consume_dedents_for_method_chain` can't consume all DEDENTs immediately
    /// (because the DEDENTs appear later in the token stream, after block bodies),
    /// this counter tracks how many should be consumed at a later point (e.g., after
    /// an if-block before checking for elif/else).
    pub(crate) deferred_dedent_count: usize,
}

impl<'a> Parser<'a> {
    pub fn new(source: &'a str) -> Self {
        let mut lexer = Lexer::new(source);
        let current = lexer.next_token();
        let previous = Token::new(TokenKind::Eof, Span::new(0, 0, 1, 1), String::new());

        let mut parser = Self {
            lexer,
            current,
            previous,
            source,
            pending_tokens: VecDeque::new(),
            mode: ParserMode::Normal,
            no_paren_depth: 0,
            debug_mode: DebugMode::Off,
            debug_depth: 0,
            macro_registry: MacroRegistry::new(),
            current_scope: "module".to_string(),
            error_hints: Vec::new(),
            pattern_indent_count: 0,
            no_brace_postfix: false,
            pending_statements: Vec::new(),
            binary_indent_count: 0,
            deferred_dedent_count: 0,
        };

        // Check for common mistakes in the initial token
        // (since it was loaded via lexer.next_token() bypassing advance())
        let next = parser.lexer.next_token();
        parser.pending_tokens.push_back(next.clone());
        let next_token = Some(&parser.pending_tokens[0]);

        use crate::error_recovery::detect_common_mistake;
        if let Some(mistake) = detect_common_mistake(&parser.current, &parser.previous, next_token) {
            use crate::error_recovery::{CommonMistake, ErrorHint, ErrorHintLevel};
            let level = match mistake {
                CommonMistake::PythonDef
                | CommonMistake::PythonTrue
                | CommonMistake::PythonFalse
                | CommonMistake::RustLetMut
                | CommonMistake::JavaPublicClass
                | CommonMistake::JavaVoid
                | CommonMistake::JavaNew
                | CommonMistake::JavaThis
                | CommonMistake::TsFunction
                | CommonMistake::TsConst
                | CommonMistake::TsInterface
                | CommonMistake::CppNamespace
                | CommonMistake::CppTemplate
                | CommonMistake::CTypeFirst
                | CommonMistake::MissingColon => ErrorHintLevel::Error,
                // PythonNone is now a warning because None is also a valid Option variant
                CommonMistake::PythonNone => ErrorHintLevel::Warning,
                CommonMistake::VerboseReturnType
                | CommonMistake::ExplicitSelf
                | CommonMistake::WrongBrackets
                | CommonMistake::CSemicolon
                | CommonMistake::SemicolonAfterBlock => ErrorHintLevel::Warning,
                CommonMistake::TsLet | CommonMistake::PythonSelf | CommonMistake::RustFnMut => ErrorHintLevel::Info,
                CommonMistake::RustLifetime
                | CommonMistake::RustMacro
                | CommonMistake::RustTurbofish
                | CommonMistake::TsArrowFunction
                | CommonMistake::PythonElif => ErrorHintLevel::Hint,
                CommonMistake::MissingCommaInArgs
                | CommonMistake::MissingColonBeforeBlock
                | CommonMistake::DictInsteadOfStruct
                | CommonMistake::MissingIndentAfterColon
                | CommonMistake::WrongIndentLevel => ErrorHintLevel::Error,
            };

            let hint = ErrorHint {
                level,
                message: format!("Common mistake detected: {}", mistake.suggestion()),
                span: parser.current.span.clone(),
                suggestion: Some(mistake.suggestion()),
                help: Some(mistake.message()),
            };

            parser.error_hints.push(hint);
        }

        parser
    }

    /// Create a parser for parsing inline expressions (e.g., f-string interpolations).
    /// Unlike `new()`, this parser does NOT treat leading whitespace as indentation,
    /// which allows expressions like ` x + y ` to parse correctly.
    pub fn new_expression(source: &'a str) -> Self {
        let mut lexer = Lexer::new_expression(source);
        let current = lexer.next_token();
        let previous = Token::new(TokenKind::Eof, Span::new(0, 0, 1, 1), String::new());

        Self {
            lexer,
            current,
            previous,
            source,
            pending_tokens: VecDeque::new(),
            mode: ParserMode::Normal,
            no_paren_depth: 0,
            debug_mode: DebugMode::Off,
            debug_depth: 0,
            macro_registry: MacroRegistry::new(),
            current_scope: "module".to_string(),
            error_hints: Vec::new(),
            pattern_indent_count: 0,
            no_brace_postfix: false,
            pending_statements: Vec::new(),
            binary_indent_count: 0,
            deferred_dedent_count: 0,
        }
    }

    /// Create a parser with LL(1) macro integration enabled.
    /// When enabled, macro contracts are processed at parse time and
    /// introduced symbols are immediately registered in the symbol table.
    pub fn with_ll1_macros(source: &'a str) -> Self {
        let mut parser = Self::new(source);
        parser.macro_registry.set_ll1_mode(true);
        parser
    }

    /// Get a reference to the macro registry
    pub fn macro_registry(&self) -> &MacroRegistry {
        &self.macro_registry
    }

    /// Get a mutable reference to the macro registry
    pub fn macro_registry_mut(&mut self) -> &mut MacroRegistry {
        &mut self.macro_registry
    }

    /// Create a parser with a specific mode (Normal or Strict).
    /// Strict mode requires parentheses for inner function calls within no-paren call arguments.
    pub fn with_mode(source: &'a str, mode: ParserMode) -> Self {
        let mut parser = Self::new(source);
        parser.mode = mode;
        parser
    }

    /// Create a parser with debug mode enabled.
    /// Debug mode outputs parsing trace information to stderr.
    pub fn with_debug(source: &'a str, debug_mode: DebugMode) -> Self {
        let mut parser = Self::new(source);
        parser.debug_mode = debug_mode;
        parser
    }

    /// Set debug mode on an existing parser
    pub fn set_debug_mode(&mut self, mode: DebugMode) {
        self.debug_mode = mode;
    }

    /// Get accumulated error hints (helpful messages for common mistakes)
    pub fn error_hints(&self) -> &[ErrorHint] {
        &self.error_hints
    }

    /// Clear accumulated error hints
    pub fn clear_error_hints(&mut self) {
        self.error_hints.clear();
    }

    /// Output debug trace message if debug mode is enabled
    #[inline]
    pub(crate) fn debug_trace(&self, msg: &str) {
        if self.debug_mode != DebugMode::Off {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}{}", indent, msg);
        }
    }

    /// Output verbose debug trace (token-level)
    #[inline]
    pub(crate) fn debug_verbose(&self, msg: &str) {
        if self.debug_mode == DebugMode::Verbose {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}{}", indent, msg);
        }
    }

    /// Enter a parsing function (for debug tracing)
    #[inline]
    pub(crate) fn debug_enter(&mut self, name: &str) {
        if self.debug_mode != DebugMode::Off {
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}> {} (token: {:?})", indent, name, self.current.kind);
            self.debug_depth += 1;
        }
    }

    /// Exit a parsing function (for debug tracing)
    #[inline]
    pub(crate) fn debug_exit(&mut self, name: &str) {
        if self.debug_mode != DebugMode::Off {
            if self.debug_depth > 0 {
                self.debug_depth -= 1;
            }
            let indent = "  ".repeat(self.debug_depth);
            eprintln!("[PARSER] {}< {}", indent, name);
        }
    }

    /// Check for potential infinite loop in parsing
    /// Returns an error if iteration count exceeds MAX_LOOP_ITERATIONS
    #[inline]
    pub(crate) fn check_loop_limit(&self, iterations: usize, context: &str) -> Result<(), ParseError> {
        if iterations >= MAX_LOOP_ITERATIONS {
            Err(ParseError::syntax_error_with_span(
                format!(
                    "Parser iteration limit exceeded in {} (possible infinite loop). \
                     Current token: {:?} at line {}, col {}",
                    context, self.current.kind, self.current.span.line, self.current.span.column
                ),
                self.current.span,
            ))
        } else {
            Ok(())
        }
    }

    pub fn parse(&mut self) -> Result<Module, ParseError> {
        self.debug_trace("Starting parse()");
        let mut items = Vec::new();
        let mut iterations = 0usize;

        while !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_module")?;
            iterations += 1;

            // Skip newlines at top level
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.is_at_end() {
                break;
            }

            self.debug_verbose(&format!("Parsing item {}", iterations));
            items.push(self.parse_item()?);
        }

        self.debug_trace(&format!("Finished parse(), {} items", items.len()));
        Ok(Module { name: None, items })
    }

    pub(crate) fn parse_item(&mut self) -> Result<Node, ParseError> {
        // Drain pending statements from multi-node desugaring (e.g., structured_export)
        if !self.pending_statements.is_empty() {
            return Ok(self.pending_statements.remove(0));
        }

        // Skip leading newlines
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        // Check for doc comment before item
        let doc_comment = self.try_parse_doc_comment();

        // Handle metadata/config blocks: `arch { ... }`, `config { ... }` etc.
        // These are identifier followed by `{` containing key = value pairs.
        // Check before the match to avoid borrow checker issues with match guards.
        let is_metadata_block = matches!(&self.current.kind,
            TokenKind::Identifier { name, .. }
                if name == "arch" || name == "config" || name == "metadata"
        ) && self.peek_is(&TokenKind::LBrace);

        if is_metadata_block {
            return self.parse_metadata_block();
        }

        // `me` starts a mutable method declaration (me method_name(...):)
        // BUT `me.field` or `me.method()` is an expression (field access/method call on self).
        // Similarly, `gen` and `kernel` start function declarations but can also be variable names.
        // Disambiguate by checking what follows: dot/assign/lparen means expression, identifier means decl.
        // Check before the match to avoid borrow checker issues with match guards.
        let is_me_method_decl = matches!(&self.current.kind, TokenKind::Me)
            && !self.peek_is(&TokenKind::Dot);
        let is_gen_or_kernel_decl = matches!(&self.current.kind, TokenKind::Gen | TokenKind::Kernel)
            && !self.peek_is(&TokenKind::Dot)
            && !self.peek_is(&TokenKind::Assign)
            && !self.peek_is(&TokenKind::LParen);
        // `match` is usually a statement keyword, but can be used as a variable name:
        //   for match in matches: results.push(match.0)
        // If followed by `.` or `=`, treat as an expression/identifier.
        let is_match_stmt = matches!(&self.current.kind, TokenKind::Match)
            && !self.peek_is(&TokenKind::Dot)
            && !self.peek_is(&TokenKind::Assign)
            && !self.peek_is(&TokenKind::Colon)
            && !self.peek_is(&TokenKind::And)
            && !self.peek_is(&TokenKind::Or)
            && !self.peek_is(&TokenKind::Eq)
            && !self.peek_is(&TokenKind::NotEq)
            && !self.peek_is(&TokenKind::RParen)
            && !self.peek_is(&TokenKind::Comma)
            && !self.peek_is(&TokenKind::Newline)
            && !self.peek_is(&TokenKind::Eof);
        // Allow 'continue', 'break', 'return' as variable names at statement level
        // e.g., `continue = false`, `break.field`
        let is_continue_as_ident = matches!(&self.current.kind, TokenKind::Continue)
            && (self.peek_is(&TokenKind::Assign) || self.peek_is(&TokenKind::Dot));
        let is_break_as_ident = matches!(&self.current.kind, TokenKind::Break)
            && (self.peek_is(&TokenKind::Assign) || self.peek_is(&TokenKind::Dot));
        let is_return_as_ident = matches!(&self.current.kind, TokenKind::Return)
            && (self.peek_is(&TokenKind::Assign) || self.peek_is(&TokenKind::Dot));

        match &self.current.kind {
            TokenKind::Hash => self.parse_attributed_item_with_doc(doc_comment),
            TokenKind::At => self.parse_decorated_function_with_doc(doc_comment),
            TokenKind::Fn => {
                // Disambiguate: fn name(...) is function definition,
                // fn(...) is lambda or function call (expression statement)
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::LParen) {
                    // fn( — could be lambda or call to variable named 'fn'
                    // Treat as expression statement (parse_primary handles fn( disambiguation)
                    self.parse_expression_or_assignment()
                } else if matches!(next.kind, TokenKind::Identifier { .. }) {
                    // fn name — function definition
                    self.parse_function_with_doc(doc_comment)
                } else {
                    // fn followed by something else — try as function definition first
                    self.parse_function_with_doc(doc_comment)
                }
            }
            TokenKind::Kernel | TokenKind::Gen if is_gen_or_kernel_decl => {
                self.parse_function_with_doc(doc_comment)
            }
            TokenKind::Me if is_me_method_decl => {
                self.parse_function_with_doc(doc_comment)
            }
            TokenKind::Async => self.parse_async_function_with_doc(doc_comment),
            TokenKind::Sync => self.parse_sync_function_with_doc(doc_comment),
            TokenKind::Struct => self.parse_struct_with_doc(doc_comment),
            TokenKind::Class => self.parse_class_with_doc(doc_comment),
            TokenKind::Enum => self.parse_enum_with_doc(doc_comment),
            TokenKind::Union => self.parse_union_with_doc(doc_comment),
            TokenKind::Trait => self.parse_trait_with_doc(doc_comment),
            TokenKind::Mixin => self.parse_mixin(),
            TokenKind::Impl => self.parse_impl(),
            TokenKind::Actor => self.parse_actor(),
            TokenKind::Pub => {
                self.advance();
                self.parse_pub_item_with_doc(doc_comment)
            }
            TokenKind::Mut => self.parse_mut_let(), // Legacy: mut let
            TokenKind::Let => self.parse_let(),     // Legacy: let
            TokenKind::Val => self.parse_val(),     // New: val (immutable)
            TokenKind::Var => self.parse_var(),     // New: var (mutable)
            TokenKind::Const => self.parse_const(),
            TokenKind::Static => self.parse_static(),
            TokenKind::Shared => self.parse_shared_let(),
            TokenKind::Ghost => self.parse_ghost_let(),
            TokenKind::Alias => {
                // Check if this is a class alias (alias NewName = OldName) or identifier usage
                // Class alias names must be PascalCase (start with uppercase)
                let next = self.peek_next();

                // Check if next token is an uppercase identifier (class alias pattern)
                if let TokenKind::Identifier { name, .. } = &next.kind {
                    if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                        // PascalCase identifier after 'alias' - treat as class alias
                        self.parse_class_alias()
                    } else {
                        // lowercase identifier after 'alias' - treat as expression
                        self.parse_expression_or_assignment()
                    }
                } else {
                    // Not followed by identifier - treat 'alias' as expression
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Type => {
                // Check if this is a type alias (type Name = ...) or expression (expect type to eq)
                // Simple heuristic: type alias names are PascalCase (start with uppercase)
                // Expression context uses lowercase like "expect type to eq"
                let next = self.peek_next();

                // Check if next token is an uppercase identifier (type alias pattern)
                if let TokenKind::Identifier { name, .. } = &next.kind {
                    if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                        // PascalCase identifier after 'type' - treat as type alias
                        self.parse_type_alias()
                    } else {
                        // lowercase identifier after 'type' - treat as expression
                        self.parse_expression_or_assignment()
                    }
                } else {
                    // Not followed by identifier - treat 'type' as expression
                    self.parse_expression_or_assignment()
                }
            }
            // Low-level features - disambiguate keyword vs identifier usage
            TokenKind::Asm => {
                // asm: "..." or asm match: ... -> inline assembly
                // asm = ... or asm.method() -> expression (variable named 'asm')
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Colon | TokenKind::Match) {
                    self.parse_asm()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Bitfield => {
                // bitfield Name...: -> bitfield definition
                // bitfield as identifier (import path, variable) -> expression
                let next = self.peek_next();
                if matches!(&next.kind, TokenKind::Identifier { name, .. } if name.chars().next().map_or(false, |c| c.is_uppercase())) {
                    self.parse_bitfield()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Newtype => {
                // newtype Name = ... -> newtype definition
                // newtype as identifier -> expression
                let next = self.peek_next();
                if matches!(&next.kind, TokenKind::Identifier { name, .. } if name.chars().next().map_or(false, |c| c.is_uppercase())) {
                    self.parse_newtype()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Extend => {
                // extend TypeName: -> extension block
                // extend as identifier (method call, import, etc.) -> expression
                let next = self.peek_next();
                if matches!(&next.kind, TokenKind::Identifier { name, .. } if name.chars().next().map_or(false, |c| c.is_uppercase())) {
                    self.parse_extend()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Comptime => {
                // comptime val ... or comptime fn ... -> compile-time marker
                // comptime as identifier -> expression
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Val | TokenKind::Fn) {
                    self.parse_comptime_val()
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Unit => self.parse_unit(),
            TokenKind::HandlePool => self.parse_handle_pool(),
            TokenKind::Extern => self.parse_extern(),
            TokenKind::Macro => self.parse_macro_def(),
            TokenKind::Literal => self.parse_literal_function(),
            // Module system (Features #104-111)
            TokenKind::Use => self.parse_use(),
            TokenKind::Import => self.parse_import(), // alias for use
            TokenKind::From => {
                // Disambiguate: 'from module import ...' vs 'from' as identifier
                // Only route to parse_from_import when followed by a valid module name.
                // NOTE: Do NOT include String/FString here — that would catch
                // `import X from "path"` where `from` appears after the import target.
                let next = self.peek_next();
                if matches!(next.kind,
                    TokenKind::Identifier { .. }
                    | TokenKind::Match  // used as module name in lz77/match.spl
                    | TokenKind::Mod    // used as module name in failsafe/__init__.spl
                    | TokenKind::Dot    // from .module import (relative import)
                ) {
                    self.parse_from_import() // Python-style: from module import {...}
                } else {
                    // Not followed by module name - treat 'from' as expression
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Mod => self.parse_mod(Visibility::Private, vec![]),
            TokenKind::Common => self.parse_common_use(),
            TokenKind::Export => self.parse_export_use(),
            TokenKind::StructuredExport => self.parse_structured_export(),
            TokenKind::Auto => self.parse_auto_import(),
            TokenKind::Requires => self.parse_requires_capabilities(),
            // AOP & Unified Predicates (#1000-1050)
            TokenKind::On => self.parse_aop_advice().map(Node::AopAdvice),
            TokenKind::Bind => {
                // Disambiguate between:
                // - DI binding: `bind on pc{...} -> Impl`
                // - Interface binding: `bind [static|dyn] Interface = ImplType`
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::On) {
                    self.parse_di_binding().map(Node::DiBinding)
                } else {
                    self.parse_interface_binding()
                }
            }
            TokenKind::Forbid | TokenKind::Allow => self.parse_arch_rule().map(Node::ArchitectureRule),
            TokenKind::Mock => self.parse_mock_decl().map(Node::MockDecl),
            TokenKind::If => self.parse_if(),
            TokenKind::IfSuspend => self.parse_if_suspend(),
            TokenKind::Match if is_match_stmt => self.parse_match_stmt(),
            TokenKind::MatchSuspend => self.parse_match_suspend(),
            TokenKind::For => self.parse_for(),
            TokenKind::ForSuspend => self.parse_for_suspend(),
            TokenKind::While => self.parse_while(),
            TokenKind::WhileSuspend => self.parse_while_suspend(),
            TokenKind::Loop => self.parse_loop(),
            TokenKind::Return if is_return_as_ident => self.parse_expression_or_assignment(),
            TokenKind::Break if is_break_as_ident => self.parse_expression_or_assignment(),
            TokenKind::Continue if is_continue_as_ident => self.parse_expression_or_assignment(),
            TokenKind::Return => self.parse_return(),
            TokenKind::Break => self.parse_break(),
            TokenKind::Continue => self.parse_continue(),
            TokenKind::Pass => self.parse_pass(),
            TokenKind::Skip => self.parse_skip(),
            TokenKind::Defer => self.parse_defer(),
            TokenKind::Assert => self.parse_assert(),
            TokenKind::Assume => self.parse_assume(),
            TokenKind::Admit => self.parse_admit(),
            // "calc" is parsed contextually - not a reserved keyword
            TokenKind::Identifier { name, .. } if name == "calc" => {
                // Check if followed by colon - if so, it's a calc statement
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Colon) {
                    self.parse_calc()
                } else {
                    // Just an identifier named "calc" - parse as expression
                    self.parse_expression_or_assignment()
                }
            }
            TokenKind::Context => {
                // Check if this is a context statement (context expr:) or function call (context(...)) or BDD DSL (context "string":)
                let next = self.peek_next();

                // If next token is a string literal, treat as BDD expression (no-paren call)
                if matches!(
                    &next.kind,
                    TokenKind::String(_) | TokenKind::RawString(_) | TokenKind::FString(_)
                ) {
                    self.parse_expression_or_assignment()
                // If next token is an opening paren, treat as function call
                } else if matches!(&next.kind, TokenKind::LParen) {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_context()
                }
            }
            TokenKind::With => self.parse_with(),
            // Lean 4 verification blocks
            // Note: lean{...} (no space) is handled as CustomBlock by lexer
            TokenKind::CustomBlock { kind, .. } if kind == "lean" => self.parse_lean_custom_block_as_node(),
            // lean import "..." and lean hint: "..." need contextual check since "lean" is also a valid identifier
            TokenKind::Identifier { name, .. } if name == "lean" => {
                // Check if this is "lean import" or "lean hint" - if so, parse as lean block/hint
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Import) {
                    self.parse_lean_import_block()
                } else if matches!(&next.kind, TokenKind::Identifier { name, .. } if name == "hint") {
                    // VER-020: Parse lean hint: "tactic"
                    self.parse_lean_hint()
                } else {
                    // Just an identifier named "lean" - parse as expression
                    self.parse_expression_or_assignment()
                }
            }
            // Gherkin-style system test DSL (Features #606-610)
            TokenKind::Feature => self.parse_feature(),
            TokenKind::Scenario => self.parse_scenario(),
            TokenKind::Examples => {
                // Check if this is an expression/assignment vs a Gherkin examples block
                // Gherkin examples: `examples name:` - followed by identifier then colon
                // Expression uses: assignment, method call, index, return value
                if self.peek_is(&TokenKind::Assign)
                    || self.peek_is(&TokenKind::Dot)
                    || self.peek_is(&TokenKind::LBracket)
                    || self.peek_is(&TokenKind::LParen)
                    || self.peek_is(&TokenKind::Newline)
                    || self.peek_is(&TokenKind::Dedent)
                {
                    self.parse_expression_or_assignment()
                } else {
                    self.parse_examples()
                }
            }
            TokenKind::Given | TokenKind::Then | TokenKind::AndThen => self.parse_step_ref_as_node(),
            TokenKind::When => {
                // Disambiguate `when COND:` (conditional compilation) from `when "step":` (BDD/Gherkin)
                // If followed by an identifier (not a string), treat as conditional compilation
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Identifier { .. } | TokenKind::Not) {
                    self.parse_when_block()
                } else {
                    self.parse_step_ref_as_node()
                }
            }
            // Wildcard suspension: _ ~= expr (discard awaited result)
            TokenKind::Underscore => self.parse_wildcard_suspend(),
            // `module name:` is an alias for `mod name:` (inline module block)
            TokenKind::Identifier { name, .. } if name == "module" => {
                // Check if followed by an identifier (module name) - if so, treat like mod
                let next = self.peek_next();
                if matches!(next.kind, TokenKind::Identifier { .. }) {
                    // Replace 'module' identifier with Mod keyword behavior
                    self.advance(); // consume 'module' identifier
                    // Now parse the rest like `mod name: ...` but without expecting 'mod' keyword
                    let start_span = self.previous.span;
                    let mod_name = self.expect_identifier()?;
                    let body = if self.check(&TokenKind::Colon) {
                        self.advance();
                        self.expect(&TokenKind::Newline)?;
                        self.expect(&TokenKind::Indent)?;
                        let mut items = Vec::new();
                        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
                            while self.check(&TokenKind::Newline) { self.advance(); }
                            if self.check(&TokenKind::Dedent) { break; }
                            items.push(self.parse_item()?);
                        }
                        if self.check(&TokenKind::Dedent) { self.advance(); }
                        Some(items)
                    } else {
                        None
                    };
                    Ok(Node::ModDecl(crate::ast::ModDecl {
                        span: crate::token::Span::new(
                            start_span.start, self.previous.span.end, start_span.line, start_span.column,
                        ),
                        name: mod_name,
                        visibility: crate::ast::Visibility::Private,
                        attributes: vec![],
                        body,
                    }))
                } else {
                    self.parse_expression_or_assignment()
                }
            }
            // Note: Implicit val/var (`name = expr`) is experimental/future.
            // Currently disabled because it conflicts with assignment syntax.
            // When enabled, it needs scope analysis to distinguish new bindings from reassignment.
            // The parse_implicit_val() method exists in var_decl.rs for future use.
            _ => self.parse_expression_or_assignment(),
        }
    }

    pub(crate) fn parse_block(&mut self) -> Result<Block, ParseError> {
        // Expect NEWLINE then INDENT
        self.expect(&TokenKind::Newline)?;

        // Simple supports "flat body" pattern where block body appears on the
        // next line at the SAME indentation level (no indent token):
        //   if cond:
        //   return val          # <-- same indent as `if`
        //
        // Handle by checking if next token is a valid statement-start token
        // instead of an Indent. If so, parse a single-statement body.
        if !self.check(&TokenKind::Indent) {
            // Skip blank lines before checking
            while self.check(&TokenKind::Newline) {
                self.advance();
            }

            if self.is_statement_start() {
                let start_span = self.current.span;
                let stmt = self.parse_item()?;
                return Ok(Block {
                    span: Span::new(
                        start_span.start,
                        self.previous.span.end,
                        start_span.line,
                        start_span.column,
                    ),
                    statements: vec![stmt],
                });
            }

            // Empty body: `case nil:` followed by dedent or another case
            if self.check(&TokenKind::Dedent) || self.check(&TokenKind::Eof) {
                let span = self.current.span;
                return Ok(Block {
                    span,
                    statements: vec![],
                });
            }

            // Fall through to expect Indent (will produce error)
        }

        self.expect(&TokenKind::Indent)?;

        // Handle empty block: Indent immediately followed by Dedent
        if self.check(&TokenKind::Dedent) {
            let span = self.current.span;
            self.advance(); // consume Dedent
            return Ok(Block {
                span,
                statements: vec![],
            });
        }

        self.parse_block_body()
    }

    /// Check if the current token can start a statement.
    /// Used to detect "flat body" patterns (body at same indentation after colon).
    fn is_statement_start(&self) -> bool {
        matches!(
            self.current.kind,
            TokenKind::Return
                | TokenKind::Break
                | TokenKind::Continue
                | TokenKind::If
                | TokenKind::For
                | TokenKind::While
                | TokenKind::Match
                | TokenKind::Loop
                | TokenKind::Pass
                | TokenKind::Val
                | TokenKind::Var
                | TokenKind::Fn
                | TokenKind::Me
                | TokenKind::Defer
                | TokenKind::Assert
                | TokenKind::Assume
                | TokenKind::Use
                | TokenKind::Import
                | TokenKind::Export
                | TokenKind::Identifier { .. }
        )
    }

    /// Parse block body (assumes INDENT has already been consumed).
    /// Used when we need to manually handle what comes before the block body.
    pub(crate) fn parse_block_body(&mut self) -> Result<Block, ParseError> {
        self.debug_enter("parse_block_body");
        let start_span = self.current.span;

        let mut statements = Vec::new();
        let mut iterations = 0usize;

        while !self.check(&TokenKind::Dedent) && !self.is_at_end() {
            self.check_loop_limit(iterations, "parse_block_body")?;
            iterations += 1;

            // Skip empty lines
            while self.check(&TokenKind::Newline) {
                self.advance();
            }
            if self.check(&TokenKind::Dedent) || self.is_at_end() {
                break;
            }

            statements.push(self.parse_item()?);

            // Consume newline after statement if present
            if self.check(&TokenKind::Newline) {
                self.advance();
            }
        }

        if self.check(&TokenKind::Dedent) {
            self.advance();
        }

        self.debug_exit("parse_block_body");
        Ok(Block {
            span: Span::new(
                start_span.start,
                self.previous.span.end,
                start_span.line,
                start_span.column,
            ),
            statements,
        })
    }

    pub(crate) fn parse_parameters(&mut self) -> Result<Vec<Parameter>, ParseError> {
        self.expect(&TokenKind::LParen)?;

        let mut params = Vec::new();

        // Skip newlines after opening paren (allow multi-line parameter lists)
        self.skip_newlines();

        while !self.check(&TokenKind::RParen) {
            let param_span = self.current.span;

            // Check for @inject attribute on parameter (#1013)
            let inject = if self.check(&TokenKind::At) {
                self.advance();
                let attr_name = self.expect_identifier()?;
                if attr_name != "inject" {
                    return Err(ParseError::unexpected_token("inject", attr_name, self.current.span));
                }
                true
            } else {
                false
            };

            let mutability = if self.check(&TokenKind::Mut) {
                self.advance();
                Mutability::Mutable
            } else {
                Mutability::Immutable
            };

            // Allow 'self' as a parameter name for method definitions
            let name = if self.check(&TokenKind::Self_) {
                self.advance();
                "self".to_string()
            } else {
                self.expect_identifier()?
            };

            let ty = if self.check(&TokenKind::Colon) {
                self.advance();
                Some(self.parse_type()?)
            } else {
                None
            };

            // Check for variadic parameter (e.g., items: T...)
            let variadic = if self.check(&TokenKind::Ellipsis) {
                self.advance();
                true
            } else {
                false
            };

            let default = if self.check(&TokenKind::Assign) {
                self.advance();
                Some(self.parse_expression()?)
            } else {
                None
            };

            // Check for call-site label keyword after type (e.g., `from: text to`)
            let call_site_label = if self.check(&TokenKind::To) {
                self.advance();
                Some("to".to_string())
            } else if self.check(&TokenKind::From) {
                self.advance();
                Some("from".to_string())
            } else if self.check(&TokenKind::By) {
                self.advance();
                Some("by".to_string())
            } else if self.check(&TokenKind::Into) {
                self.advance();
                Some("into".to_string())
            } else if self.check(&TokenKind::Onto) {
                self.advance();
                Some("onto".to_string())
            } else if self.check(&TokenKind::With) {
                self.advance();
                Some("with".to_string())
            } else {
                None
            };

            params.push(Parameter {
                span: param_span,
                name,
                ty,
                default,
                mutability,
                inject,
                variadic,
                call_site_label,
            });

            // Handle comma or newline between parameters
            if !self.check(&TokenKind::RParen) {
                if self.check(&TokenKind::Comma) {
                    self.advance();
                    // Skip newlines after comma (allow multi-line parameter lists)
                    self.skip_newlines();
                } else if self.check(&TokenKind::Newline) {
                    // Allow newline without comma in multi-line parameter lists
                    self.skip_newlines();
                } else {
                    return Err(ParseError::unexpected_token(
                        "comma or newline",
                        format!("{:?}", self.current.kind),
                        self.current.span,
                    ));
                }
            }
        }

        self.expect(&TokenKind::RParen)?;
        Ok(params)
    }

    /// Parse parenthesized type list: `(Type1, Type2, ...)`
    pub(crate) fn parse_paren_type_list(&mut self) -> Result<Vec<Type>, ParseError> {
        self.expect(&TokenKind::LParen)?;
        let mut types = Vec::new();
        while !self.check(&TokenKind::RParen) {
            types.push(self.parse_type()?);
            if !self.check(&TokenKind::RParen) {
                self.expect(&TokenKind::Comma)?;
            }
        }
        self.expect(&TokenKind::RParen)?;
        Ok(types)
    }

    /// Parse a metadata/config block: `arch { key = value ... }`
    /// This consumes the identifier, opening brace, all contents (balancing nested braces),
    /// and the closing brace. Returns a Pass node since metadata blocks don't affect AST.
    pub(crate) fn parse_metadata_block(&mut self) -> Result<Node, ParseError> {
        let start_span = self.current.span;
        self.advance(); // consume the identifier (arch, config, etc.)

        // Skip newlines before the opening brace
        while self.check(&TokenKind::Newline) {
            self.advance();
        }

        self.expect(&TokenKind::LBrace)?;

        // Consume everything until we find the matching closing brace
        let mut depth = 1u32;
        while depth > 0 && !self.is_at_end() {
            match &self.current.kind {
                TokenKind::LBrace => {
                    depth += 1;
                    self.advance();
                }
                TokenKind::RBrace => {
                    depth -= 1;
                    if depth > 0 {
                        self.advance();
                    }
                }
                _ => {
                    self.advance();
                }
            }
        }

        if self.check(&TokenKind::RBrace) {
            self.advance(); // consume final }
        }

        Ok(Node::Pass(PassStmt { span: start_span }))
    }
}
