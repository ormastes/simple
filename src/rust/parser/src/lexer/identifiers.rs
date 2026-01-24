use crate::token::{NamePattern, TokenKind};

impl<'a> super::Lexer<'a> {
    pub(super) fn scan_identifier(&mut self, first: char) -> TokenKind {
        // Check for f-string: f"..." or f"""..."""
        if first == 'f' && self.check('"') {
            self.advance(); // consume the opening "
                            // Check for triple-quoted f-string: f"""..."""
            if self.check('"') && self.check_ahead(1, '"') {
                return self.scan_triple_fstring();
            }
            return self.scan_fstring();
        }

        // Check for raw string: r"..." or r"""..."""
        if first == 'r' && self.check('"') {
            self.advance(); // consume the first "
                            // Check for triple-quoted raw string: r"""..."""
            if self.check('"') && self.check_ahead(1, '"') {
                return self.scan_triple_quoted_string();
            }
            // Single raw string: r"..."
            return self.scan_raw_double_string();
        }

        // Check for pc{...} pointcut syntax
        if first == 'p' && self.peek() == Some('c') {
            // Peek ahead to see if this is followed by {
            if self.peek_ahead(1) == Some('{') {
                self.advance(); // consume 'c'
                self.advance(); // consume '{'
                return self.scan_pointcut();
            }
        }

        // Check for custom block syntax: kind{payload}
        // Supported kinds: m, sh, sql, re, md, html, graph, img
        if let Some(block_kind) = self.try_scan_custom_block(first) {
            return block_kind;
        }

        let mut name = String::from(first);

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        // Check for i18n pattern: Name_"..." (identifier ending with _ followed by ")
        // The identifier must end with _ and be immediately followed by "
        if name.ends_with('_') && self.check('"') {
            self.advance(); // consume opening "
                            // Check for triple-quoted i18n string: Name_"""..."""
            if self.check('"') && self.check_ahead(1, '"') {
                return self.scan_i18n_triple_string(name);
            }
            return self.scan_i18n_string(name);
        }

        // Check for suspension keywords with tilde suffix (if~, while~, for~, and~, or~)
        // These must be checked before regular keyword matching
        if self.check('~') {
            match name.as_str() {
                "if" => {
                    self.advance(); // consume '~'
                    return TokenKind::IfSuspend;
                }
                "while" => {
                    self.advance(); // consume '~'
                    return TokenKind::WhileSuspend;
                }
                "for" => {
                    self.advance(); // consume '~'
                    return TokenKind::ForSuspend;
                }
                "and" => {
                    self.advance(); // consume '~'
                    return TokenKind::AndSuspend;
                }
                "or" => {
                    self.advance(); // consume '~'
                    return TokenKind::OrSuspend;
                }
                _ => {} // Not a suspension keyword, continue to regular keyword matching
            }
        }

        // Check for keywords
        match name.as_str() {
            "fn" => TokenKind::Fn,
            "me" => TokenKind::Me,
            "let" => TokenKind::Let, // Legacy
            "mut" => TokenKind::Mut, // Legacy
            "val" => TokenKind::Val,
            "var" => TokenKind::Var,
            "if" => TokenKind::If,
            "elif" => TokenKind::Elif,
            "else" => TokenKind::Else,
            "for" => TokenKind::For,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "pass" => TokenKind::Pass,
            "return" => TokenKind::Return,
            "match" => TokenKind::Match,
            "case" => TokenKind::Case,
            "struct" => TokenKind::Struct,
            "class" => TokenKind::Class,
            "enum" => TokenKind::Enum,
            "union" => TokenKind::Union,
            "trait" => TokenKind::Trait,
            "impl" => TokenKind::Impl,
            "mixin" => TokenKind::Mixin,
            "actor" => TokenKind::Actor,
            "extends" => TokenKind::Extends,
            "pub" => TokenKind::Pub,
            "priv" => TokenKind::Priv,
            "import" => TokenKind::Import,
            "from" => TokenKind::From,
            "as" => TokenKind::As,
            "mod" => TokenKind::Mod,
            "use" => TokenKind::Use,
            "export" => TokenKind::Export,
            "common" => TokenKind::Common,
            "auto" => TokenKind::Auto,
            "crate" => TokenKind::Crate,
            "in" => TokenKind::In,
            "is" => TokenKind::Is,
            "not" => TokenKind::Not,
            "and" => TokenKind::And,
            "or" => {
                // Check for "or:" combined token (used in unwrap fallback)
                if self.check(':') {
                    self.advance(); // consume ':'
                    TokenKind::OrColon
                } else {
                    TokenKind::Or
                }
            }
            "or_return" => {
                // Check for "or_return:" combined token (unwrap or early return)
                if self.check(':') {
                    self.advance(); // consume ':'
                    TokenKind::OrReturn
                } else {
                    // Not followed by colon - treat as identifier
                    let pattern = NamePattern::detect("or_return");
                    TokenKind::Identifier {
                        name: "or_return".to_string(),
                        pattern,
                    }
                }
            }
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            "nil" => TokenKind::Nil,
            "spawn" => TokenKind::Spawn,
            "go" => TokenKind::Go,
            "new" => TokenKind::New,
            "self" => TokenKind::Self_,
            "super" => TokenKind::Super,
            "async" => TokenKind::Async,
            "await" => TokenKind::Await,
            "sync" => TokenKind::Sync,
            "yield" => TokenKind::Yield,
            "move" => TokenKind::Move,
            "const" => TokenKind::Const,
            "static" => TokenKind::Static,
            "type" => TokenKind::Type,
            "unit" => TokenKind::Unit,
            "extern" => TokenKind::Extern,
            "context" => TokenKind::Context,
            "with" => TokenKind::With,
            "ghost" => TokenKind::Ghost,
            "macro" => TokenKind::Macro,
            "vec" => TokenKind::Vec,
            "shared" => TokenKind::Shared,
            "gpu" => TokenKind::Gpu,
            "bounds" => TokenKind::Bounds,
            "dyn" => TokenKind::Dyn,
            "repr" => TokenKind::Repr,
            "literal" => TokenKind::Literal,
            "alias" => TokenKind::Alias,
            // Note: "lean" is NOT a keyword - it's parsed contextually to avoid breaking
            // existing module paths like "verification.lean.codegen"
            // Note: "allow" is NOT a keyword - it's parsed contextually in unit definitions
            // to avoid conflicts with #[allow(...)] attributes
            // Contract keywords (new spec)
            "out" => TokenKind::Out,
            "out_err" => TokenKind::OutErr,
            "where" => TokenKind::Where,
            // Contract keywords (legacy)
            "requires" => TokenKind::Requires,
            "ensures" => TokenKind::Ensures,
            // Contract keywords (shared)
            "invariant" => TokenKind::Invariant,
            "old" => TokenKind::Old,
            "result" => TokenKind::Result,
            "decreases" => TokenKind::Decreases,
            "forall" => TokenKind::Forall,
            "exists" => TokenKind::Exists,
            // Inline assertion keyword
            // Note: assert!/check! are macro calls, and assert()/check() are function calls
            // If '!' or '(' follows, treat as identifier (for macro/function calls)
            // Note: We don't make "check" a keyword to avoid conflicts with common variable names
            "assert" if self.peek() != Some('!') && self.peek() != Some('(') => TokenKind::Assert,
            "assume" if self.peek() != Some('!') && self.peek() != Some('(') => TokenKind::Assume,
            "admit" if self.peek() != Some('!') && self.peek() != Some('(') => TokenKind::Admit,
            // Note: "calc" is NOT a keyword - it's parsed contextually to avoid breaking
            // existing variable names like "calc" or "calculator"
            // Infix keywords (for BDD spec framework)
            "to" => TokenKind::To,
            "not_to" => TokenKind::NotTo,
            // Gherkin-style system test DSL keywords
            "feature" => TokenKind::Feature,
            "scenario" => TokenKind::Scenario,
            "outline" => TokenKind::Outline,
            "examples" => TokenKind::Examples,
            "given" => TokenKind::Given,
            "when" => TokenKind::When,
            "then" => TokenKind::Then,
            "and_then" => TokenKind::AndThen,
            // Memory management keywords
            "handle_pool" => TokenKind::HandlePool,
            // Simple Math keywords (#1910-#1969)
            "grid" => TokenKind::Grid,
            "tensor" => TokenKind::Tensor,
            "slice" => TokenKind::Slice,
            "flat" => TokenKind::Flat,
            "default" => TokenKind::Default,
            "_" => TokenKind::Underscore,
            // AOP keywords
            "on" => TokenKind::On,
            "bind" => TokenKind::Bind,
            "forbid" => TokenKind::Forbid,
            "allow" => TokenKind::Allow,
            "mock" => TokenKind::Mock,
            // Safe unwrap operator keyword
            "unwrap" => TokenKind::Unwrap,
            _ => {
                let pattern = NamePattern::detect(&name);
                TokenKind::Identifier { name, pattern }
            }
        }
    }

    /// Scan a pointcut predicate expression: pc{...}
    /// Returns the content between { and } as a Pointcut token
    pub(super) fn scan_pointcut(&mut self) -> TokenKind {
        let mut content = String::new();
        let mut depth = 1; // We've already consumed the opening {

        while let Some(ch) = self.peek() {
            if ch == '{' {
                depth += 1;
                content.push(ch);
                self.advance();
            } else if ch == '}' {
                depth -= 1;
                if depth == 0 {
                    self.advance(); // consume the closing }
                    return TokenKind::Pointcut(content);
                } else {
                    content.push(ch);
                    self.advance();
                }
            } else {
                content.push(ch);
                self.advance();
            }
        }

        // Unclosed pointcut - return error
        TokenKind::Error("Unclosed pointcut expression (missing '}')".to_string())
    }

    /// Try to scan a custom block: kind{payload}
    /// Returns Some(TokenKind) if a valid custom block is found, None otherwise.
    /// Supported kinds: m, sh, sql, re, md, html, graph, img
    pub(super) fn try_scan_custom_block(&mut self, first: char) -> Option<TokenKind> {
        // Check single-character block kinds: m{...}
        if first == 'm' && self.peek() == Some('{') {
            self.advance(); // consume '{'
            return Some(self.scan_custom_block_payload("m"));
        }

        // Check two-character block kinds: sh{...}, re{...}, md{...}
        match first {
            's' => {
                if self.peek() == Some('h') && self.peek_ahead(1) == Some('{') {
                    self.advance(); // consume 'h'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("sh"));
                }
                if self.peek() == Some('q') && self.peek_ahead(1) == Some('l') && self.peek_ahead(2) == Some('{') {
                    self.advance(); // consume 'q'
                    self.advance(); // consume 'l'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("sql"));
                }
            }
            'r' => {
                if self.peek() == Some('e') && self.peek_ahead(1) == Some('{') {
                    self.advance(); // consume 'e'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("re"));
                }
            }
            'm' => {
                if self.peek() == Some('d') && self.peek_ahead(1) == Some('{') {
                    self.advance(); // consume 'd'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("md"));
                }
            }
            'h' => {
                if self.peek() == Some('t')
                    && self.peek_ahead(1) == Some('m')
                    && self.peek_ahead(2) == Some('l')
                    && self.peek_ahead(3) == Some('{')
                {
                    self.advance(); // consume 't'
                    self.advance(); // consume 'm'
                    self.advance(); // consume 'l'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("html"));
                }
            }
            'g' => {
                if self.peek() == Some('r')
                    && self.peek_ahead(1) == Some('a')
                    && self.peek_ahead(2) == Some('p')
                    && self.peek_ahead(3) == Some('h')
                    && self.peek_ahead(4) == Some('{')
                {
                    self.advance(); // consume 'r'
                    self.advance(); // consume 'a'
                    self.advance(); // consume 'p'
                    self.advance(); // consume 'h'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("graph"));
                }
            }
            'i' => {
                if self.peek() == Some('m') && self.peek_ahead(1) == Some('g') && self.peek_ahead(2) == Some('{') {
                    self.advance(); // consume 'm'
                    self.advance(); // consume 'g'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("img"));
                }
            }
            'l' => {
                // Check for lean{...} custom block
                if self.peek() == Some('e')
                    && self.peek_ahead(1) == Some('a')
                    && self.peek_ahead(2) == Some('n')
                    && self.peek_ahead(3) == Some('{')
                {
                    self.advance(); // consume 'e'
                    self.advance(); // consume 'a'
                    self.advance(); // consume 'n'
                    self.advance(); // consume '{'
                    return Some(self.scan_custom_block_payload("lean"));
                }
            }
            _ => {}
        }

        None
    }

    /// Scan the payload of a custom block (everything between { and matching })
    /// Handles nested braces correctly.
    pub(super) fn scan_custom_block_payload(&mut self, kind: &str) -> TokenKind {
        let mut payload = String::new();
        let mut depth = 1; // We've already consumed the opening {

        while let Some(ch) = self.peek() {
            if ch == '{' {
                depth += 1;
                payload.push(ch);
                self.advance();
            } else if ch == '}' {
                depth -= 1;
                if depth == 0 {
                    self.advance(); // consume the closing }
                    return TokenKind::CustomBlock {
                        kind: kind.to_string(),
                        payload,
                    };
                } else {
                    payload.push(ch);
                    self.advance();
                }
            } else {
                payload.push(ch);
                self.advance();
            }
        }

        // Unclosed block - return error
        TokenKind::Error(format!("Unclosed {} block (missing '}}')", kind))
    }

    pub(super) fn scan_symbol(&mut self) -> TokenKind {
        let mut name = String::new();

        while let Some(ch) = self.peek() {
            if ch.is_alphanumeric() || ch == '_' {
                name.push(ch);
                self.advance();
            } else {
                break;
            }
        }

        if name.is_empty() {
            TokenKind::Colon
        } else {
            TokenKind::Symbol(name)
        }
    }
}
