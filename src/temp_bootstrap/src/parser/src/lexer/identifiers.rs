use crate::token::TokenKind;

impl<'a> super::Lexer<'a> {
    pub(super) fn scan_identifier(&mut self, first: char) -> TokenKind {
        // Check for f-string: f"..."
        if first == 'f' && self.check('"') {
            self.advance(); // consume the opening "
            return self.scan_fstring();
        }

        // Check for byte literal: b'x'
        if first == 'b' && self.check('\'') {
            self.advance(); // consume the opening '
            let byte_val = if self.check('\\') {
                self.advance(); // consume backslash
                match self.peek() {
                    Some('n') => { self.advance(); b'\n' }
                    Some('r') => { self.advance(); b'\r' }
                    Some('t') => { self.advance(); b'\t' }
                    Some('0') => { self.advance(); b'\0' }
                    Some('\\') => { self.advance(); b'\\' }
                    Some('\'') => { self.advance(); b'\'' }
                    Some(c) => { self.advance(); c as u8 }
                    None => b'\\'
                }
            } else if let Some(c) = self.peek() {
                self.advance();
                c as u8
            } else {
                0
            };
            // Consume closing '
            if self.check('\'') {
                self.advance();
            }
            return TokenKind::Integer(byte_val as i64);
        }

        // Check for raw string: r"..." or r"""..."""
        if first == 'r' && self.check('"') {
            self.advance(); // consume the first "
            // Check for triple-quoted raw string: r"""..."""
            if self.check('"') {
                // Could be r"" (empty raw string) or r"""...""" (triple-quoted)
                self.advance(); // consume the second "
                if self.check('"') {
                    // r""" - triple-quoted raw string
                    self.advance(); // consume the third "
                    return self.scan_triple_single_quoted_string_like();
                } else {
                    // r"" - empty raw string
                    return TokenKind::RawString(String::new());
                }
            }
            return self.scan_raw_double_string();
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

        // Check for keywords
        match name.as_str() {
            "fn" | "def" => TokenKind::Fn,
            "let" | "val" => TokenKind::Let,
            "var" => TokenKind::Var,
            "mut" => TokenKind::Mut,
            "me" => TokenKind::Me,
            "if" => TokenKind::If,
            "elif" => TokenKind::Elif,
            "else" => TokenKind::Else,
            "for" => TokenKind::For,
            "while" => TokenKind::While,
            "loop" => TokenKind::Loop,
            "break" => TokenKind::Break,
            "continue" => TokenKind::Continue,
            "return" => TokenKind::Return,
            "match" => TokenKind::Match,
            "case" => TokenKind::Case,
            "struct" => TokenKind::Struct,
            "class" => TokenKind::Class,
            "enum" => TokenKind::Enum,
            "union" => TokenKind::Union,
            "trait" => TokenKind::Trait,
            "mixin" => TokenKind::Mixin,
            "impl" => TokenKind::Impl,
            "actor" => TokenKind::Actor,
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
            "or" => TokenKind::Or,
            "true" => TokenKind::Bool(true),
            "false" => TokenKind::Bool(false),
            "nil" => TokenKind::Nil,
            "spawn" => TokenKind::Spawn,
            "new" => TokenKind::New,
            "self" => TokenKind::Self_,
            "super" => TokenKind::Super,
            "async" => TokenKind::Async,
            "await" => TokenKind::Await,
            "yield" => TokenKind::Yield,
            "move" => TokenKind::Move,
            "const" => TokenKind::Const,
            "static" => TokenKind::Static,
            "type" => TokenKind::Type,
            "unit" => TokenKind::Unit,
            "extern" => TokenKind::Extern,
            "context" => TokenKind::Context,
            "with" => TokenKind::With,
            "macro" => TokenKind::Macro,
            "vec" => TokenKind::Vec,
            "shared" => TokenKind::Shared,
            "gpu" => TokenKind::Gpu,
            "dyn" => TokenKind::Dyn,
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
            // Infix keywords (for BDD spec framework)
            "to" => TokenKind::To,
            "not_to" => TokenKind::NotTo,
            "pass_do_nothing" => TokenKind::PassDoNothing,
            "pass_dn" => TokenKind::PassDn,
            "pass_todo" => TokenKind::PassTodo,
            "pass" => TokenKind::Pass,
            "bitfield" => TokenKind::Bitfield,
            "alias" => TokenKind::Alias,
            "_" => TokenKind::Underscore,
            _ => TokenKind::Identifier(name),
        }
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
