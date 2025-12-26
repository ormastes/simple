//! .sui (Simple UI) file parser
//!
//! Parses .sui files which contain a mix of server code, client code, and templates.
//!
//! # File Format
//!
//! ```sui
//! {$ let users: List[User] $}  # Shared state declaration
//!
//! {- server -}
//! # Server-side code block (compiled to native/JIT)
//! users = db.query("SELECT * FROM users")
//!
//! {+ client +}
//! # Client-side code block (compiled to WASM)
//! import dom, fetch
//! fn on_refresh():
//!     users = await fetch.get_json("/api/users")
//!     invalidate()
//!
//! {@ render @}
//! # Template block (HTML with template syntax)
//! <ul>
//!   {% for u in users: %}
//!     <li>{{ u.name }}</li>
//!   {% end %}
//! </ul>
//! ```
//!
//! # Block Types
//!
//! - `{$ ... $}` - Shared state declarations (accessible from both server and client)
//! - `{- ... -}` - Server-side code block (runs during SSR)
//! - `{+ ... +}` - Client-side code block (compiled to WASM, runs in browser)
//! - `{@ ... @}` - Template/render block (HTML with template syntax)

use crate::ast::Node;
use crate::error::ParseError;
use crate::parser_impl::Parser;

/// A parsed .sui file containing server code, client code, and templates
#[derive(Debug, Clone)]
pub struct SuiFile {
    /// Shared state declarations (accessible from server and client)
    pub shared_state: Vec<SharedStateDecl>,
    /// Server-side code blocks
    pub server_blocks: Vec<ServerBlock>,
    /// Client-side code blocks (compiled to WASM)
    pub client_blocks: Vec<ClientBlock>,
    /// Template/render blocks
    pub template_blocks: Vec<TemplateBlock>,
}

/// Shared state declaration: `{$ let users: List[User] $}`
#[derive(Debug, Clone)]
pub struct SharedStateDecl {
    pub name: String,
    pub type_annotation: Option<String>,
    pub initializer: Option<String>,
}

/// Server-side code block: `{- server -} ... code ...`
#[derive(Debug, Clone)]
pub struct ServerBlock {
    pub label: Option<String>,
    pub code: String,
    /// Parsed AST of the server code
    pub ast: Vec<Node>,
}

/// Client-side code block: `{+ client +} ... code ...`
#[derive(Debug, Clone)]
pub struct ClientBlock {
    pub label: Option<String>,
    pub code: String,
    /// Parsed AST of the client code
    pub ast: Vec<Node>,
    /// Event handlers exported for hydration
    pub exports: Vec<String>,
}

/// Template/render block: `{@ render @} ... HTML ...`
#[derive(Debug, Clone)]
pub struct TemplateBlock {
    pub label: Option<String>,
    pub template: String,
    /// Parsed template variables for hydration
    pub variables: Vec<String>,
}

/// .sui file parser
pub struct SuiParser {
    source: String,
    position: usize,
}

impl SuiParser {
    /// Create a new .sui parser
    pub fn new(source: String) -> Self {
        Self {
            source,
            position: 0,
        }
    }

    /// Parse a .sui file
    pub fn parse(&mut self) -> Result<SuiFile, ParseError> {
        let mut shared_state = Vec::new();
        let mut server_blocks = Vec::new();
        let mut client_blocks = Vec::new();
        let mut template_blocks = Vec::new();

        while !self.is_at_end() {
            self.skip_whitespace();

            if self.is_at_end() {
                break;
            }

            // Try to parse a block
            if self.peek_str(2) == "{$" {
                shared_state.push(self.parse_shared_state()?);
            } else if self.peek_str(2) == "{-" {
                server_blocks.push(self.parse_server_block()?);
            } else if self.peek_str(2) == "{+" {
                client_blocks.push(self.parse_client_block()?);
            } else if self.peek_str(2) == "{@" {
                template_blocks.push(self.parse_template_block()?);
            } else {
                // Skip unknown content (comments, whitespace)
                self.skip_until_block_start();
            }
        }

        Ok(SuiFile {
            shared_state,
            server_blocks,
            client_blocks,
            template_blocks,
        })
    }

    /// Parse shared state declaration: `{$ let users: List[User] $}`
    fn parse_shared_state(&mut self) -> Result<SharedStateDecl, ParseError> {
        self.expect_str("{$")?;
        self.skip_whitespace();

        // Extract content until closing $}
        let content = self.extract_until("$}")?;
        self.expect_str("$}")?;

        // Simple parsing: "let name: Type = value"
        let trimmed = content.trim();

        // For now, just store the raw declaration
        // TODO: Parse into proper AST
        Ok(SharedStateDecl {
            name: trimmed.to_string(),
            type_annotation: None,
            initializer: None,
        })
    }

    /// Parse server block: `{- server -} ... code ...`
    fn parse_server_block(&mut self) -> Result<ServerBlock, ParseError> {
        self.expect_str("{-")?;
        self.skip_whitespace();

        // Extract label (optional)
        let label = if self.peek_str(2) == "-}" {
            None
        } else {
            Some(self.extract_until("-}")?.trim().to_string())
        };

        self.expect_str("-}")?;
        self.skip_whitespace();

        // Extract code until next block or EOF
        let code = self.extract_code_until_block()?;

        // Parse the code as Simple code
        let ast = self.parse_simple_code(&code)?;

        Ok(ServerBlock {
            label,
            code,
            ast,
        })
    }

    /// Parse client block: `{+ client +} ... code ...`
    fn parse_client_block(&mut self) -> Result<ClientBlock, ParseError> {
        self.expect_str("{+")?;
        self.skip_whitespace();

        // Extract label (optional)
        let label = if self.peek_str(2) == "+}" {
            None
        } else {
            Some(self.extract_until("+}")?.trim().to_string())
        };

        self.expect_str("+}")?;
        self.skip_whitespace();

        // Extract code until next block or EOF
        let code = self.extract_code_until_block()?;

        // Parse the code as Simple code
        let ast = self.parse_simple_code(&code)?;

        // Extract exported functions for hydration
        let exports = self.extract_exports(&ast);

        Ok(ClientBlock {
            label,
            code,
            ast,
            exports,
        })
    }

    /// Parse template block: `{@ render @} ... HTML ...`
    fn parse_template_block(&mut self) -> Result<TemplateBlock, ParseError> {
        self.expect_str("{@")?;
        self.skip_whitespace();

        // Extract label (optional)
        let label = if self.peek_str(2) == "@}" {
            None
        } else {
            Some(self.extract_until("@}")?.trim().to_string())
        };

        self.expect_str("@}")?;
        self.skip_whitespace();

        // Extract template until next block or EOF
        let template = self.extract_code_until_block()?;

        // Extract template variables ({{ var }}, {% for var %}, etc.)
        let variables = self.extract_template_variables(&template);

        Ok(TemplateBlock {
            label,
            template,
            variables,
        })
    }

    /// Parse Simple code using the main parser
    fn parse_simple_code(&self, code: &str) -> Result<Vec<Node>, ParseError> {
        let mut parser = Parser::new(code);

        // Parse as a module
        let module = parser.parse()?;

        Ok(module.items)
    }

    /// Extract exported function names from AST
    fn extract_exports(&self, ast: &[Node]) -> Vec<String> {
        let mut exports = Vec::new();

        for node in ast {
            if let Node::Function(func_def) = node {
                exports.push(func_def.name.clone());
            }
        }

        exports
    }

    /// Extract template variables from template string
    fn extract_template_variables(&self, template: &str) -> Vec<String> {
        let mut variables = Vec::new();
        let mut chars = template.chars().peekable();

        while let Some(ch) = chars.next() {
            if ch == '{' {
                if let Some(&next) = chars.peek() {
                    if next == '{' {
                        // {{ variable }}
                        chars.next(); // consume second {
                        let var_name = self.extract_until_in_iter(&mut chars, "}}");
                        variables.push(var_name.trim().to_string());
                    } else if next == '%' {
                        // {% for var in ... %}
                        chars.next(); // consume %
                        let content = self.extract_until_in_iter(&mut chars, "%}");
                        if content.trim().starts_with("for ") {
                            // Extract variable name from "for var in ..."
                            let parts: Vec<&str> = content.trim().splitn(4, ' ').collect();
                            if parts.len() >= 2 {
                                variables.push(parts[1].to_string());
                            }
                        }
                    }
                }
            }
        }

        variables
    }

    /// Helper: extract content until pattern from iterator
    fn extract_until_in_iter(&self, chars: &mut std::iter::Peekable<std::str::Chars>, pattern: &str) -> String {
        let mut result = String::new();
        let pattern_chars: Vec<char> = pattern.chars().collect();
        let mut match_pos = 0;

        while let Some(ch) = chars.next() {
            if ch == pattern_chars[match_pos] {
                match_pos += 1;
                if match_pos == pattern_chars.len() {
                    break;
                }
            } else {
                // Add any partially matched pattern chars
                for i in 0..match_pos {
                    result.push(pattern_chars[i]);
                }
                match_pos = 0;
                result.push(ch);
            }
        }

        result
    }

    // === Helper methods ===

    fn is_at_end(&self) -> bool {
        self.position >= self.source.len()
    }

    fn peek(&self) -> char {
        if self.is_at_end() {
            '\0'
        } else {
            self.source.chars().nth(self.position).unwrap_or('\0')
        }
    }

    fn peek_str(&self, len: usize) -> String {
        self.source
            .chars()
            .skip(self.position)
            .take(len)
            .collect()
    }

    fn advance(&mut self) -> char {
        if self.is_at_end() {
            '\0'
        } else {
            let ch = self.peek();
            self.position += ch.len_utf8();
            ch
        }
    }

    fn skip_whitespace(&mut self) {
        while !self.is_at_end() {
            let ch = self.peek();
            if ch.is_whitespace() {
                self.advance();
            } else if ch == '#' {
                // Skip comment until newline
                while !self.is_at_end() && self.peek() != '\n' {
                    self.advance();
                }
            } else {
                break;
            }
        }
    }

    fn skip_until_block_start(&mut self) {
        while !self.is_at_end() {
            let two_char = self.peek_str(2);
            if two_char == "{$" || two_char == "{-" || two_char == "{+" || two_char == "{@" {
                break;
            }
            self.advance();
        }
    }

    fn expect_str(&mut self, expected: &str) -> Result<(), ParseError> {
        let actual = self.peek_str(expected.len());
        if actual == expected {
            for _ in 0..expected.len() {
                self.advance();
            }
            Ok(())
        } else {
            Err(ParseError::syntax_error(
                format!("Expected '{}', found '{}'", expected, actual),
                0,
                0,
            ))
        }
    }

    fn extract_until(&mut self, pattern: &str) -> Result<String, ParseError> {
        let mut result = String::new();
        let pattern_chars: Vec<char> = pattern.chars().collect();

        while !self.is_at_end() {
            // Check if we're at the start of the pattern
            let mut is_match = true;
            for (i, &expected) in pattern_chars.iter().enumerate() {
                if self.peek_ahead(i) != expected {
                    is_match = false;
                    break;
                }
            }

            if is_match {
                // Found the pattern - return without consuming it
                return Ok(result);
            }

            // Not at pattern, consume current character
            result.push(self.advance());
        }

        Err(ParseError::syntax_error(
            format!("Unexpected end of file, expected '{}'", pattern),
            0,
            0,
        ))
    }

    fn peek_ahead(&self, char_offset: usize) -> char {
        self.source[self.position..]
            .chars()
            .nth(char_offset)
            .unwrap_or('\0')
    }

    fn extract_code_until_block(&mut self) -> Result<String, ParseError> {
        let mut result = String::new();

        while !self.is_at_end() {
            let two_char = self.peek_str(2);
            if two_char == "{$" || two_char == "{-" || two_char == "{+" || two_char == "{@" {
                break;
            }
            result.push(self.advance());
        }

        Ok(result.trim().to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_simple_sui_file() {
        let source = r#"
{$ let count: i32 = 0 $}

{- server -}
count = 42

{+ client +}
fn increment():
    count += 1

{@ render @}
<div>Count: {{ count }}</div>
"#;

        let mut parser = SuiParser::new(source.to_string());
        let result = parser.parse().unwrap();

        assert_eq!(result.shared_state.len(), 1);
        assert_eq!(result.server_blocks.len(), 1);
        assert_eq!(result.client_blocks.len(), 1);
        assert_eq!(result.template_blocks.len(), 1);
    }

    #[test]
    fn test_parse_server_block() {
        let source = r#"
{- server -}
users = db.query("SELECT * FROM users")
"#;

        let mut parser = SuiParser::new(source.to_string());
        let result = parser.parse().unwrap();

        assert_eq!(result.server_blocks.len(), 1);
        assert!(result.server_blocks[0].code.contains("db.query"));
    }

    #[test]
    fn test_parse_client_block() {
        let source = r#"
{+ client +}
import dom

fn on_click():
    alert("clicked!")
"#;

        let mut parser = SuiParser::new(source.to_string());
        let result = parser.parse().unwrap();

        assert_eq!(result.client_blocks.len(), 1);
        assert!(result.client_blocks[0].exports.len() > 0);
        assert_eq!(result.client_blocks[0].exports[0], "on_click");
    }

    #[test]
    fn test_parse_template_variables() {
        let source = r#"
{@ render @}
<ul>
  {% for user in users: %}
    <li>{{ user.name }}</li>
  {% end %}
</ul>
"#;

        let mut parser = SuiParser::new(source.to_string());
        let result = parser.parse().unwrap();

        assert_eq!(result.template_blocks.len(), 1);
        assert!(result.template_blocks[0].variables.contains(&"user".to_string()));
    }

    #[test]
    fn test_parse_multiple_blocks() {
        let source = r#"
{- init -}
let data = load_data()

{+ client +}
fn refresh():
    reload()

{@ header @}
<header>{{ title }}</header>

{- process -}
process_data()

{@ body @}
<main>{{ content }}</main>
"#;

        let mut parser = SuiParser::new(source.to_string());
        let result = parser.parse().unwrap();

        assert_eq!(result.server_blocks.len(), 2);
        assert_eq!(result.client_blocks.len(), 1);
        assert_eq!(result.template_blocks.len(), 2);
    }
}
