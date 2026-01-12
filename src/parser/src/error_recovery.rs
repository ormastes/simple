//! Error Recovery and Helpful Diagnostics
//!
//! This module provides:
//! - Detection of common mistakes from other languages
//! - "Did you mean?" suggestions
//! - Warnings for verbose/unnecessary syntax
//! - Helpful error messages for newcomers

use crate::error::ParseError;
use crate::token::{Span, Token, TokenKind};

/// Common programming mistakes from other languages
#[derive(Debug, Clone, PartialEq)]
pub enum CommonMistake {
    // Python-style
    PythonDef,              // def instead of fn
    PythonSelf,             // self. instead of implicit self
    PythonNone,             // None instead of nil
    PythonTrue,             // True instead of true
    PythonFalse,            // False instead of false
    PythonElif,             // elif is correct (not else if)

    // Rust-style
    RustLetMut,             // let mut instead of var
    RustFnMut,              // fn(&mut self) instead of me fn()
    RustLifetime,           // 'a lifetime syntax not supported
    RustMacro,              // macro! syntax
    RustTurbofish,          // ::<T> instead of <T>

    // Java/C++ style
    JavaPublicClass,        // public class instead of pub class
    JavaVoid,               // void instead of no return type
    JavaNew,                // new Type() instead of Type {}
    JavaThis,               // this instead of self
    CppTemplate,            // template<T> instead of <T>
    CppNamespace,           // namespace instead of mod

    // TypeScript/JavaScript
    TsFunction,             // function instead of fn
    TsConst,                // const instead of val
    TsLet,                  // let instead of val (warn if immutable)
    TsInterface,            // interface instead of trait
    TsArrowFunction,        // => in function definition

    // C-style
    CSemicolon,             // unnecessary semicolons
    CTypeFirst,             // int x instead of val x: i32

    // Generic mistakes
    MissingColon,           // Missing : before type/block
    WrongBrackets,          // [] instead of <> for generics
    ExplicitSelf,           // (self) parameter when implicit
    VerboseReturnType,      // -> Type when type inference works
    SemicolonAfterBlock,    // }; instead of }
}

impl CommonMistake {
    /// Get helpful error message for this mistake
    pub fn message(&self) -> String {
        match self {
            // Python
            Self::PythonDef => {
                "Use 'fn' to define functions in Simple, not 'def'.\n\
                 \n\
                 Python:  def add(a, b):\n\
                 Simple:  fn add(a, b):".to_string()
            }
            Self::PythonSelf => {
                "In Simple, 'self' is implicit in methods. Don't write 'self.'.\n\
                 \n\
                 Python:  self.x = value\n\
                 Simple:  x = value     # self is implicit in methods".to_string()
            }
            Self::PythonNone => {
                "Use 'nil' instead of 'None' in Simple.\n\
                 \n\
                 Python:  return None\n\
                 Simple:  return nil".to_string()
            }
            Self::PythonTrue | Self::PythonFalse => {
                "Use lowercase 'true' and 'false' in Simple.\n\
                 \n\
                 Python:  if True:\n\
                 Simple:  if true:".to_string()
            }
            Self::PythonElif => {
                "'elif' is the correct syntax in Simple (not 'else if').\n\
                 \n\
                 Python:  elif x > 0:\n\
                 Simple:  elif x > 0:  # elif is built-in".to_string()
            }

            // Rust
            Self::RustLetMut => {
                "Use 'var' for mutable variables, 'val' for immutable.\n\
                 \n\
                 Rust:    let mut x = 5;\n\
                 Simple:  var x = 5     # mutable\n\
                          val y = 10    # immutable (preferred)".to_string()
            }
            Self::RustFnMut => {
                "Use 'me' keyword for mutable methods, 'self' is implicit.\n\
                 \n\
                 Rust:    fn update(&mut self) {}\n\
                 Simple:  me update():  # 'me' keyword, self implicit".to_string()
            }
            Self::RustLifetime => {
                "Simple doesn't use Rust-style lifetime annotations.\n\
                 Reference capabilities (mut/iso) handle memory safety instead.".to_string()
            }
            Self::RustTurbofish => {
                "Use <T> syntax directly, not ::<T>.\n\
                 \n\
                 Rust:    vec.collect::<Vec<_>>()\n\
                 Simple:  vec.collect<Vec<T>>()".to_string()
            }
            Self::RustMacro => {
                "Simple uses '@' for macros, not '!'.\n\
                 \n\
                 Rust:    println!(\"hello\");\n\
                 Simple:  @println(\"hello\")".to_string()
            }

            // Java/C++
            Self::JavaPublicClass => {
                "Use 'pub class' or 'pub struct' in Simple.\n\
                 \n\
                 Java:    public class Point {}\n\
                 Simple:  pub class Point:  # or 'pub struct Point:'".to_string()
            }
            Self::JavaVoid => {
                "Omit return type for void functions in Simple.\n\
                 \n\
                 Java:    void print(String s) {}\n\
                 Simple:  fn print(s: String):  # no return type".to_string()
            }
            Self::JavaNew => {
                "Use struct literal syntax instead of 'new'.\n\
                 \n\
                 Java:    Point p = new Point(1, 2);\n\
                 Simple:  val p = Point { x: 1, y: 2 }".to_string()
            }
            Self::JavaThis => {
                "Use 'self' instead of 'this' (and it's implicit in methods).\n\
                 \n\
                 Java:    this.x = value;\n\
                 Simple:  x = value  # self is implicit".to_string()
            }
            Self::CppTemplate => {
                "Generic parameters come after the name in Simple.\n\
                 \n\
                 C++:     template<typename T> class Vec {};\n\
                 Simple:  struct Vec<T>:".to_string()
            }
            Self::CppNamespace => {
                "Use 'mod' for modules instead of 'namespace'.\n\
                 \n\
                 C++:     namespace math {}\n\
                 Simple:  mod math:".to_string()
            }

            // TypeScript/JavaScript
            Self::TsFunction => {
                "Use 'fn' to define functions in Simple.\n\
                 \n\
                 TypeScript:  function add(a, b) {}\n\
                 Simple:      fn add(a, b):".to_string()
            }
            Self::TsConst => {
                "Use 'val' for immutable variables in Simple.\n\
                 \n\
                 TypeScript:  const x = 5;\n\
                 Simple:      val x = 5".to_string()
            }
            Self::TsLet => {
                "Use 'val' for immutable or 'var' for mutable variables.\n\
                 \n\
                 TypeScript:  let x = 5;  // could be reassigned\n\
                 Simple:      val x = 5   // immutable (preferred)\n\
                              var y = 5   // mutable".to_string()
            }
            Self::TsInterface => {
                "Use 'trait' instead of 'interface' in Simple.\n\
                 \n\
                 TypeScript:  interface Named {}\n\
                 Simple:      trait Named:".to_string()
            }
            Self::TsArrowFunction => {
                "Use ':' for function bodies, '=>' is for lambdas.\n\
                 \n\
                 TypeScript:  const add = (a, b) => a + b;\n\
                 Simple:      val add = \\a, b: a + b  # lambda uses backslash".to_string()
            }

            // C-style
            Self::CSemicolon => {
                "Semicolons are optional in Simple (only needed for same-line statements).\n\
                 \n\
                 C:       int x = 5;\n\
                 Simple:  val x = 5  # no semicolon needed".to_string()
            }
            Self::CTypeFirst => {
                "Type comes after the variable name in Simple.\n\
                 \n\
                 C:       int x = 5;\n\
                 Simple:  val x: i32 = 5  # type after name\n\
                          val x = 5       # or use type inference".to_string()
            }

            // Generic
            Self::MissingColon => {
                "Function and block definitions require ':' before the body.\n\
                 \n\
                 Missing: fn foo()\n\
                 Correct: fn foo():".to_string()
            }
            Self::WrongBrackets => {
                "Use angle brackets <> for generic types (not square brackets).\n\
                 \n\
                 Old:     List[T]\n\
                 New:     List<T>  # industry standard".to_string()
            }
            Self::ExplicitSelf => {
                "The 'self' parameter is implicit in methods. Don't write it.\n\
                 \n\
                 Explicit:  fn get_x(self) -> i32:  # redundant\n\
                 Implicit:  fn get_x() -> i32:      # self is automatic".to_string()
            }
            Self::VerboseReturnType => {
                "Return type can be inferred. Only specify when needed for clarity.\n\
                 \n\
                 Verbose:  fn add(a: i32, b: i32) -> i32: a + b\n\
                 Concise:  fn add(a: i32, b: i32): a + b  # return type inferred".to_string()
            }
            Self::SemicolonAfterBlock => {
                "Don't use semicolons after block closures.\n\
                 \n\
                 Wrong:  if x > 0: { ... };\n\
                 Right:  if x > 0: { ... }".to_string()
            }
        }
    }

    /// Get suggested fix
    pub fn suggestion(&self) -> String {
        match self {
            Self::PythonDef => "Replace 'def' with 'fn'".to_string(),
            Self::PythonNone => "Replace 'None' with 'nil'".to_string(),
            Self::PythonTrue => "Replace 'True' with 'true'".to_string(),
            Self::PythonFalse => "Replace 'False' with 'false'".to_string(),
            Self::PythonElif => "'elif' is correct - use it instead of 'else if'".to_string(),
            Self::RustLetMut => "Use 'var' instead of 'let mut'".to_string(),
            Self::RustMacro => "Use '@' for macros instead of '!'".to_string(),
            Self::RustFnMut => "Use 'me' keyword instead of '&mut self' parameter".to_string(),
            Self::JavaPublicClass => "Use 'pub class' or 'pub struct'".to_string(),
            Self::JavaVoid => "Omit the return type (-> Type) for void functions".to_string(),
            Self::JavaNew => "Use struct literal: Type { field: value }".to_string(),
            Self::JavaThis => "Use 'self' (which is implicit in methods)".to_string(),
            Self::TsFunction => "Replace 'function' with 'fn'".to_string(),
            Self::TsConst => "Replace 'const' with 'val'".to_string(),
            Self::TsLet => "Use 'val' (immutable) or 'var' (mutable)".to_string(),
            Self::TsInterface => "Replace 'interface' with 'trait'".to_string(),
            Self::MissingColon => "Add ':' before the function body".to_string(),
            Self::WrongBrackets => "Use <> instead of [] for generics".to_string(),
            Self::ExplicitSelf => "Remove the 'self' parameter (it's implicit)".to_string(),
            Self::VerboseReturnType => "Consider omitting return type (type inference works)".to_string(),
            Self::CTypeFirst => "Use 'val' or 'var' with type after name".to_string(),
            _ => "See error message for details".to_string(),
        }
    }
}

/// Detect common mistakes from token sequences
pub fn detect_common_mistake(
    current: &Token,
    previous: &Token,
    next: Option<&Token>,
) -> Option<CommonMistake> {
    // Check for Python-style 'def'
    if current.lexeme == "def" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::PythonDef);
    }

    // Check for 'None' (Python)
    if current.lexeme == "None" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::PythonNone);
    }

    // Check for 'True' or 'False' (Python/Java)
    if current.lexeme == "True" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::PythonTrue);
    }
    if current.lexeme == "False" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::PythonFalse);
    }

    // Check for 'let mut' (Rust)
    if matches!(previous.kind, TokenKind::Let)
        && current.lexeme == "mut"
        && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::RustLetMut);
    }

    // Check for 'public class' (Java)
    if current.lexeme == "public" && matches!(current.kind, TokenKind::Identifier(_)) {
        if let Some(next_token) = next {
            if next_token.lexeme == "class" {
                return Some(CommonMistake::JavaPublicClass);
            }
        }
    }

    // Check for 'void' (Java/C++)
    if current.lexeme == "void" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::JavaVoid);
    }

    // Check for 'new' keyword (Java/C++) - but NOT when used as method name after dot
    // In Simple, 'new' is a valid method name for constructors (e.g., Type.new())
    // Only flag standalone 'new Type()' pattern as a mistake
    if matches!(current.kind, TokenKind::New) && !matches!(previous.kind, TokenKind::Dot) {
        return Some(CommonMistake::JavaNew);
    }

    // Check for 'this' (Java/JavaScript)
    if current.lexeme == "this" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::JavaThis);
    }

    // Check for 'function' (JavaScript/TypeScript)
    if current.lexeme == "function" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::TsFunction);
    }

    // Check for 'const' (TypeScript/JavaScript)
    if current.lexeme == "const" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::TsConst);
    }

    // Check for 'interface' (TypeScript/Java)
    if current.lexeme == "interface" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::TsInterface);
    }

    // Check for 'namespace' (C++)
    if current.lexeme == "namespace" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::CppNamespace);
    }

    // Check for 'template' (C++)
    if current.lexeme == "template" && matches!(current.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::CppTemplate);
    }

    // Check for 'let' without 'mut' (TypeScript/JavaScript) - info level suggestion to use val/var
    if matches!(current.kind, TokenKind::Let) {
        // Only suggest if not followed by 'mut' (which is already handled above)
        if let Some(next_token) = next {
            if next_token.lexeme != "mut" {
                return Some(CommonMistake::TsLet);
            }
        } else {
            return Some(CommonMistake::TsLet);
        }
    }

    // Check for Python-style explicit self.x (when 'self' keyword is followed by dot)
    if matches!(current.kind, TokenKind::Self_)
        && !matches!(previous.kind, TokenKind::Fn | TokenKind::Me) {
        // This is 'self' being used explicitly (not in method signature)
        if let Some(next_token) = next {
            if matches!(next_token.kind, TokenKind::Dot) {
                return Some(CommonMistake::PythonSelf);
            }
        }
    }

    // Check for TypeScript arrow function: ) =>
    if matches!(current.kind, TokenKind::FatArrow)
        && matches!(previous.kind, TokenKind::RParen) {
        return Some(CommonMistake::TsArrowFunction);
    }

    // Check for wrong brackets in generics: identifier[
    if matches!(current.kind, TokenKind::LBracket)
        && matches!(previous.kind, TokenKind::Identifier(_)) {
        // This could be array indexing, but if followed by type-like identifier, likely generic
        if let Some(next_token) = next {
            // Check if next token looks like a type (capitalized identifier)
            if let TokenKind::Identifier(ref name) = next_token.kind {
                if name.chars().next().map_or(false, |c| c.is_uppercase()) {
                    return Some(CommonMistake::WrongBrackets);
                }
            }
        }
    }

    // Check for Rust turbofish: ::<
    if matches!(current.kind, TokenKind::Lt)
        && matches!(previous.kind, TokenKind::DoubleColon) {
        return Some(CommonMistake::RustTurbofish);
    }

    // Check for Rust macro syntax: identifier!
    if current.lexeme == "!"
        && matches!(current.kind, TokenKind::Not)
        && matches!(previous.kind, TokenKind::Identifier(_)) {
        return Some(CommonMistake::RustMacro);
    }

    // Check for C-style type-first declarations: int x, float y, etc.
    if let TokenKind::Identifier(ref type_name) = current.kind {
        // Common C/C++/Java type names
        let c_types = [
            "int", "uint", "float", "double", "char", "long", "short",
            "byte", "boolean", "void", "string", "String",
            "int8", "int16", "int32", "int64",
            "uint8", "uint16", "uint32", "uint64",
            "float32", "float64",
        ];

        if c_types.contains(&type_name.as_str()) {
            // Check if followed by identifier (likely a variable name)
            if let Some(next_token) = next {
                if matches!(next_token.kind, TokenKind::Identifier(_)) {
                    return Some(CommonMistake::CTypeFirst);
                }
            }
        }
    }

    None
}

/// Warning levels for diagnostics
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ErrorHintLevel {
    Error,
    Warning,
    Info,
    Hint,
}

/// Diagnostic message with helpful information
#[derive(Debug, Clone)]
pub struct ErrorHint {
    pub level: ErrorHintLevel,
    pub message: String,
    pub span: Span,
    pub suggestion: Option<String>,
    pub help: Option<String>,
}

impl ErrorHint {
    pub fn error(message: String, span: Span) -> Self {
        Self {
            level: ErrorHintLevel::Error,
            message,
            span,
            suggestion: None,
            help: None,
        }
    }

    pub fn warning(message: String, span: Span) -> Self {
        Self {
            level: ErrorHintLevel::Warning,
            message,
            span,
            suggestion: None,
            help: None,
        }
    }

    pub fn with_suggestion(mut self, suggestion: String) -> Self {
        self.suggestion = Some(suggestion);
        self
    }

    pub fn with_help(mut self, help: String) -> Self {
        self.help = Some(help);
        self
    }

    /// Format diagnostic for display
    pub fn format(&self, source: &str) -> String {
        let level_str = match self.level {
            ErrorHintLevel::Error => "error",
            ErrorHintLevel::Warning => "warning",
            ErrorHintLevel::Info => "info",
            ErrorHintLevel::Hint => "hint",
        };

        let mut output = format!(
            "{}: {}\n  --> line {}:{}\n",
            level_str, self.message, self.span.line, self.span.column
        );

        // Show source line with caret
        if let Some(line) = source.lines().nth(self.span.line - 1) {
            output.push_str(&format!("   |\n"));
            output.push_str(&format!("{:3} | {}\n", self.span.line, line));
            output.push_str(&format!(
                "   | {}^\n",
                " ".repeat(self.span.column - 1)
            ));
        }

        if let Some(ref suggestion) = self.suggestion {
            output.push_str(&format!("\nSuggestion: {}\n", suggestion));
        }

        if let Some(ref help) = self.help {
            output.push_str(&format!("\nHelp: {}\n", help));
        }

        output
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_python_def_detection() {
        let token = Token::new(
            TokenKind::Identifier("def".to_string()),
            Span::new(0, 3, 1, 1),
            "def".to_string(),
        );
        let prev = Token::new(TokenKind::Newline, Span::new(0, 0, 1, 1), "".to_string());

        let mistake = detect_common_mistake(&token, &prev, None);
        assert_eq!(mistake, Some(CommonMistake::PythonDef));
    }

    #[test]
    fn test_mistake_messages() {
        let mistake = CommonMistake::PythonDef;
        let msg = mistake.message();
        assert!(msg.contains("Use 'fn'"));
        assert!(msg.contains("not 'def'"));
    }
}
