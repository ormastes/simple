use super::{CheckError, ErrorSeverity};
use simple_parser::ast::{Block, Expr, Node, Pattern, Type};
use simple_parser::NumericSuffix;
use std::path::Path;

pub(super) fn validate_basic_type_annotations(file_path: &Path, items: &[Node], errors: &mut Vec<CheckError>) {
    for item in items {
        validate_basic_type_annotation_node(file_path, item, None, errors);
    }
}

fn validate_basic_type_annotation_node(
    file_path: &Path,
    item: &Node,
    return_type: Option<&Type>,
    errors: &mut Vec<CheckError>,
) {
    match item {
        Node::Function(function) => {
            validate_basic_type_annotation_block(file_path, &function.body, function.return_type.as_ref(), errors);
        }
        Node::Let(stmt) => {
            if let (Some(expected), Some(value)) = (declared_type(&stmt.ty, &stmt.pattern), stmt.value.as_ref()) {
                validate_literal_type(file_path, stmt.span.line, stmt.span.column, expected, value, errors);
            }
        }
        Node::Const(stmt) => {
            if let Some(expected) = stmt.ty.as_ref() {
                validate_literal_type(
                    file_path,
                    stmt.span.line,
                    stmt.span.column,
                    expected,
                    &stmt.value,
                    errors,
                );
            }
        }
        Node::Static(stmt) => {
            if let Some(expected) = stmt.ty.as_ref() {
                validate_literal_type(
                    file_path,
                    stmt.span.line,
                    stmt.span.column,
                    expected,
                    &stmt.value,
                    errors,
                );
            }
        }
        Node::Return(stmt) => {
            if let (Some(expected), Some(value)) = (return_type, stmt.value.as_ref()) {
                validate_literal_type(file_path, stmt.span.line, stmt.span.column, expected, value, errors);
            }
        }
        Node::If(stmt) => {
            validate_basic_type_annotation_block(file_path, &stmt.then_block, return_type, errors);
            for (_, _, block) in &stmt.elif_branches {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
            if let Some(block) = &stmt.else_block {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
        }
        Node::For(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::While(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::Loop(stmt) => validate_basic_type_annotation_block(file_path, &stmt.body, return_type, errors),
        Node::Skip(stmt) => {
            if let simple_parser::ast::SkipBody::Block(block) = &stmt.body {
                validate_basic_type_annotation_block(file_path, block, return_type, errors);
            }
        }
        _ => {}
    }
}

fn validate_basic_type_annotation_block(
    file_path: &Path,
    block: &Block,
    return_type: Option<&Type>,
    errors: &mut Vec<CheckError>,
) {
    for statement in &block.statements {
        validate_basic_type_annotation_node(file_path, statement, return_type, errors);
    }
}

fn declared_type<'a>(explicit: &'a Option<Type>, pattern: &'a Pattern) -> Option<&'a Type> {
    explicit.as_ref().or_else(|| match pattern {
        Pattern::Typed { ty, .. } => Some(ty),
        _ => None,
    })
}

fn validate_literal_type(
    file_path: &Path,
    line: usize,
    column: usize,
    expected: &Type,
    value: &Expr,
    errors: &mut Vec<CheckError>,
) {
    let Some(expected_name) = simple_type_name(expected) else {
        return;
    };
    let Some(found_type) = literal_type_name(value) else {
        return;
    };
    let found_name = found_type.display_name();
    if found_name == "nil" {
        return;
    }
    if type_names_compatible(expected_name, found_name) {
        return;
    }
    if numeric_literal_type_compatible(expected_name, found_type) {
        return;
    }

    errors.push(CheckError {
        file: file_path.display().to_string(),
        line,
        column,
        severity: ErrorSeverity::Error,
        code: Some("E1003".to_string()),
        message: format!("type mismatch: expected {}, found {}", expected_name, found_name),
        expected: Some(expected_name.to_string()),
        found: Some(found_name.to_string()),
        notes: Vec::new(),
        help: vec!["change the annotation or use a value with the declared type".to_string()],
    });
}

fn simple_type_name(ty: &Type) -> Option<&str> {
    match ty {
        Type::Simple(name) => Some(name.as_str()),
        _ => None,
    }
}

#[derive(Debug, Clone, Copy)]
enum LiteralTypeName {
    Exact(&'static str),
    UnsuffixedInteger,
    UnsuffixedFloat,
}

impl LiteralTypeName {
    fn display_name(self) -> &'static str {
        match self {
            Self::Exact(name) => name,
            Self::UnsuffixedInteger => "i64",
            Self::UnsuffixedFloat => "f64",
        }
    }
}

fn literal_type_name(expr: &Expr) -> Option<LiteralTypeName> {
    match expr {
        Expr::Integer(_) => Some(LiteralTypeName::UnsuffixedInteger),
        Expr::TypedInteger(_, suffix) => Some(LiteralTypeName::Exact(integer_suffix_type_name(suffix))),
        Expr::Float(_) => Some(LiteralTypeName::UnsuffixedFloat),
        Expr::TypedFloat(_, suffix) => Some(LiteralTypeName::Exact(float_suffix_type_name(suffix))),
        Expr::String(_) | Expr::TypedString(_, _) | Expr::FString { .. } => Some(LiteralTypeName::Exact("text")),
        Expr::Bool(_) => Some(LiteralTypeName::Exact("bool")),
        Expr::Nil => Some(LiteralTypeName::Exact("nil")),
        _ => None,
    }
}

fn integer_suffix_type_name(suffix: &NumericSuffix) -> &'static str {
    match suffix {
        NumericSuffix::I8 => "i8",
        NumericSuffix::I16 => "i16",
        NumericSuffix::I32 => "i32",
        NumericSuffix::I64 => "i64",
        NumericSuffix::U8 => "u8",
        NumericSuffix::U16 => "u16",
        NumericSuffix::U32 => "u32",
        NumericSuffix::U64 => "u64",
        NumericSuffix::F32 => "f32",
        NumericSuffix::F64 => "f64",
        NumericSuffix::Unit(_) => "i64",
    }
}

fn float_suffix_type_name(suffix: &NumericSuffix) -> &'static str {
    match suffix {
        NumericSuffix::F32 => "f32",
        NumericSuffix::F64 => "f64",
        NumericSuffix::Unit(_) => "f64",
        NumericSuffix::I8
        | NumericSuffix::I16
        | NumericSuffix::I32
        | NumericSuffix::I64
        | NumericSuffix::U8
        | NumericSuffix::U16
        | NumericSuffix::U32
        | NumericSuffix::U64 => "f64",
    }
}

fn type_names_compatible(expected: &str, found: &str) -> bool {
    is_any_type_name(expected)
        || expected == found
        || matches!(
            (expected, found),
            ("str", "text")
                | ("String", "text")
                | ("Text", "text")
                | ("Bool", "bool")
                | ("Boolean", "bool")
                | ("Int", "i64")
                | ("Integer", "i64")
                | ("Float", "f64")
        )
}

fn numeric_literal_type_compatible(expected: &str, found: LiteralTypeName) -> bool {
    match found {
        LiteralTypeName::UnsuffixedInteger => is_integer_type_name(expected),
        LiteralTypeName::UnsuffixedFloat => is_float_type_name(expected),
        LiteralTypeName::Exact(_) => false,
    }
}

fn is_integer_type_name(name: &str) -> bool {
    matches!(
        name,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "Int"
            | "Integer"
    )
}

fn is_float_type_name(name: &str) -> bool {
    matches!(name, "f32" | "f64" | "Float")
}

fn is_any_type_name(name: &str) -> bool {
    matches!(name, "any" | "Any")
}
