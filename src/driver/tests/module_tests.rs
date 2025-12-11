//! System tests for module system (Features #104-111)
//!
//! Tests for:
//! - Module path syntax (dot-separated)
//! - use statements (single, group, glob)
//! - mod declarations
//! - common use (directory prelude)
//! - export use (re-exports)
//! - auto import (macro glob inclusion)
//! - Visibility control

mod test_helpers;
use test_helpers::{run_expect_interp, run_expect_compile_error};

// =============================================================================
// Feature #104: Module Path Syntax
// =============================================================================

#[test]
fn module_path_dot_separated_parsing() {
    // Simple module path should parse without error
    run_expect_interp(
        r#"
use crate.core.base
main = 0
"#,
        0,
    );
}

#[test]
fn module_path_multiple_segments() {
    run_expect_interp(
        r#"
use crate.sys.http.router
main = 0
"#,
        0,
    );
}

// =============================================================================
// Feature #107: Import System - use statements
// =============================================================================

#[test]
fn use_single_item() {
    // use module.Name - single item import
    run_expect_interp(
        r#"
use crate.core.Option
main = 0
"#,
        0,
    );
}

#[test]
fn use_group_items() {
    // use module.{A, B, C} - group import
    run_expect_interp(
        r#"
use crate.core.{Option, Result, Vec}
main = 0
"#,
        0,
    );
}

#[test]
fn use_glob() {
    // use module.* - glob import
    run_expect_interp(
        r#"
use crate.core.*
main = 0
"#,
        0,
    );
}

#[test]
fn use_with_alias() {
    // use module.Name as Alias
    run_expect_interp(
        r#"
use crate.core.Option as Opt
main = 0
"#,
        0,
    );
}

// =============================================================================
// Feature #106: mod declarations
// =============================================================================

#[test]
fn mod_declaration_simple() {
    // mod name - private module declaration
    run_expect_interp(
        r#"
mod internal
main = 0
"#,
        0,
    );
}

#[test]
fn mod_declaration_public() {
    // pub mod name - public module declaration
    run_expect_interp(
        r#"
pub mod router
main = 0
"#,
        0,
    );
}

#[test]
fn mod_declaration_with_attribute() {
    // #[attr] mod name - attributed module
    run_expect_interp(
        r#"
#[no_gc]
pub mod driver
main = 0
"#,
        0,
    );
}

// =============================================================================
// Feature #107: common use (directory prelude)
// =============================================================================

#[test]
fn common_use_glob() {
    // common use module.* - directory prelude
    run_expect_interp(
        r#"
common use crate.core.base.*
main = 0
"#,
        0,
    );
}

#[test]
fn common_use_single() {
    // common use module.Name
    run_expect_interp(
        r#"
common use crate.net.Url
main = 0
"#,
        0,
    );
}

// =============================================================================
// Feature #107: export use (re-exports)
// =============================================================================

#[test]
fn export_use_single() {
    // export use module.Name
    run_expect_interp(
        r#"
export use router.Router
main = 0
"#,
        0,
    );
}

#[test]
fn export_use_group() {
    // export use module.{A, B}
    run_expect_interp(
        r#"
export use router.{Client, Request}
main = 0
"#,
        0,
    );
}

#[test]
fn export_use_glob() {
    // export use module.*
    run_expect_interp(
        r#"
export use router.*
main = 0
"#,
        0,
    );
}

// =============================================================================
// Feature #108: auto import (macro glob inclusion)
// =============================================================================

#[test]
fn auto_import_macro() {
    // auto import module.macro_name
    run_expect_interp(
        r#"
auto import router.route
main = 0
"#,
        0,
    );
}

#[test]
fn auto_import_multiple() {
    // Multiple auto imports
    run_expect_interp(
        r#"
auto import router.route
auto import router.route_get
main = 0
"#,
        0,
    );
}

// =============================================================================
// Combined: Complete __init__.spl pattern
// =============================================================================

#[test]
fn init_spl_complete_pattern() {
    // Complete __init__.spl structure
    run_expect_interp(
        r#"
mod http

pub mod router
mod internal

common use crate.core.base.*

export use router.Router
export use router.route

auto import router.route
auto import router.route_get

main = 0
"#,
        0,
    );
}

// =============================================================================
// Error cases
// =============================================================================

#[test]
fn use_invalid_syntax_error() {
    // Invalid use syntax should error
    run_expect_compile_error(
        r#"
use
main = 0
"#,
        "expected",
    );
}

#[test]
fn mod_missing_name_error() {
    // mod without name should error
    run_expect_compile_error(
        r#"
mod
main = 0
"#,
        "expected",
    );
}
