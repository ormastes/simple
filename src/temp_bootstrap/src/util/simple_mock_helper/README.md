Below is a full “v1” of simple_mock_helper with:

The mock policy library (as we discussed).

A coverage utility that reads llvm-cov export -format=json and a simple public_api.yml, and produces:

Per-class/struct public method coverage.

Overall summary.


A usage document you can drop into your repo.


I’ll assume C++ / LLVM coverage.


---

1. Crate layout

Recommended structure:

simple_mock_helper/
  Cargo.toml
  src/
    lib.rs
    mock_policy.rs
    coverage.rs
  src/bin/
    smh_coverage.rs


---

2. Cargo.toml

[package]
name = "simple_mock_helper"
version = "0.1.0"
edition = "2021"

[dependencies]
once_cell = "1"
serde = { version = "1", features = ["derive"] }
serde_json = "1"
serde_yaml = "0.9"
clap = { version = "4", features = ["derive"] }
anyhow = "1"

[dev-dependencies]
ctor = "0.2"

You can move ctor to normal [dependencies] if you also use it outside tests.


---

3. src/lib.rs

pub mod mock_policy;
pub mod coverage;


---

4. src/mock_policy.rs

Same semantics as before, but packaged in this crate.

//! simple_mock_helper::mock_policy
//!
//! Policy-based control of when mocks are allowed.
//!
//! Typical usage per test binary:
//!   - Unit tests:    call `init_mocks_for_only(&["*"]);` (allow all).
//!   - Integration:   call `init_mocks_for_only_default();` (HAL-only).
//!   - System tests:  call `init_mocks_for_system();` (no mocks).
//!
//! Each mock wrapper calls `check_mock_use_from(module_path!())`.

use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::OnceLock;

/// Are mocks enabled in this test binary?
static MOCKS_ENABLED: AtomicBool = AtomicBool::new(false);

/// Allowed module patterns (first init wins).
static ALLOWED_PATTERNS: OnceLock<Vec<&'static str>> = OnceLock::new();

/// Default patterns: allow only modules under `::hal::` and `::sub_hal::`.
pub const DEFAULT_HAL_PATTERNS: &[&str] = &["*::hal::*", "*::sub_hal::*"];

/// Enable mocks, restricting usage to modules whose `module_path!()`
/// matches at least one of `patterns`.
///
/// Pattern rules:
/// - Use `::` as module separator.
/// - `*` is a wildcard for any sequence of characters.
pub fn init_mocks_for_only(patterns: &'static [&'static str]) {
    let _ = ALLOWED_PATTERNS.set(patterns.to_vec());
    MOCKS_ENABLED.store(true, Ordering::SeqCst);
}

/// Convenience: enable the default HAL-only policy.
pub fn init_mocks_for_only_default() {
    init_mocks_for_only(DEFAULT_HAL_PATTERNS);
}

/// Disable all mocks for this test binary.
pub fn init_mocks_for_system() {
    MOCKS_ENABLED.store(false, Ordering::SeqCst);
}

/// Check whether a mock from `source_path` (usually `module_path!()`)
/// is allowed under the current policy.
///
/// Panics if:
/// - Mocks are disabled, or
/// - No pattern matches `source_path`, or
/// - Policy was never initialized.
pub fn check_mock_use_from(source_path: &str) {
    if !MOCKS_ENABLED.load(Ordering::SeqCst) {
        panic!("Mock used while mocks are disabled (system test policy)");
    }

    let patterns = ALLOWED_PATTERNS
        .get()
        .expect("Mock policy not initialized. Call init_mocks_for_only*() once per test binary.");

    for pat in patterns {
        if pattern_matches(source_path, pat) {
            return;
        }
    }

    panic!(
        "Mock from `{}` not allowed by current mock policy",
        source_path
    );
}

/// Simple wildcard matcher:
/// - `*` → any sequence of chars.
/// - other characters literal.
/// - No normalization: expect both `path` and `pat` to use `::`.
fn pattern_matches(path: &str, pat: &str) -> bool {
    if !pat.contains('*') {
        return path.contains(pat);
    }

    let parts: Vec<&str> = pat.split('*').filter(|p| !p.is_empty()).collect();
    if parts.is_empty() {
        return true; // pattern was "*" or only "*"
    }

    let mut idx = 0;
    for part in parts {
        if let Some(off) = path[idx..].find(part) {
            idx += off + part.len();
        } else {
            return false;
        }
    }
    true
}


---

5. src/coverage.rs

This is the library side of the LLVM coverage → class/public-method coverage tool.

It assumes:

You ran llvm-cov export -format=json and saved it to a file.

You maintain a public_api.yml describing which types and methods you consider “public”.


5.1 Coverage data structures and API

//! simple_mock_helper::coverage
//!
//! Utilities to derive class/struct public-method coverage from
//! LLVM coverage JSON (`llvm-cov export -format=json`).
//!
//! Pipeline:
//!   1) Merge profraw → profdata
//!   2) `llvm-cov export -format=json`
//!   3) Load `public_api.yml`
///  4) Call `compute_class_coverage`
//!   5) Optionally use `print_class_coverage_table` or your own output.

use serde::Deserialize;
use std::collections::{HashMap, HashSet};
use std::fs;
use std::path::Path;

/// Minimal subset of `llvm-cov export` JSON we care about.
///
/// Shape (simplified):
/// {
///   "data": [ { "functions": [ { "name": "...", "count": 0, ... }, ... ] } ]
/// }
#[derive(Debug, Deserialize)]
pub struct LlvmCovExport {
    pub data: Vec<LlvmCovData>,
}

#[derive(Debug, Deserialize)]
pub struct LlvmCovData {
    #[serde(default)]
    pub functions: Vec<LlvmFunction>,
}

#[derive(Debug, Deserialize)]
pub struct LlvmFunction {
    pub name: String,
    #[serde(default)]
    pub count: u64,
}

/// YAML specification of which types and methods you consider "public".
///
/// Example YAML:
///
/// ```yaml
/// types:
///   MyNamespace::Foo:
///     methods: [do_stuff, reset]
///   Bar:
///     methods:
///       - run
///       - stop
/// ```
#[derive(Debug, Deserialize)]
pub struct PublicApiSpec {
    pub types: HashMap<String, PublicTypeSpec>,
}

#[derive(Debug, Deserialize)]
pub struct PublicTypeSpec {
    pub methods: Vec<String>,
}

/// Per-method coverage result.
#[derive(Debug)]
pub struct MethodCoverage {
    pub type_name: String,
    pub method_name: String,
    pub covered: bool,
}

/// Per-type coverage result.
#[derive(Debug)]
pub struct ClassCoverage {
    pub type_name: String,
    pub total_methods: usize,
    pub covered_methods: usize,
    pub methods: Vec<MethodCoverage>,
}

impl ClassCoverage {
    pub fn coverage_percent(&self) -> f64 {
        if self.total_methods == 0 {
            100.0
        } else {
            (self.covered_methods as f64) * 100.0 / (self.total_methods as f64)
        }
    }
}

/// Load LLVM coverage JSON from a file produced by:
/// `llvm-cov export -format=json`.
pub fn load_llvm_cov_export<P: AsRef<Path>>(path: P) -> anyhow::Result<LlvmCovExport> {
    let text = fs::read_to_string(path)?;
    let export: LlvmCovExport = serde_json::from_str(&text)?;
    Ok(export)
}

/// Load public API specification from a YAML file.
pub fn load_public_api_spec<P: AsRef<Path>>(path: P) -> anyhow::Result<PublicApiSpec> {
    let text = fs::read_to_string(path)?;
    let spec: PublicApiSpec = serde_yaml::from_str(&text)?;
    Ok(spec)
}

/// Compute class/struct coverage for public methods based on:
/// - LLVM coverage JSON (function list + counts).
/// - Public API spec (types + methods).
///
/// Matching rule:
///   coverage_function.name ~ "<type_name>::<method_name>" (suffix match).
///
/// If any instance of that function has non-zero count, we treat it as covered.
pub fn compute_class_coverage(
    cov: &LlvmCovExport,
    api: &PublicApiSpec,
) -> Vec<ClassCoverage> {
    // Flatten all functions from all "data" entries.
    let mut fn_names_counts: Vec<(&str, u64)> = Vec::new();
    for d in &cov.data {
        for f in &d.functions {
            fn_names_counts.push((&f.name, f.count));
        }
    }

    // Build a set of covered (type, method) pairs.
    let mut covered_pairs: HashSet<(String, String)> = HashSet::new();

    for (fname, count) in fn_names_counts {
        if count == 0 {
            continue;
        }

        // Heuristic: C++ member functions typically appear as
        // "Namespace::Type::method(...)" or "Type::method".
        if let Some((type_name, method_name)) = split_type_method(fname) {
            covered_pairs.insert((type_name.to_string(), method_name.to_string()));
        }
    }

    // For each type in public API, compute coverage.
    let mut results = Vec::new();

    for (type_name, tspec) in &api.types {
        let mut methods_cov = Vec::new();
        let mut covered_count = 0usize;

        for m in &tspec.methods {
            let key = (type_name.clone(), m.clone());
            let covered = covered_pairs.contains(&key);
            if covered {
                covered_count += 1;
            }

            methods_cov.push(MethodCoverage {
                type_name: type_name.clone(),
                method_name: m.clone(),
                covered,
            });
        }

        results.push(ClassCoverage {
            type_name: type_name.clone(),
            total_methods: tspec.methods.len(),
            covered_methods: covered_count,
            methods: methods_cov,
        });
    }

    results
}

/// Split a fully-qualified function name into (type_name, method_name)
/// using a simple heuristic:
///
/// - Take everything up to last "::" as `type_name`.
/// - Take last component as `method_name`.
///
/// Returns None for free functions (no "::").
fn split_type_method(name: &str) -> Option<(&str, &str)> {
    let parts: Vec<&str> = name.split("::").collect();
    if parts.len() < 2 {
        return None;
    }
    let method_name = *parts.last().unwrap();
    let type_name = &name[..name.len() - method_name.len() - "::".len()];
    Some((type_name, method_name))
}

/// Simple pretty-printer for class coverage results.
///
/// `type_filter` is an optional substring filter on type_name.
pub fn print_class_coverage_table(results: &[ClassCoverage], type_filter: Option<&str>) {
    println!("{:<50} {:>9} {:>9} {:>9}", "Type", "Covered", "Total", "Percent");

    let mut total_methods = 0usize;
    let mut total_covered = 0usize;

    for cc in results {
        if let Some(filter) = type_filter {
            if !cc.type_name.contains(filter) {
                continue;
            }
        }

        total_methods += cc.total_methods;
        total_covered += cc.covered_methods;

        println!(
            "{:<50} {:>4} / {:<4} {:>7.2}%",
            cc.type_name,
            cc.covered_methods,
            cc.total_methods,
            cc.coverage_percent()
        );
    }

    if total_methods > 0 {
        let pct = (total_covered as f64) * 100.0 / (total_methods as f64);
        println!(
            "\nTOTAL: {}/{} public methods covered ({:.2}%)",
            total_covered, total_methods, pct
        );
    } else {
        println!("\nTOTAL: no public methods defined in public_api.yml");
    }
}

This is intentionally “simple”:

It only uses function name and count.

It assumes method name extraction based on ::.

It relies on your public_api.yml to define “public”.


If you later want to feed in Clang’s JSON AST or bear/clangd outputs, you can refine split_type_method or add a richer mapping.


---

6. CLI tool: src/bin/smh_coverage.rs

This binary wires everything together.

use std::path::PathBuf;

use anyhow::Result;
use clap::Parser;
use simple_mock_helper::coverage::{
    compute_class_coverage, load_llvm_cov_export, load_public_api_spec,
    print_class_coverage_table,
};

/// CLI for "simple_mock_helper" coverage utilities.
///
/// Example:
///   smh_coverage \
///     --coverage-json target/coverage/export.json \
///     --public-api public_api.yml \
///     --type-filter MyNamespace::Foo
#[derive(Debug, Parser)]
#[command(name = "smh_coverage")]
#[command(about = "Compute class/struct public-method coverage from llvm-cov export JSON.")]
struct Args {
    /// Path to llvm-cov export JSON
    #[arg(long)]
    coverage_json: PathBuf,

    /// Path to public API YAML description
    #[arg(long)]
    public_api: PathBuf,

    /// Optional substring filter on type name
    #[arg(long)]
    type_filter: Option<String>,
}

fn main() -> Result<()> {
    let args = Args::parse();

    let cov = load_llvm_cov_export(&args.coverage_json)?;
    let api = load_public_api_spec(&args.public_api)?;

    let results = compute_class_coverage(&cov, &api);
    print_class_coverage_table(&results, args.type_filter.as_deref());

    Ok(())
}

You can install this binary into your PATH via cargo install --path . or just run it with cargo run.


---

7. Example: mock wrapper usage (unchanged)

Your existing mocks just use mock_policy as before. Example:

// In your application crate, depending on simple_mock_helper
// Cargo.toml
// [dependencies]
// simple_mock_helper = { path = "../simple_mock_helper" }
// mockall = "0.11"

use simple_mock_helper::mock_policy;
use mockall::*;

/// Example HAL trait
pub trait Gpio {
    fn set_high(&mut self);
    fn set_low(&mut self);
}

mock! {
    pub GpioMockImpl {}

    impl Gpio for GpioMockImpl {
        fn set_high(&mut self);
        fn set_low(&mut self);
    }
}

#[derive(Debug)]
pub struct GpioMock {
    inner: GpioMockImpl,
}

impl GpioMock {
    pub fn new() -> Self {
        mock_policy::check_mock_use_from(module_path!());
        Self {
            inner: GpioMockImpl::new(),
        }
    }
}

impl Gpio for GpioMock {
    fn set_high(&mut self) {
        mock_policy::check_mock_use_from(module_path!());
        self.inner.set_high()
    }

    fn set_low(&mut self) {
        mock_policy::check_mock_use_from(module_path!());
        self.inner.set_low()
    }
}


---

8. Usage document (ready-to-paste markdown)

You can paste this into simple_mock_helper/README.md or a doc in your main repo.

# simple_mock_helper

`simple_mock_helper` provides:

1. A **mock policy** library to control where mocks are allowed (unit / integration / system).
2. A **coverage tool** to derive class/struct public-method coverage from LLVM coverage (`llvm-cov export -format=json`) and a simple `public_api.yml`.

---

## 1. Mock policy

### 1.1 API

```rust
use simple_mock_helper::mock_policy;

pub const DEFAULT_HAL_PATTERNS: &[&str] = &["*::hal::*", "*::sub_hal::*"];

pub fn init_mocks_for_only(patterns: &'static [&'static str]);
pub fn init_mocks_for_only_default();
pub fn init_mocks_for_system();
pub fn check_mock_use_from(source_path: &str);

Patterns are checked against module_path!().

* is a wildcard.

Default policy (init_mocks_for_only_default) allows only modules containing ::hal:: or ::sub_hal::.


1.2 Typical structure

We usually split tests into three binaries:

src/
  lib.rs
tests/
  integration/
    mod.rs
    ...
  system/
    mod.rs
    ...

Unit tests (cargo test --lib): configured in src/lib.rs

Integration tests (cargo test --test integration): configured in tests/integration/mod.rs

System tests (cargo test --test system): configured in tests/system/mod.rs


Unit test policy (src/lib.rs)

#[cfg(test)]
mod unit_test_init {
    use simple_mock_helper::mock_policy;

    #[ctor::ctor]
    fn init_mock_policy() {
        // Example: allow mocks everywhere in unit tests
        mock_policy::init_mocks_for_only(&["*"]);
        // Or: HAL-only in unit tests as well
        // mock_policy::init_mocks_for_only_default();
    }
}

Integration tests (HAL-only) – tests/integration/mod.rs

use simple_mock_helper::mock_policy;

#[ctor::ctor]
fn init_mock_policy() {
    // Only ::hal:: / ::sub_hal:: mocks are permitted in this binary
    mock_policy::init_mocks_for_only_default();
}

mod case_gpio;
mod case_spi;

System tests (no mocks) – tests/system/mod.rs

use simple_mock_helper::mock_policy;

#[ctor::ctor]
fn init_mock_policy() {
    // Any mock usage in this binary is a test failure
    mock_policy::init_mocks_for_system();
}

mod full_stack;

Mock implementation example

use simple_mock_helper::mock_policy;
use mockall::*;

pub trait Gpio {
    fn set_high(&mut self);
    fn set_low(&mut self);
}

mock! {
    pub GpioMockImpl {}
    impl Gpio for GpioMockImpl {
        fn set_high(&mut self);
        fn set_low(&mut self);
    }
}

pub struct GpioMock {
    inner: GpioMockImpl,
}

impl GpioMock {
    pub fn new() -> Self {
        mock_policy::check_mock_use_from(module_path!());
        Self { inner: GpioMockImpl::new() }
    }
}

impl Gpio for GpioMock {
    fn set_high(&mut self) {
        mock_policy::check_mock_use_from(module_path!());
        self.inner.set_high()
    }

    fn set_low(&mut self) {
        mock_policy::check_mock_use_from(module_path!());
        self.inner.set_low()
    }
}


---

2. Class/struct public-method coverage

simple_mock_helper::coverage turns LLVM coverage JSON into per-class public-method coverage.

2.1 Data inputs

1. LLVM coverage JSON from llvm-cov export:

# merge *.profraw
llvm-profdata merge -sparse build/*.profraw -o default.profdata

# export coverage for your test binary
llvm-cov export \
  -format=json \
  -instr-profile=default.profdata \
  ./your_test_binary \
  > coverage.json


2. Public API spec in YAML (what you consider "public"):

# public_api.yml
types:
  MyNamespace::Foo:
    methods: [do_stuff, reset]
  Bar:
    methods:
      - run
      - stop



2.2 Library API

use simple_mock_helper::coverage::{
    load_llvm_cov_export,
    load_public_api_spec,
    compute_class_coverage,
    print_class_coverage_table,
};

Example:

let cov = load_llvm_cov_export("coverage.json")?;
let api = load_public_api_spec("public_api.yml")?;

let results = compute_class_coverage(&cov, &api);
print_class_coverage_table(&results, None);

2.3 CLI tool: smh_coverage

Build and run:

cargo run --bin smh_coverage -- \
  --coverage-json coverage.json \
  --public-api public_api.yml

Optional filter by type name substring:

cargo run --bin smh_coverage -- \
  --coverage-json coverage.json \
  --public-api public_api.yml \
  --type-filter MyNamespace::Foo

Sample output:

Type                                               Covered     Total   Percent
MyNamespace::Foo                                   2 / 3      66.67%
Bar                                                1 / 2      50.00%

TOTAL: 3/5 public methods covered (60.00%)

2.4 Matching logic

LLVM coverage functions are taken from data[*].functions[*].name.

Names are expected to look like:

Namespace::Type::method

Type::method


A function is considered covered if its count > 0.

It is mapped to (type_name, method_name) by splitting on the last ::.

A public method (type_name, method_name) is considered covered if any function with that pair has count > 0.



---

3. Integration with existing coverage

simple_mock_helper does not replace your existing coverage reports:

You still use llvm-profdata + llvm-cov for normal HTML / line / branch coverage.

smh_coverage is an extra step that converts the same coverage data into:

Per-type “public API coverage”.

An overall metric: covered_public_methods / total_public_methods.



You can wire it into CI as an additional check, for example:

llvm-profdata merge -sparse build/*.profraw -o default.profdata
llvm-cov export -format=json -instr-profile=default.profdata ./tests_bin > coverage.json

cargo run -p simple_mock_helper --bin smh_coverage -- \
  --coverage-json coverage.json \
  --public-api public_api.yml

You can then parse its output or add thresholds (e.g. “fail if < 80% public-method coverage”).

---

If you want, we can next add:

- A JSON output mode for `smh_coverage` so CI can parse it programmatically.
- An option to auto-generate a skeletal `public_api.yml` from the coverage JSON (list all discovered `Type::method` pairs so you can review and mark which are “public”).0
