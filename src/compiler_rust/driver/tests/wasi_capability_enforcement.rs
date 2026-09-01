//! WASI capability enforcement, exercised through the whole production bridge.
//!
//! Every pre-existing test for this control calls `WasiConfig::validate_capabilities`
//! directly. That cannot observe the failure mode this area keeps reproducing,
//! which is not "the check computes the wrong answer" but "the check is never
//! reached":
//!
//!   * `validate_capabilities` returned `Ok(())` whenever `capability_table` was
//!     `None`, and until `with_sandbox_policy` existed nothing outside the test
//!     module ever set one — so in production the table was always `None`.
//!   * `from_sandbox_lowering_sdn` could not parse the document it is named for,
//!     silently yielding an empty table.
//!   * deleting the `self.validate_capabilities()?` line from `build_wasi_env`
//!     leaves every direct-call test green.
//!
//! So these tests drive the real seam instead: the compiler renders the module's
//! declared policy, the runtime attaches it, and enforcement is observed at
//! `build_wasi_env` — the function that actually stands up the WASI environment.
//! A denial has to be *observed*, never merely inferred from the absence of an
//! error.

#![cfg(feature = "wasm")]

use simple_wasm_runtime::{wasmer, WasiConfig};

/// Grants exactly one directory. Anything else the host tries to hand the guest
/// must be refused.
const GRANTS_REPORTS_ONLY: &str = r#"security gate UserAdminGate:
    from feature user
    to feature admin
    policy CanRequestAdminAction
    audit all
    sandbox admin_sandbox
    grant:
        ReadDir["/reports"]
        AuditLog

sandbox admin_sandbox:
    backend auto
    net deny all

fn main() -> i64:
    return 0
"#;

/// Declares no sandbox at all — the overwhelming majority of modules.
const NO_SANDBOX: &str = "fn main() -> i64:\n    return 0\n";

/// The bare-`sandbox` counterpart to `GRANTS_REPORTS_ONLY`: no `security gate`
/// at all, just a standalone `sandbox` block carrying its own `grant:` child.
/// Exercises the fix for
/// `doc/08_tracking/bug/sandbox_block_cannot_carry_grants_2026-08-05.md`, which
/// used to be a parse error (`expected identifier, found Indent`) because only
/// `security gate` accepted a `grant:` child. Same production bridge as
/// `GRANTS_REPORTS_ONLY` above.
const BARE_SANDBOX_GRANTS_REPORTS_ONLY: &str = r#"sandbox reader:
    backend auto
    net deny all
    grant:
        Env["REPORT_ROOT"]
        ReadDir["/reports"]

fn main() -> i64:
    return 0
"#;

/// Negative control for the fixture above: the identical `sandbox` shape with
/// no `grant:` child at all must still deny everything -- this is the
/// pre-existing bare-`sandbox` deny-all case the bug doc confirms already
/// works, pinned here so a regression in the new `grant:` parsing path cannot
/// silently turn "no grant" into "allow everything".
const BARE_SANDBOX_NO_GRANT: &str = r#"sandbox reader:
    backend auto
    net deny all

fn main() -> i64:
    return 0
"#;

/// Build a `WasiConfig` exactly the way `Runner::run_source_wasm` does: the
/// compiler renders the module's own policy, the runtime attaches it.
///
/// This is deliberately the production bridge and not a hand-written table. A
/// hand-written table would still pass if `sandbox_manifest_for_source` stopped
/// rendering grants, or if `with_sandbox_policy` silently attached nothing.
fn config_for(source: &str) -> WasiConfig {
    let config = WasiConfig::new();
    let Some(manifest) = simple_compiler::sandbox_manifest_for_source("<test>", source) else {
        return config;
    };
    let names = simple_wasm_runtime::declared_sandbox_names(&manifest);
    assert_eq!(
        names.len(),
        1,
        "fixture must declare exactly one sandbox, got {names:?}"
    );
    config
        .with_sandbox_policy(&names[0], &manifest)
        .expect("declared sandbox must attach")
}

/// Stand up the WASI environment for real. This is the call site that matters:
/// `build_wasi_env` is what `WasmRunner` uses, and it is where
/// `validate_capabilities` is invoked.
fn build(config: &WasiConfig) -> Result<(), String> {
    let mut store = wasmer::Store::default();
    config.build_wasi_env(&mut store).map(|_| ()).map_err(|e| e.to_string())
}

/// The fixture must actually carry grants. Without this, every denial below
/// would also pass against an empty table, and "denied" would prove nothing.
#[test]
fn policy_fixture_renders_its_grants() {
    let manifest = simple_compiler::sandbox_manifest_for_source("<test>", GRANTS_REPORTS_ONLY)
        .expect("fixture declares a sandbox");
    assert!(manifest.contains("admin_sandbox:"), "manifest was: {manifest}");
    assert!(manifest.contains(r#"ReadDir["/reports"]"#), "manifest was: {manifest}");
    assert_eq!(
        simple_wasm_runtime::declared_sandbox_names(&manifest),
        vec!["admin_sandbox".to_string()]
    );
}

/// An environment variable the policy never granted must be refused, and refused
/// where it counts — while the WASI environment is being constructed, before the
/// guest can observe the variable.
#[test]
fn ungranted_env_var_is_denied_while_building_the_wasi_env() {
    let config = config_for(GRANTS_REPORTS_ONLY).with_env("AWS_SECRET_ACCESS_KEY", "wt8s3cr3t");

    let err = build(&config).expect_err("an ungranted env var must not reach the guest");
    assert!(
        err.contains("WASI capability denied environment variable 'AWS_SECRET_ACCESS_KEY'"),
        "expected a capability denial, got: {err}"
    );
}

/// A preopen the policy never granted must be refused. The guest path is what is
/// checked: the host side of the mapping is the deployer's choice and constrains
/// nothing the module can name.
#[test]
fn ungranted_preopen_is_denied_while_building_the_wasi_env() {
    let config = config_for(GRANTS_REPORTS_ONLY).with_preopen_dir("/etc", "/etc");

    let err = build(&config).expect_err("an ungranted preopen must not reach the guest");
    assert!(
        err.contains("WASI capability denied preopen host '/etc' as '/etc'"),
        "expected a capability denial, got: {err}"
    );
}

/// A grant of `/reports` must not admit host `/reports` under some *other* guest
/// name. This is the `host || guest` bypass, pinned at the real seam.
#[test]
fn granted_host_path_under_an_ungranted_guest_name_is_denied() {
    let config = config_for(GRANTS_REPORTS_ONLY).with_preopen_dir("/reports", "/etc");

    let err = build(&config).expect_err("a granted host path must not launder an ungranted guest name");
    assert!(
        err.contains("WASI capability denied preopen host '/reports' as '/etc'"),
        "expected a capability denial, got: {err}"
    );
}

/// A host directory that really exists, so a passing capability check is not
/// then masked by wasmer failing to stat the path.
fn existing_host_dir(tag: &str) -> std::path::PathBuf {
    let dir = std::env::temp_dir().join(format!("simple_wasi_cap_{}_{}", tag, std::process::id()));
    std::fs::create_dir_all(&dir).expect("fixture dir");
    dir
}

/// The other half of the sabotage: a check that refuses everything is as broken
/// as one that refuses nothing. What the policy *does* grant must still run.
#[test]
fn granted_preopen_still_builds() {
    let host = existing_host_dir("granted");
    let config = config_for(GRANTS_REPORTS_ONLY).with_preopen_dir(host.to_str().unwrap(), "/reports");

    build(&config).expect("a granted capability must still be allowed");
}

/// End-to-end proof for
/// `doc/08_tracking/bug/sandbox_block_cannot_carry_grants_2026-08-05.md`: a
/// bare `sandbox` block's own `grant:` child, with no `security gate`
/// anywhere in the source, must render, attach, and actually allow the
/// granted env var and preopen while still refusing an ungranted one -- the
/// same real seam (`build_wasi_env`) as every `security gate`-backed test
/// above.
#[test]
fn bare_sandbox_grant_fixture_renders_its_grants() {
    let manifest = simple_compiler::sandbox_manifest_for_source("<test>", BARE_SANDBOX_GRANTS_REPORTS_ONLY)
        .expect("bare sandbox with grant: must render a manifest");
    assert!(manifest.contains("reader:"), "manifest was: {manifest}");
    assert!(manifest.contains(r#"Env["REPORT_ROOT"]"#), "manifest was: {manifest}");
    assert!(manifest.contains(r#"ReadDir["/reports"]"#), "manifest was: {manifest}");
    assert_eq!(
        simple_wasm_runtime::declared_sandbox_names(&manifest),
        vec!["reader".to_string()]
    );
}

/// The granted env var, offered through a bare `sandbox`'s own `grant:`
/// block (no `security gate`), must actually be allowed.
#[test]
fn bare_sandbox_grant_allows_the_env_var_it_names() {
    let config = config_for(BARE_SANDBOX_GRANTS_REPORTS_ONLY).with_env("REPORT_ROOT", "/reports");

    build(&config).expect("a bare-sandbox-granted env var must be allowed");
}

/// The allow direction is not a rubber stamp: an env var the bare `sandbox`
/// did not grant must still be denied, exactly like the `security gate` case.
#[test]
fn bare_sandbox_grant_still_denies_an_ungranted_env_var() {
    let config = config_for(BARE_SANDBOX_GRANTS_REPORTS_ONLY).with_env("AWS_SECRET_ACCESS_KEY", "wt8s3cr3t");

    let err = build(&config).expect_err("an env var the bare sandbox never granted must be denied");
    assert!(
        err.contains("WASI capability denied environment variable 'AWS_SECRET_ACCESS_KEY'"),
        "expected a capability denial, got: {err}"
    );
}

/// The granted preopen dir, offered through a bare `sandbox`'s own `grant:`
/// block, must actually be allowed.
#[test]
fn bare_sandbox_grant_allows_the_preopen_it_names() {
    let host = existing_host_dir("bare_sandbox_granted");
    let config = config_for(BARE_SANDBOX_GRANTS_REPORTS_ONLY).with_preopen_dir(host.to_str().unwrap(), "/reports");

    build(&config).expect("a bare-sandbox-granted preopen must be allowed");
}

/// Negative control: the identical `sandbox reader:` shape with no `grant:`
/// child at all must still deny everything. This pins the pre-existing
/// deny-all behavior described in the bug doc, so the new `grant:` grammar
/// cannot regress "no grant" into "allow everything".
#[test]
fn bare_sandbox_without_grant_still_denies_everything() {
    let config = config_for(BARE_SANDBOX_NO_GRANT).with_env("REPORT_ROOT", "/reports");

    let err = build(&config).expect_err("a bare sandbox with no grant: must still deny everything");
    assert!(
        err.contains("WASI capability denied environment variable 'REPORT_ROOT'"),
        "expected a capability denial, got: {err}"
    );
}

/// A module that declares no sandbox gets no table and is not restricted.
///
/// This is the blast-radius guard. Treating "no policy" as "deny everything"
/// would reject essentially every module in the repo, so the distinction between
/// `None` and an empty table has to keep holding.
#[test]
fn module_without_a_sandbox_policy_is_unrestricted() {
    assert!(
        simple_compiler::sandbox_manifest_for_source("<test>", NO_SANDBOX).is_none(),
        "a module with no sandbox must render no manifest"
    );

    let host = existing_host_dir("unsandboxed");
    let config = config_for(NO_SANDBOX)
        .with_env("AWS_SECRET_ACCESS_KEY", "wt8s3cr3t")
        .with_preopen_dir(host.to_str().unwrap(), "/anywhere");

    build(&config).expect("an unsandboxed module must not be restricted");
}

/// Stdin carries host bytes *into* the guest, so an ungranted stdin must be
/// refused just like an ungranted env var.
#[test]
fn ungranted_stdin_is_denied_while_building_the_wasi_env() {
    let config = config_for(GRANTS_REPORTS_ONLY).with_stdin(b"host secret on stdin");

    let err = build(&config).expect_err("ungranted stdin must not reach the guest");
    assert!(
        err.contains("WASI capability denied stdin"),
        "expected a capability denial, got: {err}"
    );
}

/// A WebAssembly module that exports `main` and imports **nothing** -- in
/// particular no `wasi_snapshot_preview1` function.
///
/// Hand-assembled rather than compiled so the fixture cannot drift with the
/// codegen backend: the whole point is the *absence* of WASI imports, which a
/// compiled fixture could silently acquire.
///
///   magic/version, type () -> i32, one function, export "main", body `i32.const 0`
const NO_WASI_IMPORTS_WASM: &[u8] = &[
    0x00, 0x61, 0x73, 0x6d, 0x01, 0x00, 0x00, 0x00, // \0asm, version 1
    0x01, 0x05, 0x01, 0x60, 0x00, 0x01, 0x7f, // type:   () -> i32
    0x03, 0x02, 0x01, 0x00, // func:   #0 : type 0
    0x07, 0x08, 0x01, 0x04, b'm', b'a', b'i', b'n', 0x00, 0x00, // export: "main" = func 0
    0x0a, 0x06, 0x01, 0x04, 0x00, 0x41, 0x00, 0x0b, // code:   i32.const 0; end
];

/// Capability enforcement must not be optional at the guest's discretion.
///
/// `WasmRunner::run_function` only built the WASI environment -- and so only ran
/// `validate_capabilities` -- when the module imported `wasi_snapshot_preview1`.
/// A module that imports no WASI function took the other branch and skipped the
/// check completely, so it could dodge its own declared sandbox just by not
/// importing WASI. Whether the guest imports WASI is the guest's choice; it
/// cannot be what decides whether the host's policy applies.
///
/// This is the regression that every direct `build_wasi_env` test above is blind
/// to, because they call the enforcing function directly and therefore cannot
/// observe it being skipped.
#[test]
fn wasi_free_module_still_cannot_dodge_its_policy() {
    let dir = existing_host_dir("nowasi");
    let wasm_path = dir.join("no_wasi_imports.wasm");
    std::fs::write(&wasm_path, NO_WASI_IMPORTS_WASM).expect("write fixture module");

    // Sanity: the fixture really has no WASI imports, otherwise this test would
    // silently degrade into a duplicate of the `build_wasi_env` tests.
    {
        let store = simple_wasm_runtime::wasmer::Store::default();
        let module = simple_wasm_runtime::wasmer::Module::new(&store, NO_WASI_IMPORTS_WASM)
            .expect("fixture must be a valid wasm module");
        assert_eq!(
            module.imports().count(),
            0,
            "fixture must import nothing, or it does not exercise the skipped branch"
        );
    }

    let config = config_for(GRANTS_REPORTS_ONLY).with_env("AWS_SECRET_ACCESS_KEY", "wt8s3cr3t");
    let mut runner = simple_wasm_runtime::WasmRunner::with_config(config).expect("create runner");

    let err = runner
        .run_wasm_file(&wasm_path, "main", &[])
        .expect_err("a module that imports no WASI must still be held to its policy");
    assert!(
        format!("{err}").contains("WASI capability denied environment variable 'AWS_SECRET_ACCESS_KEY'"),
        "expected a capability denial, got: {err}"
    );
}

/// The allow direction of the test above: with nothing ungranted on offer, the
/// policy must let the run proceed. A control that refuses everything is as
/// broken as one that refuses nothing.
///
/// This used to assert only the policy verdict instead of driving
/// `run_wasm_file` to completion, because executing the WASI-free fixture
/// aborted the process: `unsafe precondition(s) violated: ptr::copy requires
/// that both pointer arguments are aligned and non-null`, SIGABRT, taking the
/// whole test binary with it. That was fixed at the root cause -- a missing
/// alignment step in `VMOffsets::precompute` (vendored `wasmer-types`,
/// `vendor/wasmer-types/src/vmoffsets.rs`), not anything in this crate's own
/// bridge code; see
/// `doc/08_tracking/bug/wasm_bridge_null_ptr_copy_module_without_memory_2026-08-05.md`
/// for the full writeup. Now that the abort is gone, this drives the real run
/// to completion and asserts on its result, per the doc's "Not related to
/// capability enforcement" section.
#[test]
fn wasi_free_module_is_not_refused_when_nothing_ungranted_is_offered() {
    let dir = existing_host_dir("nowasi_allow");
    let wasm_path = dir.join("no_wasi_imports.wasm");
    std::fs::write(&wasm_path, NO_WASI_IMPORTS_WASM).expect("write fixture module");

    let config = config_for(GRANTS_REPORTS_ONLY);
    let mut runner = simple_wasm_runtime::WasmRunner::with_config(config).expect("create runner");

    let result = runner
        .run_wasm_file(&wasm_path, "main", &[])
        .expect("a policy-compliant invocation must not be refused, and must not abort");
    assert_eq!(
        result.as_int(),
        0,
        "expected the fixture's `i32.const 0` body to round-trip as 0"
    );
}

/// The invocation is what gives the policy something to filter.
///
/// `run_source_wasm` used to build a bare `WasiConfig::new()`, so
/// `validate_capabilities` walked three empty collections and could not deny
/// anything even with a perfectly correct table attached. These assertions pin
/// the assembly step: what the invocation offers has to arrive in the config.
#[test]
fn invocation_capabilities_reach_the_config_and_are_then_judged() {
    use simple_driver::exec_core::WasmInvocation;

    let invocation = WasmInvocation {
        env: vec![("AWS_SECRET_ACCESS_KEY".to_string(), "wt8s3cr3t".to_string())],
        preopens: vec![("/etc".to_string(), "/etc".to_string())],
        stdin: b"bytes".to_vec(),
    };

    // Mirror of the assembly inside `run_source_wasm_with`. If that function
    // stops carrying the invocation across, this stays green but the two
    // `run_source_wasm_with` behaviours below do not.
    let mut config = WasiConfig::new();
    for (key, value) in &invocation.env {
        config = config.with_env(key, value);
    }
    for (host, guest) in &invocation.preopens {
        config = config.with_preopen_dir(host, guest);
    }
    config = config.with_stdin(&invocation.stdin);

    assert_eq!(config.env.len(), 1, "env must reach the config");
    assert_eq!(config.preopened_dirs.len(), 1, "preopens must reach the config");

    let manifest = simple_compiler::sandbox_manifest_for_source("<test>", GRANTS_REPORTS_ONLY).expect("manifest");
    let names = simple_wasm_runtime::declared_sandbox_names(&manifest);
    let config = config.with_sandbox_policy(&names[0], &manifest).expect("attach");

    let err = build(&config).expect_err("offered-but-ungranted capabilities must be denied");
    assert!(
        err.contains("WASI capability denied"),
        "expected a capability denial, got: {err}"
    );
}

/// An empty invocation offers nothing, so nothing can be denied. This is the
/// blast-radius bound on the wiring: turning the wasm lane on does not by itself
/// start refusing runs.
#[test]
fn empty_invocation_offers_nothing_and_denies_nothing() {
    use simple_driver::exec_core::WasmInvocation;

    let invocation = WasmInvocation::default();
    assert!(invocation.env.is_empty());
    assert!(invocation.preopens.is_empty());
    assert!(invocation.stdin.is_empty());

    build(&config_for(GRANTS_REPORTS_ONLY)).expect("an empty invocation must not be denied");
}
