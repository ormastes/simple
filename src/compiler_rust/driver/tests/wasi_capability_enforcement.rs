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
    assert_eq!(names.len(), 1, "fixture must declare exactly one sandbox, got {names:?}");
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
    let manifest =
        simple_compiler::sandbox_manifest_for_source("<test>", GRANTS_REPORTS_ONLY).expect("fixture declares a sandbox");
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
