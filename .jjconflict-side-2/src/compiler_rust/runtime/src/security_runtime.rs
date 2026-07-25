//! Runtime entry points for compiler-generated security gate advice.

use std::collections::{HashMap, HashSet};
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{Mutex, OnceLock};

static ENTER_GATE_COUNT: AtomicU64 = AtomicU64::new(0);
static EXIT_GATE_COUNT: AtomicU64 = AtomicU64::new(0);
static REQUIRE_POLICY_COUNT: AtomicU64 = AtomicU64::new(0);
static ENTER_SANDBOX_COUNT: AtomicU64 = AtomicU64::new(0);
static EXIT_SANDBOX_COUNT: AtomicU64 = AtomicU64::new(0);
static AUDIT_START_COUNT: AtomicU64 = AtomicU64::new(0);
static AUDIT_SUCCESS_COUNT: AtomicU64 = AtomicU64::new(0);
static AUDIT_FAILURE_COUNT: AtomicU64 = AtomicU64::new(0);
static LAST_GATE_ID: AtomicU64 = AtomicU64::new(0);
static LAST_POLICY_ID: AtomicU64 = AtomicU64::new(0);
static LAST_SANDBOX_ID: AtomicU64 = AtomicU64::new(0);
static LAST_AUDIT_ID: AtomicU64 = AtomicU64::new(0);
static LAST_POLICY_ALLOWED: AtomicU64 = AtomicU64::new(1);
static LAST_SANDBOX_REGISTERED: AtomicU64 = AtomicU64::new(0);
static LAST_SANDBOX_BACKEND_ID: AtomicU64 = AtomicU64::new(0);
static LAST_SANDBOX_CAPABILITY_HANDLES: AtomicU64 = AtomicU64::new(0);
static LAST_SANDBOX_CAPABILITY_ALLOWED: AtomicU64 = AtomicU64::new(1);
static SANDBOX_CAPABILITY_DENIAL_COUNT: AtomicU64 = AtomicU64::new(0);
static LAST_HOST_IMPORT_ALLOWED: AtomicU64 = AtomicU64::new(1);
static HOST_IMPORT_DENIAL_COUNT: AtomicU64 = AtomicU64::new(0);
static LOADED_REGISTRY_ENTRIES: AtomicU64 = AtomicU64::new(0);

#[derive(Default)]
struct SecurityRegistry {
    denied_policies: HashSet<u64>,
    registered_sandboxes: HashSet<u64>,
    sandbox_lowerings: HashMap<u64, SandboxLoweringRecord>,
    active_sandboxes: Vec<u64>,
}

#[derive(Default)]
struct SandboxLoweringRecord {
    backend_id: u64,
    capability_handles: u64,
    capability_handle_ids: HashSet<u64>,
    denied_capability_ids: HashSet<u64>,
}

fn registry() -> &'static Mutex<SecurityRegistry> {
    static REGISTRY: OnceLock<Mutex<SecurityRegistry>> = OnceLock::new();
    REGISTRY.get_or_init(|| Mutex::new(SecurityRegistry::default()))
}

fn security_metadata_id(value: &str) -> u64 {
    let mut hash = 0xcbf29ce484222325_u64;
    for byte in value.as_bytes() {
        hash ^= u64::from(*byte);
        hash = hash.wrapping_mul(0x100000001b3);
    }
    hash
}

fn capability_alias_ids(name: &str) -> Vec<u64> {
    let normalized = name.trim();
    let mut aliases = vec![security_metadata_id(normalized)];
    let expanded = match normalized {
        "net" | "network" => Some("Network"),
        "fs" | "filesystem" => Some("Filesystem"),
        "env" | "environment" => Some("Env"),
        "process" | "proc" => Some("Process"),
        "syscall" => Some("Syscall"),
        _ => None,
    };
    if let Some(alias) = expanded {
        aliases.push(security_metadata_id(alias));
    }
    aliases
}

fn capability_handle_id(handle: &str) -> u64 {
    let trimmed = handle.trim();
    let name = trimmed.split(['[', '(', '<', ' ']).next().unwrap_or(trimmed);
    security_metadata_id(name)
}

fn host_import_capability_id(name: &str) -> Option<u64> {
    match name {
        "rt_file_read_text"
        | "rt_file_read_text_rv"
        | "rt_file_canonicalize"
        | "rt_file_exists"
        | "rt_file_size"
        | "rt_file_mtime"
        | "rt_file_read_bytes"
        | "rt_file_read_lines"
        | "rt_file_hash_sha256"
        | "rt_file_mmap_read_text"
        | "rt_file_mmap_read_text_rv"
        | "rt_file_mmap_read_bytes"
        | "rt_file_mmap_read_bytes_rv"
        | "rt_file_mmap_len"
        | "rt_file_read_text_at"
        | "rt_read_file"
        | "doctest_read_file"
        | "doctest_path_exists"
        | "doctest_is_file"
        | "doctest_is_dir"
        | "doctest_walk_directory"
        | "doctest_path_has_extension"
        | "doctest_path_contains" => Some(security_metadata_id("ReadFile")),
        "rt_file_write_text"
        | "rt_file_write_text_rv"
        | "rt_file_append_text"
        | "rt_file_fsync"
        | "rt_file_fsync_cached"
        | "rt_file_copy"
        | "rt_file_move"
        | "rt_file_remove"
        | "rt_file_rename"
        | "rt_file_write_bytes"
        | "rt_file_write_text_at"
        | "rt_file_write_text_at_cached"
        | "rt_file_write_text_at_cached_repeat"
        | "rt_write_file"
        | "rt_remove_file"
        | "rt_create_dir"
        | "rt_remove_dir"
        | "rt_rename"
        | "rt_package_create_tarball"
        | "rt_package_extract_tarball"
        | "rt_package_copy_file"
        | "rt_package_mkdir_all"
        | "rt_package_remove_dir_all"
        | "rt_package_create_symlink"
        | "rt_package_chmod" => Some(security_metadata_id("WriteFile")),
        _ if name.starts_with("rt_env_") || name == "env_get" || name == "rt_env_get" => {
            Some(security_metadata_id("Env"))
        }
        _ if name.starts_with("rt_process_")
            || name.starts_with("rt_pty_")
            || name == "process_run"
            || name == "rt_exec"
            || name == "rt_execute_native" =>
        {
            Some(security_metadata_id("Process"))
        }
        _ if name.starts_with("native_tcp_")
            || name.starts_with("native_udp_")
            || name.starts_with("rt_io_tcp_")
            || name.starts_with("rt_http_")
            || name.starts_with("rt_dns_")
            || name.starts_with("rt_tls_")
            || name.starts_with("rt_monoio_tcp_")
            || name.starts_with("rt_monoio_udp_")
            || name.starts_with("monoio_tcp_")
            || name.starts_with("monoio_udp_")
            || name.starts_with("rt_unix_socket_")
            || name == "rt_host_wm_client_connect" =>
        {
            Some(security_metadata_id("Network"))
        }
        _ => None,
    }
}

fn is_security_control_plane_import(name: &str) -> bool {
    name.starts_with("rt_security_")
}

fn active_sandbox_backend_id() -> Option<u64> {
    registry().lock().ok().and_then(|registry| {
        let sandbox_id = registry.active_sandboxes.last()?;
        registry
            .sandbox_lowerings
            .get(sandbox_id)
            .map(|record| record.backend_id)
    })
}

fn active_sandbox_is_simple_vm() -> bool {
    active_sandbox_backend_id() == Some(security_metadata_id("simple_vm_capability_table"))
}

#[no_mangle]
pub extern "C" fn rt_security_enter_gate(gate_id: u64) {
    LAST_GATE_ID.store(gate_id, Ordering::Relaxed);
    ENTER_GATE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_exit_gate(gate_id: u64) {
    LAST_GATE_ID.store(gate_id, Ordering::Relaxed);
    EXIT_GATE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_require_policy(policy_id: u64) {
    LAST_POLICY_ID.store(policy_id, Ordering::Relaxed);
    let allowed = registry()
        .lock()
        .map(|registry| !registry.denied_policies.contains(&policy_id))
        .unwrap_or(true);
    LAST_POLICY_ALLOWED.store(u64::from(allowed), Ordering::Relaxed);
    REQUIRE_POLICY_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_enter_sandbox(sandbox_id: u64) {
    LAST_SANDBOX_ID.store(sandbox_id, Ordering::Relaxed);
    let (registered, backend_id, capability_handles) = registry()
        .lock()
        .map(|mut registry| {
            let registered = registry.registered_sandboxes.contains(&sandbox_id)
                || registry.sandbox_lowerings.contains_key(&sandbox_id);
            let lowering = registry.sandbox_lowerings.get(&sandbox_id);
            let result = (
                registered,
                lowering.map(|record| record.backend_id).unwrap_or(0),
                lowering.map(|record| record.capability_handles).unwrap_or(0),
            );
            if registered {
                registry.active_sandboxes.push(sandbox_id);
            }
            result
        })
        .unwrap_or((false, 0, 0));
    LAST_SANDBOX_REGISTERED.store(u64::from(registered), Ordering::Relaxed);
    LAST_SANDBOX_BACKEND_ID.store(backend_id, Ordering::Relaxed);
    LAST_SANDBOX_CAPABILITY_HANDLES.store(capability_handles, Ordering::Relaxed);
    ENTER_SANDBOX_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_exit_sandbox(sandbox_id: u64) {
    LAST_SANDBOX_ID.store(sandbox_id, Ordering::Relaxed);
    if let Ok(mut registry) = registry().lock() {
        if let Some(index) = registry.active_sandboxes.iter().rposition(|id| *id == sandbox_id) {
            registry.active_sandboxes.remove(index);
        }
    }
    EXIT_SANDBOX_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_audit_start(gate_id: u64, audit_id: u64) {
    LAST_GATE_ID.store(gate_id, Ordering::Relaxed);
    LAST_AUDIT_ID.store(audit_id, Ordering::Relaxed);
    AUDIT_START_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_audit_success(gate_id: u64) {
    LAST_GATE_ID.store(gate_id, Ordering::Relaxed);
    AUDIT_SUCCESS_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_audit_failure(gate_id: u64) {
    LAST_GATE_ID.store(gate_id, Ordering::Relaxed);
    AUDIT_FAILURE_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[no_mangle]
pub extern "C" fn rt_security_reset_counters() {
    ENTER_GATE_COUNT.store(0, Ordering::Relaxed);
    EXIT_GATE_COUNT.store(0, Ordering::Relaxed);
    REQUIRE_POLICY_COUNT.store(0, Ordering::Relaxed);
    ENTER_SANDBOX_COUNT.store(0, Ordering::Relaxed);
    EXIT_SANDBOX_COUNT.store(0, Ordering::Relaxed);
    AUDIT_START_COUNT.store(0, Ordering::Relaxed);
    AUDIT_SUCCESS_COUNT.store(0, Ordering::Relaxed);
    AUDIT_FAILURE_COUNT.store(0, Ordering::Relaxed);
    LAST_GATE_ID.store(0, Ordering::Relaxed);
    LAST_POLICY_ID.store(0, Ordering::Relaxed);
    LAST_SANDBOX_ID.store(0, Ordering::Relaxed);
    LAST_AUDIT_ID.store(0, Ordering::Relaxed);
    LAST_POLICY_ALLOWED.store(1, Ordering::Relaxed);
    LAST_SANDBOX_REGISTERED.store(0, Ordering::Relaxed);
    LAST_SANDBOX_BACKEND_ID.store(0, Ordering::Relaxed);
    LAST_SANDBOX_CAPABILITY_HANDLES.store(0, Ordering::Relaxed);
    LAST_SANDBOX_CAPABILITY_ALLOWED.store(1, Ordering::Relaxed);
    SANDBOX_CAPABILITY_DENIAL_COUNT.store(0, Ordering::Relaxed);
    LAST_HOST_IMPORT_ALLOWED.store(1, Ordering::Relaxed);
    HOST_IMPORT_DENIAL_COUNT.store(0, Ordering::Relaxed);
    LOADED_REGISTRY_ENTRIES.store(0, Ordering::Relaxed);
    if let Ok(mut registry) = registry().lock() {
        *registry = SecurityRegistry::default();
    }
}

#[no_mangle]
pub extern "C" fn rt_security_gate_depth() -> u64 {
    ENTER_GATE_COUNT
        .load(Ordering::Relaxed)
        .saturating_sub(EXIT_GATE_COUNT.load(Ordering::Relaxed))
}

#[no_mangle]
pub extern "C" fn rt_security_policy_checks() -> u64 {
    REQUIRE_POLICY_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_audit_events() -> u64 {
    AUDIT_START_COUNT.load(Ordering::Relaxed)
        + AUDIT_SUCCESS_COUNT.load(Ordering::Relaxed)
        + AUDIT_FAILURE_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_last_gate_id() -> u64 {
    LAST_GATE_ID.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_last_policy_id() -> u64 {
    LAST_POLICY_ID.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_last_sandbox_id() -> u64 {
    LAST_SANDBOX_ID.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_last_audit_id() -> u64 {
    LAST_AUDIT_ID.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_register_policy(policy_id: u64, allowed: bool) {
    if let Ok(mut registry) = registry().lock() {
        if allowed {
            registry.denied_policies.remove(&policy_id);
        } else {
            registry.denied_policies.insert(policy_id);
        }
    }
}

#[no_mangle]
pub extern "C" fn rt_security_policy_allowed() -> bool {
    LAST_POLICY_ALLOWED.load(Ordering::Relaxed) != 0
}

#[no_mangle]
pub extern "C" fn rt_security_register_sandbox(sandbox_id: u64) {
    if let Ok(mut registry) = registry().lock() {
        registry.registered_sandboxes.insert(sandbox_id);
    }
}

#[no_mangle]
pub extern "C" fn rt_security_sandbox_registered() -> bool {
    LAST_SANDBOX_REGISTERED.load(Ordering::Relaxed) != 0
}

#[no_mangle]
pub extern "C" fn rt_security_last_sandbox_backend_id() -> u64 {
    LAST_SANDBOX_BACKEND_ID.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_last_sandbox_capability_handles() -> u64 {
    LAST_SANDBOX_CAPABILITY_HANDLES.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_sandbox_capability_allowed(capability_id: u64) -> bool {
    let allowed = registry()
        .lock()
        .map(|registry| {
            let Some(sandbox_id) = registry.active_sandboxes.last() else {
                return true;
            };
            let Some(lowering) = registry.sandbox_lowerings.get(sandbox_id) else {
                return true;
            };
            if lowering.denied_capability_ids.contains(&capability_id) {
                return false;
            }
            lowering.capability_handle_ids.is_empty() || lowering.capability_handle_ids.contains(&capability_id)
        })
        .unwrap_or(true);
    LAST_SANDBOX_CAPABILITY_ALLOWED.store(u64::from(allowed), Ordering::Relaxed);
    if !allowed {
        SANDBOX_CAPABILITY_DENIAL_COUNT.fetch_add(1, Ordering::Relaxed);
    }
    allowed
}

#[no_mangle]
pub extern "C" fn rt_security_last_sandbox_capability_allowed() -> bool {
    LAST_SANDBOX_CAPABILITY_ALLOWED.load(Ordering::Relaxed) != 0
}

#[no_mangle]
pub extern "C" fn rt_security_sandbox_capability_denials() -> u64 {
    SANDBOX_CAPABILITY_DENIAL_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_host_import_allowed(name_ptr: *const u8, name_len: u64) -> bool {
    if name_ptr.is_null() {
        LAST_HOST_IMPORT_ALLOWED.store(0, Ordering::Relaxed);
        HOST_IMPORT_DENIAL_COUNT.fetch_add(1, Ordering::Relaxed);
        return false;
    }
    let bytes = unsafe { std::slice::from_raw_parts(name_ptr, name_len as usize) };
    let Ok(name) = std::str::from_utf8(bytes) else {
        LAST_HOST_IMPORT_ALLOWED.store(0, Ordering::Relaxed);
        HOST_IMPORT_DENIAL_COUNT.fetch_add(1, Ordering::Relaxed);
        return false;
    };
    let allowed = match host_import_capability_id(name) {
        Some(capability_id) => rt_security_sandbox_capability_allowed(capability_id),
        None if active_sandbox_is_simple_vm() => is_security_control_plane_import(name),
        None => true,
    };
    LAST_HOST_IMPORT_ALLOWED.store(u64::from(allowed), Ordering::Relaxed);
    if !allowed {
        HOST_IMPORT_DENIAL_COUNT.fetch_add(1, Ordering::Relaxed);
    }
    allowed
}

#[no_mangle]
pub extern "C" fn rt_security_last_host_import_allowed() -> bool {
    LAST_HOST_IMPORT_ALLOWED.load(Ordering::Relaxed) != 0
}

#[no_mangle]
pub extern "C" fn rt_security_host_import_denials() -> u64 {
    HOST_IMPORT_DENIAL_COUNT.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_loaded_registry_entries() -> u64 {
    LOADED_REGISTRY_ENTRIES.load(Ordering::Relaxed)
}

#[no_mangle]
pub extern "C" fn rt_security_load_registry_sdn(ptr: *const u8, len: u64) -> u64 {
    if ptr.is_null() || len == 0 {
        return 0;
    }
    let bytes = unsafe { std::slice::from_raw_parts(ptr, len as usize) };
    let Ok(text) = std::str::from_utf8(bytes) else {
        return 0;
    };
    let loaded = load_registry_sdn_text(text);
    LOADED_REGISTRY_ENTRIES.fetch_add(loaded, Ordering::Relaxed);
    loaded
}

fn load_registry_sdn_text(text: &str) -> u64 {
    let mut loaded = 0_u64;
    let mut pending_kind = None;
    let mut pending_name: Option<&str> = None;
    let mut in_sandbox_lowering = false;
    let mut current_sandbox: Option<&str> = None;
    let mut current_backend: Option<&str> = None;
    let mut capability_handles = 0_u64;
    let mut capability_handle_ids = HashSet::new();
    let mut denied_capability_ids = HashSet::new();
    let mut in_capability_handles = false;
    let mut in_policy_rules = false;

    for line in text.lines() {
        let trimmed = line.trim();
        if trimmed == "sandbox_lowering:" {
            loaded += flush_sandbox_lowering(
                current_sandbox.take(),
                current_backend.take(),
                capability_handles,
                std::mem::take(&mut capability_handle_ids),
                std::mem::take(&mut denied_capability_ids),
            );
            capability_handles = 0;
            in_capability_handles = false;
            in_policy_rules = false;
            in_sandbox_lowering = true;
            pending_kind = None;
            pending_name = None;
            continue;
        }
        if in_sandbox_lowering {
            if trimmed.is_empty() || trimmed.starts_with('#') {
                continue;
            }
            if line.starts_with("  ") && !line.starts_with("    ") && trimmed.ends_with(':') {
                loaded += flush_sandbox_lowering(
                    current_sandbox.take(),
                    current_backend.take(),
                    capability_handles,
                    std::mem::take(&mut capability_handle_ids),
                    std::mem::take(&mut denied_capability_ids),
                );
                capability_handles = 0;
                in_capability_handles = false;
                in_policy_rules = false;
                current_sandbox = Some(trimmed.trim_end_matches(':'));
                continue;
            }
            if let Some(backend) = trimmed.strip_prefix("lowered_backend:") {
                current_backend = Some(backend.trim());
                in_capability_handles = false;
                in_policy_rules = false;
                continue;
            }
            if trimmed == "capability_handles:" {
                in_capability_handles = true;
                in_policy_rules = false;
                continue;
            }
            if trimmed == "policy_rules:" {
                in_policy_rules = true;
                in_capability_handles = false;
                continue;
            }
            if in_capability_handles && trimmed.starts_with("- ") && current_sandbox.is_some() {
                capability_handles += 1;
                capability_handle_ids.insert(capability_handle_id(trimmed.trim_start_matches("- ")));
                continue;
            }
            if in_policy_rules && current_sandbox.is_some() {
                if let Some((key, value)) = trimmed.split_once(':') {
                    if value.trim().starts_with("deny") {
                        for alias_id in capability_alias_ids(key) {
                            denied_capability_ids.insert(alias_id);
                        }
                    }
                }
                continue;
            }
            if !line.starts_with(' ') {
                loaded += flush_sandbox_lowering(
                    current_sandbox.take(),
                    current_backend.take(),
                    capability_handles,
                    std::mem::take(&mut capability_handle_ids),
                    std::mem::take(&mut denied_capability_ids),
                );
                capability_handles = 0;
                in_capability_handles = false;
                in_policy_rules = false;
                in_sandbox_lowering = false;
            }
        }
        if let Some(name) = trimmed.strip_prefix("- require_policy:") {
            pending_kind = Some("policy");
            pending_name = Some(name.trim());
            continue;
        }
        if let Some(name) = trimmed.strip_prefix("- enter_sandbox:") {
            pending_kind = Some("sandbox");
            pending_name = Some(name.trim());
            continue;
        }

        let Some(id_text) = trimmed.strip_prefix("id:") else {
            continue;
        };
        let parsed_id = id_text.trim().parse::<u64>().ok();
        let id = parsed_id
            .or_else(|| pending_name.map(security_metadata_id))
            .unwrap_or(0);
        if id == 0 {
            pending_kind = None;
            pending_name = None;
            continue;
        }

        match pending_kind {
            Some("policy") => {
                rt_security_register_policy(id, true);
                loaded += 1;
            }
            Some("sandbox") => {
                rt_security_register_sandbox(id);
                loaded += 1;
            }
            _ => {}
        }
        pending_kind = None;
        pending_name = None;
    }

    loaded += flush_sandbox_lowering(
        current_sandbox,
        current_backend,
        capability_handles,
        capability_handle_ids,
        denied_capability_ids,
    );
    loaded
}

fn flush_sandbox_lowering(
    sandbox_name: Option<&str>,
    backend_name: Option<&str>,
    capability_handles: u64,
    capability_handle_ids: HashSet<u64>,
    denied_capability_ids: HashSet<u64>,
) -> u64 {
    let Some(sandbox_name) = sandbox_name else {
        return 0;
    };
    let Some(backend_name) = backend_name else {
        return 0;
    };
    let sandbox_id = security_metadata_id(sandbox_name);
    let backend_id = security_metadata_id(backend_name);
    if let Ok(mut registry) = registry().lock() {
        registry.registered_sandboxes.insert(sandbox_id);
        registry.sandbox_lowerings.insert(
            sandbox_id,
            SandboxLoweringRecord {
                backend_id,
                capability_handles,
                capability_handle_ids,
                denied_capability_ids,
            },
        );
    }
    1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tracks_security_gate_runtime_counters() {
        rt_security_reset_counters();
        rt_security_register_policy(22, true);
        rt_security_register_sandbox(33);
        rt_security_enter_gate(11);
        rt_security_require_policy(22);
        rt_security_enter_sandbox(33);
        rt_security_audit_start(11, 44);
        rt_security_audit_success(11);
        assert_eq!(rt_security_gate_depth(), 1);
        assert_eq!(rt_security_policy_checks(), 1);
        assert_eq!(rt_security_audit_events(), 2);
        assert_eq!(rt_security_last_gate_id(), 11);
        assert_eq!(rt_security_last_policy_id(), 22);
        assert_eq!(rt_security_last_sandbox_id(), 33);
        assert_eq!(rt_security_last_audit_id(), 44);
        assert!(rt_security_policy_allowed());
        assert!(rt_security_sandbox_registered());

        rt_security_exit_sandbox(33);
        rt_security_exit_gate(11);
        assert_eq!(rt_security_gate_depth(), 0);
    }

    #[test]
    fn policy_registry_can_deny_policy_id() {
        rt_security_reset_counters();
        rt_security_register_policy(77, false);
        rt_security_require_policy(77);
        assert!(!rt_security_policy_allowed());
    }

    #[test]
    fn loads_generated_registry_entries_from_security_aop_sdn() {
        rt_security_reset_counters();
        let policy_id = security_metadata_id("CanRequestAdminAction");
        let sandbox_id = security_metadata_id("admin_sandbox");
        let manifest = format!(
            "security_aop_lowering:\n  advice_plans:\n    - gate: UserAdminGate\n      steps:\n        - require_policy: CanRequestAdminAction\n          id: {}\n        - enter_sandbox: admin_sandbox\n          id: {}\n",
            policy_id, sandbox_id
        );

        let loaded = rt_security_load_registry_sdn(manifest.as_ptr(), manifest.len() as u64);
        assert_eq!(loaded, 2);
        assert_eq!(rt_security_loaded_registry_entries(), 2);
        rt_security_require_policy(policy_id);
        assert!(rt_security_policy_allowed());
        rt_security_enter_sandbox(sandbox_id);
        assert!(rt_security_sandbox_registered());
    }

    #[test]
    fn loads_sandbox_lowering_metadata_into_runtime_registry() {
        rt_security_reset_counters();
        let sandbox_id = security_metadata_id("admin_sandbox");
        let backend_id = security_metadata_id("linux_landlock_seccomp_namespaces");
        let manifest = "\
sandbox_lowering:
  admin_sandbox:
    source_backend: auto
    lowered_backend: linux_landlock_seccomp_namespaces
    enforcement:
      - landlock_ruleset
    capability_handles:
      - ReadDir[\"/reports\"]
      - AuditLog
";

        let loaded = rt_security_load_registry_sdn(manifest.as_ptr(), manifest.len() as u64);
        assert_eq!(loaded, 1);
        assert_eq!(rt_security_loaded_registry_entries(), 1);
        rt_security_enter_sandbox(sandbox_id);
        assert!(rt_security_sandbox_registered());
        assert_eq!(rt_security_last_sandbox_backend_id(), backend_id);
        assert_eq!(rt_security_last_sandbox_capability_handles(), 2);
    }

    #[test]
    fn active_sandbox_enforces_lowered_capability_handles() {
        rt_security_reset_counters();
        let sandbox_id = security_metadata_id("plugin_sandbox");
        let read_dir_id = security_metadata_id("ReadDir");
        let network_id = security_metadata_id("Network");
        let manifest = "\
sandbox_lowering:
  plugin_sandbox:
    source_backend: simple_os
    lowered_backend: simple_os_native_object_capability_handles
    enforcement:
      - native_object_capability_handles
      - handle_transfer_table
      - kernel_rights_mask
    capability_handles:
      - ReadDir[\"/reports\"]
      - AuditLog
    policy_rules:
      net: deny all
";

        assert_eq!(
            rt_security_load_registry_sdn(manifest.as_ptr(), manifest.len() as u64),
            1
        );
        assert!(rt_security_sandbox_capability_allowed(network_id));
        rt_security_enter_sandbox(sandbox_id);
        assert!(rt_security_sandbox_capability_allowed(read_dir_id));
        assert!(!rt_security_sandbox_capability_allowed(network_id));
        assert!(!rt_security_last_sandbox_capability_allowed());
        assert_eq!(rt_security_sandbox_capability_denials(), 1);
        rt_security_exit_sandbox(sandbox_id);
        assert!(rt_security_sandbox_capability_allowed(network_id));
    }

    #[test]
    fn active_sandbox_filters_vm_host_imports_by_capability_class() {
        rt_security_reset_counters();
        let sandbox_id = security_metadata_id("vm_plugin");
        let manifest = "\
sandbox_lowering:
  vm_plugin:
    source_backend: simple_vm
    lowered_backend: simple_vm_capability_table
    enforcement:
      - module_capability_table
      - host_import_filter
    capability_handles:
      - ReadFile[\"/reports/input.txt\"]
      - AuditLog
    policy_rules:
      net: deny all
      process: deny all
      env: deny all
";

        assert_eq!(
            rt_security_load_registry_sdn(manifest.as_ptr(), manifest.len() as u64),
            1
        );
        rt_security_enter_sandbox(sandbox_id);

        assert!(rt_security_host_import_allowed(
            b"rt_file_read_text".as_ptr(),
            "rt_file_read_text".len() as u64
        ));
        assert!(!rt_security_host_import_allowed(
            b"rt_file_write_text".as_ptr(),
            "rt_file_write_text".len() as u64
        ));
        assert!(!rt_security_host_import_allowed(
            b"rt_http_get".as_ptr(),
            "rt_http_get".len() as u64
        ));
        assert!(!rt_security_host_import_allowed(
            b"rt_process_run".as_ptr(),
            "rt_process_run".len() as u64
        ));
        assert!(!rt_security_host_import_allowed(
            b"rt_env_get".as_ptr(),
            "rt_env_get".len() as u64
        ));
        assert!(!rt_security_last_host_import_allowed());
        assert!(!rt_security_host_import_allowed(
            b"rt_plugin_custom_host_call".as_ptr(),
            "rt_plugin_custom_host_call".len() as u64
        ));
        assert!(rt_security_host_import_allowed(
            b"rt_security_enter_gate".as_ptr(),
            "rt_security_enter_gate".len() as u64
        ));
        assert_eq!(rt_security_host_import_denials(), 5);
    }

    #[test]
    fn write_only_vm_host_import_filter_denies_read_imports() {
        rt_security_reset_counters();
        let sandbox_id = security_metadata_id("writer_plugin");
        let manifest = "\
sandbox_lowering:
  writer_plugin:
    source_backend: simple_vm
    lowered_backend: simple_vm_capability_table
    enforcement:
      - module_capability_table
      - host_import_filter
    capability_handles:
      - WriteFile[\"/reports/output.txt\"]
";

        assert_eq!(
            rt_security_load_registry_sdn(manifest.as_ptr(), manifest.len() as u64),
            1
        );
        rt_security_enter_sandbox(sandbox_id);
        assert!(rt_security_host_import_allowed(
            b"rt_file_write_text".as_ptr(),
            "rt_file_write_text".len() as u64
        ));
        assert!(!rt_security_host_import_allowed(
            b"rt_file_read_text".as_ptr(),
            "rt_file_read_text".len() as u64
        ));
    }
}
