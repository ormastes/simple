use std::path::{Path, PathBuf};

use simple_common::target::TargetOS;

use crate::linker::error::{LinkerError, LinkerResult};

use super::builder::NativeBinaryBuilder;
use super::options::{compile_c_args, detect_c_compiler, detect_nm_command, is_msvc_compiler};

/// Symbols in the extra_keep allowlist used for both pass-1 and pass-2 stub generation.
const EXTRA_KEEP: &[&str] = &[
    "BackendPort",
    "BlockResolver",
    "AopWeaver",
    "CodegenPipeline",
    "CompilerBackendImpl",
    "DiContainer",
    "compile_module_with_backend",
    "Scope",
    "ScopeId",
    "SymbolTable",
    "LogAspect",
    "NativeLinkOptions",
    "visibilitychecker_new",
    "VisibilityWarning.new",
    "with_resolved_blocks",
    "write_elf_bytes_to_file",
    "HirLowering",
    "desugar_module",
    "optimize_mir_module",
    "process_async_mir",
    "get_effective_backend_name",
    "resolve_methods",
    "link_to_native",
    "link_llvm_native",
    "link_to_smf",
    "link_to_self_contained",
    "run_monomorphization",
    "run_effect_pass",
    "run_compile",
    "generate_cmake_for_modules",
    "SmfHeader.new_v1_1",
    "new",
    "create",
    "from_function",
    "aggressive",
    "eval_static_assert",
    "int",
    "preprocess_conditionals",
    "load_path",
    "join_path",
    "is_absolute_path",
    "for_arch",
    "host",
    "parse",
    "parse_leak_dump",
    "symbols_get",
    "size",
    "speed",
    "RUNTIME_SYMBOL_NAMES.contains",
    "checker_check_symbol_access",
    "checker_get_warnings",
    "checker_record_warning",
    "simple_contract_check",
    "simple_contract_check_msg",
    "fallback",
    "doctest_is_dir",
    "doctest_is_file",
    "doctest_path_contains",
    "doctest_path_exists",
    "doctest_path_has_extension",
    "doctest_read_file",
    "doctest_walk_directory",
    "ffi_regex_is_match",
    "ffi_regex_find",
    "ffi_regex_find_all",
    "ffi_regex_captures",
    "ffi_regex_replace",
    "ffi_regex_replace_all",
    "ffi_regex_split",
    "ffi_regex_split_n",
    "native_http_send",
    "native_tcp_accept",
    "native_tcp_bind",
    "native_tcp_close",
    "native_tcp_connect",
    "native_tcp_connect_timeout",
    "native_tcp_flush",
    "native_tcp_get_nodelay",
    "native_tcp_peek",
    "native_tcp_read",
    "native_tcp_set_backlog",
    "native_tcp_set_keepalive",
    "native_tcp_set_nodelay",
    "native_tcp_set_read_timeout",
    "native_tcp_set_write_timeout",
    "native_tcp_shutdown",
    "native_tcp_write",
    "native_udp_bind",
    "native_udp_close",
    "native_udp_connect",
    "native_udp_get_broadcast",
    "native_udp_get_ttl",
    "native_udp_join_multicast_v4",
    "native_udp_join_multicast_v6",
    "native_udp_leave_multicast_v4",
    "native_udp_leave_multicast_v6",
    "native_udp_peek",
    "native_udp_peek_from",
    "native_udp_peer_addr",
    "native_udp_recv",
    "native_udp_recv_from",
    "native_udp_send",
    "native_udp_send_to",
    "native_udp_set_broadcast",
    "native_udp_set_multicast_loop",
    "native_udp_set_multicast_ttl",
    "native_udp_set_read_timeout",
    "native_udp_set_ttl",
    "native_udp_set_write_timeout",
];

const RT_KEEP: &[&str] = &[
    "rt_time_now_nanos",
    "rt_time_now_micros",
    "rt_time_now_unix_micros",
    "rt_file_mmap_read_text",
    "rt_file_mmap_read_bytes",
    "rt_file_read_text_at",
    "rt_file_read_bytes_at",
    "rt_file_write_text_at",
    "rt_file_write_bytes_at",
    "rt_mmap",
    "rt_mmap_raw",
    "rt_munmap",
    "rt_munmap_raw",
    "rt_madvise",
    "rt_msync",
    "rt_process_spawn_async",
    "rt_process_wait",
    "rt_process_is_running",
    "rt_process_kill",
    "rt_hostname",
    "rt_volatile_read_u8",
    "rt_volatile_read_u16",
    "rt_volatile_read_u32",
    "rt_volatile_read_u64",
    "rt_volatile_write_u8",
    "rt_volatile_write_u16",
    "rt_volatile_write_u32",
    "rt_volatile_write_u64",
    "rt_memory_barrier",
    "rt_load_barrier",
    "rt_store_barrier",
    "panic",
    "future_alloc_ready",
    "future_map",
    "future_then",
    "rt_io_file_open",
    "rt_io_file_read",
    "rt_io_file_read_all",
    "rt_io_file_read_line",
    "rt_bytes_to_text",
    "rt_io_file_write",
    "rt_io_file_write_all",
    "rt_io_file_flush",
    "rt_io_file_seek",
    "rt_io_file_close",
    "rt_io_file_metadata",
    "rt_io_file_set_permissions",
    "rt_io_file_exists",
    "rt_io_file_delete",
    "rt_io_tcp_bind",
    "rt_io_tcp_accept",
    "rt_io_tcp_accept_timeout",
    "rt_io_tcp_connect",
    "rt_io_tcp_connect_timeout",
    "rt_io_tcp_read",
    "rt_io_tcp_read_line",
    "rt_io_tcp_write",
    "rt_io_tcp_flush",
    "rt_io_tcp_close",
    "rt_io_tcp_local_addr",
    "rt_io_tcp_peer_addr",
    "rt_io_tcp_set_nodelay",
    "rt_io_tcp_set_read_timeout",
    "rt_io_tcp_set_write_timeout",
    "rt_io_tcp_shutdown",
    "rt_io_udp_bind",
    "rt_io_udp_recv_from",
    "rt_io_udp_send_to",
    "rt_io_udp_connect",
    "rt_io_udp_send",
    "rt_io_udp_recv",
    "rt_io_udp_local_addr",
    "rt_io_udp_set_broadcast",
    "rt_io_udp_set_read_timeout",
    "rt_io_udp_close",
    "rt_epoll_create",
    "rt_epoll_ctl",
    "rt_epoll_wait",
    "rt_socket_set_nonblocking",
    "rt_stdin_read",
    "rt_stdin_read_all",
    "rt_stdin_read_line",
    "rt_stdout_write",
    "rt_stdout_flush",
    "rt_stderr_write",
    "rt_stderr_flush",
    "acquire",
    "empty",
    "defaults",
    "mem_enable",
    "mem_snapshot",
    "mem_disable",
    "mem_dump_leaks",
    "mem_live_count",
    "mem_live_bytes",
    "mem_reset",
    "rt_text_to_bytes",
    "rt_fault_set_stack_overflow_detection",
    "rt_fault_set_timeout",
    "rt_fault_set_execution_limit",
    "rt_debug_set_active",
    "rt_debug_enable",
    "rt_debug_disable",
    "rt_file_rename",
    "rt_file_write",
    "rt_file_delete",
    "rt_file_size",
    "rt_file_lock",
    "rt_file_unlock",
    "rt_getpid",
    "rt_compile_to_llvm_ir",
    "rt_file_hash_sha256",
    "rt_path_parent",
    "range",
];

/// Generate C source code for symbol stubs given a set of symbol names.
fn gen_stub_code(
    symbols: &std::collections::BTreeSet<String>,
    use_strong: bool,
    target_os: TargetOS,
    ret_insn: &str,
) -> String {
    let attr = if use_strong { "" } else { "__attribute__((weak)) " };
    let mut code = String::from("#include <stdint.h>\n#include <stdbool.h>\n");
    for sym in symbols {
        let is_data = sym.contains("GLOBAL_") || sym.contains("SCOPE_");
        let valid_ident = sym.chars().all(|c| c.is_ascii_alphanumeric() || c == '_') && sym != "int";
        if is_data && valid_ident {
            code.push_str(&format!("{1}int64_t {0} = 0;\n", sym, attr));
        } else if valid_ident {
            code.push_str(&format!("{1}int64_t {0}(void) {{ return 0; }}\n", sym, attr));
        } else if matches!(target_os, TargetOS::FreeBSD) {
            let clean = sym.replace('\"', "");
            code.push_str(&format!(
                "__asm__(\".globl {0}\\n{0}:\\n  {1}\\n\");\n",
                clean, ret_insn
            ));
        } else if !use_strong {
            let clean = sym.replace('\"', "");
            #[cfg(target_os = "macos")]
            code.push_str(&format!(
                "__asm__(\".weak_definition _{0}\\n_{0}:\\n  {1}\\n\");\n",
                clean, ret_insn
            ));
            #[cfg(any(target_os = "linux", target_os = "freebsd"))]
            code.push_str(&format!("__asm__(\".weak {0}\\n{0}:\\n  {1}\\n\");\n", clean, ret_insn));
            #[cfg(target_os = "windows")]
            code.push_str(&format!("__attribute__((weak)) void {0}(void) {{}}\n", clean));
        }
    }
    code
}

impl NativeBinaryBuilder {
    /// Build the main shim (C `main()` → `spl_main()`) and add to stubs list.
    pub(super) fn build_main_shim(&self, temp_path: &Path, bootstrap_stubs: &mut Vec<PathBuf>) -> LinkerResult<()> {
        let cc = detect_c_compiler(&self.options.target);
        let stub_c = temp_path.join("_main_shim.c");
        let stub_o = temp_path.join("_main_shim.o");
        std::fs::write(
            &stub_c,
            r#"
extern int spl_main(void);
extern void rt_set_args(int argc, char** argv);
int main(int argc, char** argv) {
    rt_set_args(argc, argv);
    return spl_main();
}
"#,
        )
        .map_err(|e| LinkerError::LinkFailed(format!("failed to write main shim: {}", e)))?;
        let status = std::process::Command::new(&cc)
            .args(compile_c_args(&cc, &stub_o, &stub_c))
            .status()
            .map_err(|e| LinkerError::LinkFailed(format!("failed to compile main shim: {}", e)))?;
        if status.success() {
            bootstrap_stubs.push(stub_o);
        } else {
            eprintln!("warning: failed to build main shim with {} (status {})", cc, status);
        }
        Ok(())
    }

    /// Build pass-1 bootstrap stubs: common missing-symbol stub + auto-generated stubs from obj.
    pub(super) fn build_pass1_stubs(
        &self,
        temp_path: &Path,
        obj_path: &Path,
        ret_insn: &str,
        bootstrap_stubs: &mut Vec<PathBuf>,
    ) -> LinkerResult<()> {
        let cc = detect_c_compiler(&self.options.target);
        let use_strong = matches!(self.options.target.os, TargetOS::Windows | TargetOS::FreeBSD);

        // 2) common missing-symbol stub
        self.build_missing_sym_stub(temp_path, &cc, use_strong, ret_insn, bootstrap_stubs)?;

        // 3) auto-generate stubs from obj symbols
        self.build_auto_stubs_from_obj(
            temp_path,
            obj_path,
            &cc,
            use_strong,
            ret_insn,
            bootstrap_stubs,
            "_bootstrap_auto.c",
            "_bootstrap_auto.o",
        )?;

        Ok(())
    }

    fn build_missing_sym_stub(
        &self,
        temp_path: &Path,
        cc: &str,
        use_strong: bool,
        ret_insn: &str,
        bootstrap_stubs: &mut Vec<PathBuf>,
    ) -> LinkerResult<()> {
        let miss_c = temp_path.join("_bootstrap_missing.c");
        let miss_o = temp_path.join("_bootstrap_missing.o");
        let weak_attr = if use_strong { "" } else { "__attribute__((weak)) " };
        let weak_vis = if use_strong {
            ""
        } else {
            "__attribute__((weak, visibility(\"default\"))) "
        };
        let asm_section = if matches!(self.options.target.os, TargetOS::FreeBSD) {
            format!(
                "__asm__(\".globl SCOPE_LEVELS.contains_key\\nSCOPE_LEVELS.contains_key:\\n  {ret_insn}\\n\");\n",
                ret_insn = ret_insn
            )
        } else if use_strong {
            String::new()
        } else {
            format!(
                "#ifdef __APPLE__\n__asm__(\".weak_definition _SCOPE_LEVELS.contains_key\\n_SCOPE_LEVELS.contains_key:\\n  {ret_insn}\\n\");\n#else\n__asm__(\".weak SCOPE_LEVELS.contains_key\\nSCOPE_LEVELS.contains_key:\\n  {ret_insn}\\n\");\n#endif\n",
                ret_insn = ret_insn
            )
        };
        std::fs::write(
            &miss_c,
            format!(
                r#"
#include <stdint.h>
#include <stdbool.h>
{w}int64_t get_global_GLOBAL_LOG_LEVEL(void) {{ return 0; }}
{w}void set_global_GLOBAL_LOG_LEVEL(int64_t v) {{ (void)v; }}
{w}bool rt_file_rename(const char* a, const char* b) {{ (void)a; (void)b; return true; }}
{w}void rt_fault_set_stack_overflow_detection(int64_t v) {{ (void)v; }}
{w}void rt_fault_set_timeout(int64_t v) {{ (void)v; }}
{w}void rt_fault_set_execution_limit(int64_t v) {{ (void)v; }}
{w}void rt_debug_set_active(int64_t v) {{ (void)v; }}
{w}void rt_debug_enable(void) {{}}
{w}void rt_debug_disable(void) {{}}
#if defined(_WIN32)
#include <windows.h>
static inline int64_t _rt_now_nanos(void) {{
    LARGE_INTEGER freq, count;
    if (!QueryPerformanceFrequency(&freq) || !QueryPerformanceCounter(&count)) return 0;
    return (int64_t)((double)count.QuadPart / (double)freq.QuadPart * 1000000000.0);
}}
#else
#include <time.h>
static inline int64_t _rt_now_nanos(void) {{
    struct timespec ts;
    if (clock_gettime(CLOCK_REALTIME, &ts) != 0) return 0;
    return (int64_t)ts.tv_sec * 1000000000LL + (int64_t)ts.tv_nsec;
}}
#endif
{w}int64_t rt_time_now_nanos(void) {{ return _rt_now_nanos(); }}
{w}int64_t rt_time_now_micros(void) {{ return _rt_now_nanos() / 1000; }}
{w}int64_t rt_time_now_unix_micros(void) {{ return _rt_now_nanos() / 1000; }}
{w}char* rt_hostname(void) {{ return (char*)""; }}
{wv}void* get_global_SCOPE_LEVELS(void) {{ return 0; }}
{wv}int64_t count_by_severity(void) {{ return 0; }}
{asm}
"#,
                w = weak_attr,
                wv = weak_vis,
                asm = asm_section
            ),
        )
        .map_err(|e| LinkerError::LinkFailed(format!("failed to write missing-symbol stub: {}", e)))?;
        let status = std::process::Command::new(cc)
            .args(compile_c_args(cc, &miss_o, &miss_c))
            .status()
            .map_err(|e| LinkerError::LinkFailed(format!("failed to compile missing-symbol stub: {}", e)))?;
        if status.success() {
            bootstrap_stubs.push(miss_o);
        } else {
            eprintln!(
                "warning: failed to build bootstrap missing-symbol stub with {} (status {})",
                cc, status
            );
        }
        Ok(())
    }

    fn build_auto_stubs_from_obj(
        &self,
        temp_path: &Path,
        obj_path: &Path,
        cc: &str,
        use_strong: bool,
        ret_insn: &str,
        bootstrap_stubs: &mut Vec<PathBuf>,
        c_name: &str,
        o_name: &str,
    ) -> LinkerResult<()> {
        let (nm_cmd, nm_args) = detect_nm_command(&self.options.target);
        let nm_out = match std::process::Command::new(&nm_cmd)
            .args(&nm_args)
            .arg(obj_path)
            .output()
        {
            Ok(o) => o,
            Err(_) => return Ok(()),
        };

        let mut symbols = std::collections::BTreeSet::new();
        for line in String::from_utf8_lossy(&nm_out.stdout).lines() {
            if let Some(sym) = line.split_whitespace().last() {
                if sym.len() >= 2 {
                    symbols.insert(sym.to_string());
                }
            }
        }

        if symbols.is_empty() {
            return Ok(());
        }

        let code = gen_stub_code(&symbols, use_strong, self.options.target.os, ret_insn);
        let auto_c = temp_path.join(c_name);
        let auto_o = temp_path.join(o_name);
        std::fs::write(&auto_c, code)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write auto stub: {}", e)))?;
        let status = std::process::Command::new(cc)
            .args(compile_c_args(cc, &auto_o, &auto_c))
            .status()
            .map_err(|e| LinkerError::LinkFailed(format!("failed to compile auto stub: {}", e)))?;
        if status.success() {
            bootstrap_stubs.push(auto_o);
        } else {
            eprintln!("warning: failed to build auto stub with {} (status {})", cc, status);
        }
        Ok(())
    }

    /// Build pass-2 stubs from first-pass binary undefined symbols.
    pub(super) fn build_pass2_stubs(
        &self,
        temp_path: &Path,
        first_out: &Path,
        ret_insn: &str,
        bootstrap_stubs: &mut Vec<PathBuf>,
    ) -> LinkerResult<()> {
        let (nm_cmd2, nm_args2) = detect_nm_command(&self.options.target);
        let nm_out = std::process::Command::new(&nm_cmd2)
            .args(&nm_args2)
            .arg(first_out)
            .output()
            .map_err(|e| LinkerError::LinkFailed(format!("failed to run {} on first-pass output: {}", nm_cmd2, e)))?;

        let mut symbols = std::collections::BTreeSet::new();
        for line in String::from_utf8_lossy(&nm_out.stdout).lines() {
            if let Some(sym) = line.split_whitespace().last() {
                if sym.len() >= 2 {
                    symbols.insert(sym.to_string());
                }
            }
        }

        if symbols.is_empty() {
            return Ok(());
        }

        let use_strong = matches!(self.options.target.os, TargetOS::Windows | TargetOS::FreeBSD);
        let code = gen_stub_code(&symbols, use_strong, self.options.target.os, ret_insn);
        let auto_c = temp_path.join("_bootstrap_auto2.c");
        let auto_o = temp_path.join("_bootstrap_auto2.o");
        std::fs::write(&auto_c, code)
            .map_err(|e| LinkerError::LinkFailed(format!("failed to write auto stub: {}", e)))?;
        let cc2 = detect_c_compiler(&self.options.target);
        let status = std::process::Command::new(&cc2)
            .args(compile_c_args(&cc2, &auto_o, &auto_c))
            .status()
            .map_err(|e| LinkerError::LinkFailed(format!("failed to compile auto stub: {}", e)))?;
        if status.success() {
            bootstrap_stubs.push(auto_o);
        } else {
            eprintln!(
                "warning: failed to build auto stub (second pass) with {} (status {})",
                cc2, status
            );
        }
        Ok(())
    }
}
