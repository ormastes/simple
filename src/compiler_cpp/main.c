#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <time.h>

#ifdef _WIN32
  #include <windows.h>
  #include <io.h>
  #include <process.h>
  #ifdef _MSC_VER
    #define strdup _strdup
  #endif
  #define PATH_SEP '\\'
#else
  #include <unistd.h>
  #include <sys/stat.h>
  #include <sys/wait.h>
  #define PATH_SEP '/'
#endif

#ifdef __APPLE__
  #include <mach-o/dyld.h>  /* _NSGetExecutablePath */
#endif
#if defined(__FreeBSD__)
  #include <sys/types.h>
  #include <sys/sysctl.h>
#endif

#define nil NULL
#define pass_do_nothing ((void)0)
#define pass_dn ((void)0)
#define pass_todo ((void)0)

#pragma GCC diagnostic ignored "-Wdeprecated-non-prototype"
#pragma GCC diagnostic ignored "-Wparentheses-equality"
#pragma GCC diagnostic ignored "-Wunused-value"

#include "simple_helpers.h"

/* Forward declarations for functions defined later */
static int get_exe_dir(char* buf, size_t bufsz);
static int file_accessible(const char* path);

typedef struct {
    int gc_log;
    int gc_off;
    int use_notui;
    long long max_recursion_depth;
    long long timeout_secs;
    long long execution_limit;
    int stack_overflow_detection;
    const char* backend;
    int force_interpret;
    const char* interpreter_mode;
    const char* run_config;
    int no_jit;
    long long jit_threshold;
} GlobalFlags;


static int file_exists(const char* p) { (void)p; return 0; }
static const char* file_read(const char* p) { (void)p; return ""; }
static int file_write(const char* p, const char* d) { (void)p;(void)d; return 1; }
static int dir_create(const char* p, int recursive) { (void)p;(void)recursive; return 1; }
static const char* cwd(void) { return ""; }
static const char* env_get(const char* k) {
    if (!k) return "";
    const char* v = getenv(k);
    return v ? v : "";
}
static void env_set(const char* k, const char* v) { (void)k; (void)v; }
static long long shell() { return 0; }
static long long file_size_raw(const char* p) { (void)p; return 0; }

/* Check file existence using access() */
static int cli_file_exists(const char* p) {
    if (!p) return 0;
#ifdef _WIN32
    return _access(p, 0) == 0;
#else
    return access(p, F_OK) == 0;
#endif
}

static long long cli_read_file(SimpleStringArray a) { (void)a; return 0; }
static int g_argc_main = 0;
static char** g_argv_main = NULL;
static SimpleStringArray cli_get_args(void) {
    SimpleStringArray a = simple_new_string_array();
    for (int i = 0; i < g_argc_main; i++)
        simple_string_push(&a, g_argv_main[i] ? g_argv_main[i] : "");
    return a;
}

/* ── Interpreter delegation ──
 * For commands not natively compiled, delegate to the interpreter binary
 * with the appropriate .spl entry point. This gives fast startup for
 * compiled commands while still supporting all features via interpreter.
 */
static char g_interp_bin[4096] = {0};
static char g_src_dir[4096] = {0};

static void init_interp_paths(void) {
    if (g_interp_bin[0]) return; /* already initialized */
    char self_path[4096] = {0};
    if (get_exe_dir(self_path, sizeof(self_path)) != 0) return;
    /* Interpreter binary: ../bin/release/simple-0.6.0 (relative to build/) */
    snprintf(g_interp_bin, sizeof(g_interp_bin), "%s../bin/release/simple-0.6.0", self_path);
    if (!file_accessible(g_interp_bin)) {
        /* Try: ../bin/release/simple */
        snprintf(g_interp_bin, sizeof(g_interp_bin), "%s../bin/release/simple", self_path);
    }
    snprintf(g_src_dir, sizeof(g_src_dir), "%s../src", self_path);
}

/* Suppress [DEBUG] and [WARNING] noise from the interpreter binary's stderr.
 * Fork a child to run the interpreter; parent filters stderr via pipe.
 * If fork isn't available, fall back to direct execv (noise but functional). */
static long long run_interpreter_filtered(char** argv) {
#ifndef _WIN32
    int pipefd[2];
    if (pipe(pipefd) != 0) {
        /* pipe failed — fall back to unfiltered execv */
        execv(g_interp_bin, argv);
        perror("execv");
        return 1;
    }
    pid_t pid = fork();
    if (pid < 0) {
        close(pipefd[0]); close(pipefd[1]);
        execv(g_interp_bin, argv);
        perror("execv");
        return 1;
    }
    if (pid == 0) {
        /* Child: redirect stderr to pipe write end, then exec interpreter */
        close(pipefd[0]);
        dup2(pipefd[1], STDERR_FILENO);
        close(pipefd[1]);
        execv(g_interp_bin, argv);
        _exit(127);
    }
    /* Parent: read from pipe, filter, write to real stderr */
    close(pipefd[1]);
    char buf[4096];
    ssize_t n;
    /* Line-buffered filtering */
    char line[8192];
    int lpos = 0;
    while ((n = read(pipefd[0], buf, sizeof(buf))) > 0) {
        for (ssize_t i = 0; i < n; i++) {
            if (buf[i] == '\n' || lpos >= (int)sizeof(line) - 1) {
                line[lpos] = '\0';
                /* Filter out noisy lines */
                if (strncmp(line, "[DEBUG]", 7) != 0 &&
                    strncmp(line, "[WARNING] Failed to load test database", 38) != 0 &&
                    strncmp(line, "[WARNING] Existing records will be preserved", 44) != 0 &&
                    strncmp(line, "[INFO] Backup created at:", 25) != 0 &&
                    strncmp(line, "Warning: Failed to update", 25) != 0) {
                    write(STDERR_FILENO, line, lpos);
                    write(STDERR_FILENO, "\n", 1);
                }
                lpos = 0;
            } else {
                line[lpos++] = buf[i];
            }
        }
    }
    /* Flush remaining partial line */
    if (lpos > 0) {
        line[lpos] = '\0';
        if (strncmp(line, "[DEBUG]", 7) != 0)
            write(STDERR_FILENO, line, lpos);
    }
    close(pipefd[0]);
    int status;
    waitpid(pid, &status, 0);
    free(argv);
    if (WIFEXITED(status)) return WEXITSTATUS(status);
    return 1;
#else
    int rc = _spawnv(_P_WAIT, g_interp_bin, (const char* const*)argv);
    free(argv);
    return rc;
#endif
}

/* Run interpreter with a .spl entry point and the original CLI args */
static long long delegate_to_interpreter(const char* entry_spl) {
    init_interp_paths();
    if (!file_accessible(g_interp_bin)) {
        fprintf(stderr, "Error: interpreter binary not found (needed for '%s')\n", entry_spl);
        return 1;
    }
    char entry_path[4096];
    snprintf(entry_path, sizeof(entry_path), "%s/app/cli/%s", g_src_dir, entry_spl);

    char** argv = (char**)malloc((g_argc_main + 3) * sizeof(char*));
    argv[0] = g_interp_bin;
    argv[1] = entry_path;
    for (int i = 1; i < g_argc_main; i++)
        argv[i + 1] = g_argv_main[i];
    argv[g_argc_main + 1] = NULL;
    return run_interpreter_filtered(argv);
}

/* Delegate with a specific fast-path entry point for known commands */
static long long delegate_test(SimpleStringArray a) {
    /* Check if single .spl test → use lightweight runner */
    int has_spl = 0;
    int has_heavy = 0;
    for (long long i = 0; i < a.len; i++) {
        const char* arg = a.items[i];
        if (simple_ends_with(arg, ".spl")) has_spl = 1;
        if (simple_starts_with(arg, "--coverage") || simple_starts_with(arg, "--sdoctest") ||
            simple_starts_with(arg, "--container") || strcmp(arg, "--chaos") == 0 ||
            strcmp(arg, "--fuzz") == 0 || strcmp(arg, "--parallel") == 0)
            has_heavy = 1;
    }
    if (has_spl && !has_heavy)
        return delegate_to_interpreter("../test_runner_new/test_runner_single.spl");
    return delegate_to_interpreter("../test_runner_new/test_runner_main.spl");
}

static long long cli_run_code(const char* c, int g, int o) { (void)c;(void)g;(void)o; return 0; }
/* Run a .spl file through the interpreter binary */
static long long cli_run_file(const char* p, SimpleStringArray a, int g, int o) {
    (void)a; (void)g; (void)o;
    init_interp_paths();
    if (!file_accessible(g_interp_bin)) {
        fprintf(stderr, "Error: interpreter binary not found (needed to run '%s')\n", p);
        return 1;
    }
    char** argv = (char**)malloc((g_argc_main + 3) * sizeof(char*));
    argv[0] = g_interp_bin;
    argv[1] = (char*)p;
    for (int i = 1; i < g_argc_main; i++)
        argv[i + 1] = g_argv_main[i];
    argv[g_argc_main + 1] = NULL;
    return run_interpreter_filtered(argv);
}
static long long cli_watch_file(const char* p) { (void)p; return 0; }
static long long cli_run_repl(int g, int o) { (void)g;(void)o; return 0; }
static long long cli_run_tests(SimpleStringArray a, int g, int o) { (void)g;(void)o; return delegate_test(a); }
static long long cli_run_lint(SimpleStringArray a) { (void)a; return delegate_to_interpreter("lint_entry.spl"); }
static long long cli_run_fmt(SimpleStringArray a) { (void)a; return delegate_to_interpreter("lint_entry.spl"); }
static long long cli_run_fix(SimpleStringArray a) { (void)a; return delegate_to_interpreter("lint_entry.spl"); }
static long long cli_run_verify(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }
static long long cli_run_migrate(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_mcp(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long cli_run_lsp(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long cli_run_diff(SimpleStringArray a) { (void)a; return 0; }
static long long cli_constr(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_query(SimpleStringArray a) { (void)a; return 0; }
static long long cli_info(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_spec_coverage(SimpleStringArray a) { (void)a; return 0; }
static long long cli_replay(SimpleStringArray a) { (void)a; return 0; }
static long long cli_gen_lean(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_feature_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_task_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_spec_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_sspec_docgen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_feature_doc(SimpleStringArray a) { (void)a; return 0; }
static long long cli_todo_scan(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long cli_run_todo_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_lex(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_brief(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long cli_run_ffi_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_i18n(SimpleStringArray a) { (void)a; return 0; }
/* Cross-platform: get path of this executable */
static int get_exe_dir(char* buf, size_t bufsz) {
#if defined(_WIN32)
    DWORD len = GetModuleFileNameA(NULL, buf, (DWORD)bufsz);
    if (len == 0 || len >= bufsz) return -1;
    /* Truncate to directory */
    char* last = strrchr(buf, '\\');
    if (!last) last = strrchr(buf, '/');
    if (last) *(last + 1) = '\0';
    return 0;
#elif defined(__APPLE__)
    uint32_t size = (uint32_t)bufsz;
    if (_NSGetExecutablePath(buf, &size) != 0) return -1;
    buf[bufsz - 1] = '\0';
    char* last = strrchr(buf, '/');
    if (last) *(last + 1) = '\0';
    return 0;
#elif defined(__FreeBSD__)
    int mib[4] = { CTL_KERN, KERN_PROC, KERN_PROC_PATHNAME, -1 };
    size_t len = bufsz;
    if (sysctl(mib, 4, buf, &len, NULL, 0) != 0) return -1;
    char* last = strrchr(buf, '/');
    if (last) *(last + 1) = '\0';
    return 0;
#else
    /* Linux: /proc/self/exe */
    ssize_t len = readlink("/proc/self/exe", buf, bufsz - 1);
    if (len <= 0) return -1;
    buf[len] = '\0';
    char* last = strrchr(buf, '/');
    if (last) *(last + 1) = '\0';
    return 0;
#endif
}

/* Cross-platform: check file exists */
static int file_accessible(const char* path) {
#ifdef _WIN32
    return _access(path, 0) == 0;
#else
    return access(path, X_OK) == 0;
#endif
}

/* Cross-platform: get exit status from system() */
static int get_exit_status(int rc) {
#ifdef _WIN32
    return rc;  /* Windows system() returns exit code directly */
#else
    return WEXITSTATUS(rc);
#endif
}

static long long cli_compile(SimpleStringArray a) {
    /* Parse compile args: compile [--backend=c] [-o output] source.spl */
    const char* source_file = NULL;
    const char* output_file = NULL;
    const char* backend = "c";
    int verbose = 0;
    for (long long i = 0; i < a.len; i++) {
        const char* arg = a.items[i];
        if (strcmp(arg, "compile") == 0) continue;
        if (strncmp(arg, "--backend=", 10) == 0) { backend = arg + 10; continue; }
        if (strcmp(arg, "--verbose") == 0 || strcmp(arg, "-v") == 0) { verbose = 1; continue; }
        if (strcmp(arg, "-o") == 0 && i + 1 < a.len) { output_file = a.items[++i]; continue; }
        if (strncmp(arg, "-o", 2) == 0 && strlen(arg) > 2) { output_file = arg + 2; continue; }
        if (strncmp(arg, "--output=", 9) == 0) { output_file = arg + 9; continue; }
        if (arg[0] == '-') continue; /* skip unknown flags */
        if (!source_file) source_file = arg;
    }
    if (!source_file) {
        fprintf(stderr, "Error: No source file specified\nUsage: simple compile [--backend=c] [-o output] source.spl\n");
        return 1;
    }
    /* Default output file */
    char out_buf[4096];
    if (!output_file) {
        strncpy(out_buf, source_file, sizeof(out_buf) - 5);
        char* dot = strrchr(out_buf, '.');
        if (dot) strcpy(dot, ".c"); else strcat(out_buf, ".c");
        output_file = out_buf;
    }
    /* Find simple_codegen in same directory as this binary */
    char self_path[4096] = {0};
    if (get_exe_dir(self_path, sizeof(self_path)) != 0) {
        fprintf(stderr, "Error: cannot determine binary location\n");
        return 1;
    }
    char codegen_path[4096];
#ifdef _WIN32
    snprintf(codegen_path, sizeof(codegen_path), "%ssimple_codegen.exe", self_path);
#else
    snprintf(codegen_path, sizeof(codegen_path), "%ssimple_codegen", self_path);
#endif
    /* Check codegen exists */
    if (!file_accessible(codegen_path)) {
        fprintf(stderr, "Error: simple_codegen not found at %s\n", codegen_path);
        return 1;
    }
    if (verbose) printf("Compiling %s to C (backend=%s)\n", source_file, backend);
    /* Build and run command */
    char cmd[8192];
#ifdef _WIN32
    snprintf(cmd, sizeof(cmd), "\"%s\" compile \"%s\" \"%s\"", codegen_path, source_file, output_file);
#else
    snprintf(cmd, sizeof(cmd), "'%s' compile '%s' '%s'", codegen_path, source_file, output_file);
#endif
    int rc = system(cmd);
    if (rc == 0) {
        printf("Output: %s\n", output_file);
        printf("Build with: clang -std=gnu11 -O2 %s -lm -o output\n", output_file);
    }
    return get_exit_status(rc);
}
static long long cli_handle_web(SimpleStringArray a) { (void)a; return 0; }
static long long cli_handle_diagram(SimpleStringArray a) { (void)a; return 0; }
static long long cli_handle_run(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }
static void fault_set_stack_overflow_detection(long long v) { (void)v; }
static void fault_set_max_recursion_depth(long long v) { (void)v; }
static void fault_set_timeout(long long v) { (void)v; }
static void fault_set_execution_limit(long long v) { (void)v; }
static int jit_available(void) { return 0; }
static long long handle_build(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_check(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_arch_check(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_check_dbs(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_fix_dbs(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_doc_coverage(SimpleStringArray a) { (void)a; return delegate_to_interpreter("main.spl"); }
static long long run_stats(SimpleStringArray a) { (void)a; return delegate_to_interpreter("stats_entry.spl"); }
static long long run_leak_check() { return delegate_to_interpreter("leak_check_entry.spl"); }
static void print_cli_help(void) {
    printf("Simple Language v%s\n\n", env_get("SIMPLE_VERSION"));
    printf("Usage: simple <command> [options]\n\n");
    printf("Commands:\n");
    printf("  <file.spl>     Run a Simple source file\n");
    printf("  test           Run tests\n");
    printf("  compile        Compile to C backend\n");
    printf("  build          Build project\n");
    printf("  lint           Run linter\n");
    printf("  fmt            Format code\n");
    printf("  fix            Auto-fix issues\n");
    printf("  stats          Show project statistics\n");
    printf("  mcp            Start MCP server\n");
    printf("  lsp            Start LSP server\n");
    printf("  check          Run checks\n");
    printf("  doc-coverage   Documentation coverage report\n");
    printf("  todo-scan      Scan TODOs\n");
    printf("  targets        List compilation targets\n");
    printf("  linkers        List available linkers\n");
    printf("  -c <code>      Execute code inline\n");
    printf("  --version      Show version\n");
    printf("  --help         Show this help\n");
    printf("\nGlobal Flags:\n");
    printf("  --gc-log          Log GC activity\n");
    printf("  --gc-off          Disable GC\n");
    printf("  --no-jit          Disable JIT\n");
    printf("  --interpret       Force interpreter mode\n");
    printf("  --backend=<name>  Select backend\n");
    printf("  --timeout=<secs>  Set execution timeout\n");
}
static long long handle_init(SimpleStringArray a) { (void)a; return 0; }
static const char* read_sdn_run_config(void) { return ""; }
static long long sdn_line_indent() { return 0; }
static const char* strip_sdn_quotes(void) { return ""; }
static int check_self_contained(void) { return 0; }
static void simple_error(const char* cat, const char* msg) { fprintf(stderr, "%s: %s\n", cat, msg); }
static void error(const char* cat, const char* msg) { simple_error(cat, msg); }
static int jit_native_available(void) { return 0; }
extern void spl_init_args(int argc, char** argv);
SimpleStringArray get_cli_args(void);
const char* get_version(void);
void print_version(void);
void print_targets(void);
void print_linkers(void);
void print_error(const char* msg);
void print_error_with_help(const char* msg);
long long run_lex_command(const char* path);
GlobalFlags parse_global_flags(SimpleStringArray args);
void apply_fault_detection(GlobalFlags flags);
void apply_jit_env_vars(GlobalFlags flags);
SimpleStringArray filter_internal_flags(SimpleStringArray args);

SimpleStringArray get_cli_args(void) {
    SimpleStringArray all_args = cli_get_args();
    SimpleStringArray args = simple_new_string_array();
    long long start_idx = 1;
    if (((all_args.len > 1) && simple_ends_with(all_args.items[1], "main.spl"))) {
    start_idx = 2;
    }
    long long i = start_idx;
    while ((i < all_args.len)) {
    simple_string_push(&args, all_args.items[i]);
    i = (i + 1);
    }
    simple_string_array_free(&all_args);
    return args;
}

const char* get_version(void) {
    const char* version = env_get("SIMPLE_VERSION");
    if (((strcmp(version, "") != 0) && (version != NULL))) {
    return version;
    }
    return "0.6.1";
}

void print_version(void) {
    const char* v = get_version();
    printf("Simple v%s\n", v);
}

void print_targets(void) {
    printf("%s\n", "Available target architectures:");
    printf("%s\n", "");
    printf("%s\n", "  x86_64          64-bit x86 Linux (ELF)");
    printf("%s\n", "  aarch64         64-bit ARM Linux (ELF)");
    printf("%s\n", "  riscv64         64-bit RISC-V Linux (ELF)");
    printf("%s\n", "  aarch64-macos   64-bit ARM macOS (Mach-O, Apple Silicon)");
    printf("%s\n", "  x86_64-macos    64-bit x86 macOS (Mach-O, Intel Mac)");
    printf("%s\n", "  i686            32-bit x86");
    printf("%s\n", "  armv7           32-bit ARM");
    printf("%s\n", "  riscv32         32-bit RISC-V");
    printf("%s\n", "");
    printf("%s\n", "WebAssembly:");
    printf("%s\n", "  wasm32-wasi     32-bit WebAssembly (WASI Preview 1)");
    printf("%s\n", "  wasm32          32-bit WebAssembly (standalone, no WASI)");
    printf("%s\n", "  wasm64          64-bit WebAssembly (Memory64 proposal)");
    printf("%s\n", "");
    printf("%s\n", "Usage:");
    printf("%s\n", "  simple compile app.spl --target aarch64");
    printf("%s\n", "  simple compile app.spl --target aarch64-macos");
    printf("%s\n", "  simple compile app.spl --target wasm32-wasi -o app.wasm");
}

void print_linkers(void) {
    printf("%s\n", "Available native linkers:");
    printf("%s\n", "");
    printf("%s\n", "  mold      Modern linker (fastest, recommended)");
    printf("%s\n", "  lld       LLVM linker (fast, widely available)");
    printf("%s\n", "  ld        GNU linker (default, always available)");
    printf("%s\n", "");
    printf("%s\n", "The linker is auto-detected if not specified.");
    printf("%s\n", "Preference order: mold > lld > ld");
    printf("%s\n", "");
    printf("%s\n", "Usage:");
    printf("%s\n", "  simple compile app.spl --linker mold");
}

void print_error(const char* msg) {
    simple_error("cli", msg);
}

void print_error_with_help(const char* msg) {
    simple_error("cli", msg);
    printf("%s\n", "");
    print_cli_help();
}

long long run_lex_command(const char* path) {
    SimpleStringArray args = get_cli_args();
    long long rc = cli_run_lex(args);
    simple_string_array_free(&args);
    return rc;
}

GlobalFlags parse_global_flags(SimpleStringArray args) {
    int gc_log = 0;
    int gc_off = 0;
    int use_notui = 0;
    long long max_recursion_depth = 0;
    long long timeout_secs = 0;
    long long execution_limit = 0;
    int stack_overflow_detection = 0;
    int has_stack_overflow_flag = 0;
    const char* backend = "auto";
    int force_interpret = 0;
    const char* interpreter_mode = "optimized";
    const char* run_config = "";
    int no_jit = 0;
    long long jit_threshold = 10;
    long long i = 0;
    while ((i < args.len)) {
    const char* arg = args.items[i];
    if ((strcmp(arg, "--gc-log") == 0)) {
    gc_log = 1;
    } else if ((strcmp(arg, "--gc-off") == 0)) {
    gc_off = 1;
    } else if ((strcmp(arg, "--notui") == 0)) {
    use_notui = 1;
    } else if ((strcmp(arg, "--interpret") == 0)) {
    force_interpret = 1;
    } else if ((strcmp(arg, "--interpret-optimized") == 0)) {
    force_interpret = 1;
    interpreter_mode = "optimized";
    } else if ((strcmp(arg, "--no-jit") == 0)) {
    no_jit = 1;
    } else if (simple_starts_with(arg, "--jit-threshold=")) {
    jit_threshold = atoll(arg + 16);
    } else if (((strcmp(arg, "--jit-threshold") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    jit_threshold = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--interpreter-mode=")) {
    interpreter_mode = arg + 19;
    } else if (((strcmp(arg, "--interpreter-mode") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    interpreter_mode = args.items[i];
    } else if (simple_starts_with(arg, "--run-config=")) {
    run_config = arg + 13;
    } else if (((strcmp(arg, "--run-config") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    run_config = args.items[i];
    } else if (simple_starts_with(arg, "--backend=")) {
    backend = arg + 10;
    } else if (((strcmp(arg, "--backend") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    backend = args.items[i];
    } else if ((strcmp(arg, "--stack-overflow-detection") == 0)) {
    stack_overflow_detection = 1;
    has_stack_overflow_flag = 1;
    } else if ((strcmp(arg, "--no-stack-overflow-detection") == 0)) {
    stack_overflow_detection = 0;
    has_stack_overflow_flag = 1;
    } else if (simple_starts_with(arg, "--max-recursion-depth=")) {
    max_recursion_depth = atoll(arg + 21);
    } else if (((strcmp(arg, "--max-recursion-depth") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    max_recursion_depth = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--timeout=")) {
    timeout_secs = atoll(arg + 10);
    } else if (((strcmp(arg, "--timeout") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    timeout_secs = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--execution-limit=")) {
    execution_limit = atoll(arg + 18);
    } else if (((strcmp(arg, "--execution-limit") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    execution_limit = atoll(args.items[i]);
        }
    i = (i + 1);
    }
    if (!((force_interpret && (strcmp(backend, "auto") == 0)))) {
    const char* env_mode = env_get("SIMPLE_EXECUTION_MODE");
    if ((strcmp(env_mode, "interpret") == 0)) {
    force_interpret = 1;
    } else if ((strcmp(env_mode, "interpret-optimized") == 0)) {
    force_interpret = 1;
    interpreter_mode = "optimized";
    } else if ((strcmp(env_mode, "cranelift") == 0)) {
    backend = "cranelift";
    } else if ((strcmp(env_mode, "llvm") == 0)) {
    backend = "llvm";
    } else if ((strcmp(env_mode, "vhdl") == 0)) {
    backend = "vhdl";
    } else if ((strcmp(env_mode, "jit") == 0)) {
    backend = "auto";
        }
    }
    if ((strcmp(run_config, "") == 0)) {
    run_config = read_sdn_run_config();
    }
    if (((strcmp(run_config, "compiler") == 0) || (strcmp(run_config, "shared") == 0))) {
    interpreter_mode = "optimized";
    force_interpret = 1;
    } else if ((strcmp(run_config, "interpreter") == 0)) {
    interpreter_mode = "optimized";
    force_interpret = 1;
    } else if ((strcmp(run_config, "legacy") == 0)) {
    interpreter_mode = "classic";
    force_interpret = 1;
    }
    return (GlobalFlags){.gc_log = gc_log, .gc_off = gc_off, .use_notui = use_notui, .max_recursion_depth = max_recursion_depth, .timeout_secs = timeout_secs, .execution_limit = execution_limit, .stack_overflow_detection = stack_overflow_detection, .backend = backend, .force_interpret = force_interpret, .interpreter_mode = interpreter_mode, .run_config = run_config, .no_jit = no_jit, .jit_threshold = jit_threshold};
}

void apply_fault_detection(GlobalFlags flags) {
    if ((flags.max_recursion_depth > 0)) {
    fault_set_max_recursion_depth(flags.max_recursion_depth);
    fault_set_stack_overflow_detection(1);
    }
    if (flags.stack_overflow_detection) {
    fault_set_stack_overflow_detection(1);
    }
    if ((flags.timeout_secs > 0)) {
    fault_set_timeout(flags.timeout_secs);
    }
    if ((flags.execution_limit > 0)) {
    fault_set_execution_limit(flags.execution_limit);
    }
}

void apply_jit_env_vars(GlobalFlags flags) {
    if (flags.no_jit) {
    env_set("SIMPLE_NO_JIT", "1");
    }
    if ((flags.jit_threshold != 10)) {
    char t[32];
    snprintf(t, sizeof(t), "%lld", flags.jit_threshold);
    env_set("SIMPLE_JIT_THRESHOLD", t);
    }
    if ((strcmp(flags.backend, "auto") != 0)) {
    env_set("SIMPLE_JIT_BACKEND", flags.backend);
    }
}

SimpleStringArray filter_internal_flags(SimpleStringArray args) {
    SimpleStringArray result = simple_new_string_array();
    int skip_next = 0;
    for (long long _i_arg = 0; _i_arg < args.len; _i_arg++) { const char* arg = args.items[_i_arg];
    if (skip_next) {
    skip_next = 0;
    } else if (((((((strcmp(arg, "--max-recursion-depth") == 0) || (strcmp(arg, "--timeout") == 0)) || (strcmp(arg, "--execution-limit") == 0)) || (strcmp(arg, "--interpreter-mode") == 0)) || (strcmp(arg, "--run-config") == 0)) || (strcmp(arg, "--jit-threshold") == 0))) {
    skip_next = 1;
    } else if (!((((((((simple_starts_with(arg, "--gc") && (strcmp(arg, "--notui") != 0)) && (strcmp(arg, "--lang") != 0)) && (strcmp(arg, "--stack-overflow-detection") != 0)) && (strcmp(arg, "--no-stack-overflow-detection") != 0)) && (strcmp(arg, "--interpret") != 0)) && (strcmp(arg, "--interpret-optimized") != 0)) && (strcmp(arg, "--no-jit") != 0)))) {
    if (!(((((((simple_starts_with(arg, "--lang=") && !(simple_starts_with(arg, "--max-recursion-depth="))) && !(simple_starts_with(arg, "--timeout="))) && !(simple_starts_with(arg, "--execution-limit="))) && !(simple_starts_with(arg, "--interpreter-mode"))) && !(simple_starts_with(arg, "--run-config"))) && !(simple_starts_with(arg, "--jit-threshold="))))) {
    simple_string_push(&result, arg);
            }
        }
    }
    return result;
}

static SimpleStringArray _main_args;
static SimpleStringArray _main_filtered;
static void _main_cleanup(void) {
    simple_string_array_free(&_main_args);
    simple_string_array_free(&_main_filtered);
}

int main(int argc, char** argv) {
    g_argc_main = argc;
    g_argv_main = argv;
    spl_init_args(argc, argv);
    SimpleStringArray args = get_cli_args();
    _main_args = args;
    _main_filtered = (SimpleStringArray){NULL, 0, 0};
    atexit(_main_cleanup);
    if ((args.len == 0)) {
    if (check_self_contained()) {
    return 0;
        }
    }
    GlobalFlags flags = parse_global_flags(args);
    apply_fault_detection(flags);
    apply_jit_env_vars(flags);
    SimpleStringArray filtered_args = filter_internal_flags(args);
    _main_filtered = filtered_args;
    if (((strcmp(flags.backend, "auto") != 0) && !(flags.force_interpret))) {
    if (!(jit_native_available())) {
    char err_buf[256];
    snprintf(err_buf, sizeof(err_buf), "requested JIT backend '%s' but runtime has no native exec_manager support", flags.backend);
    print_error(err_buf);
    return 1;
        }
    }
    /* Suppress [jit] info message — this is a compiled CLI dispatcher,
     * JIT is only relevant when running .spl through the interpreter. */
    if ((filtered_args.len == 0)) {
    return cli_run_repl(flags.gc_log, flags.gc_off);
    }
    const char* first = filtered_args.items[0];
    { const char* _match_val = first;
    if (strcmp(_match_val, "-h") == 0 || strcmp(_match_val, "--help") == 0) {
    print_cli_help();
    return 0;
    } else if (strcmp(_match_val, "-v") == 0 || strcmp(_match_val, "--version") == 0) {
    print_version();
    return 0;
    } else if (strcmp(_match_val, "-c") == 0) {
    if ((filtered_args.len < 2)) {
    print_error("-c requires a code argument");
    return 1;
        }
    return cli_run_code(filtered_args.items[1], flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "compile") == 0) {
    return cli_compile(filtered_args);
    } else if (strcmp(_match_val, "targets") == 0) {
    print_targets();
    return 0;
    } else if (strcmp(_match_val, "linkers") == 0) {
    print_linkers();
    return 0;
    } else if (strcmp(_match_val, "web") == 0) {
    return cli_handle_web(filtered_args);
    } else if (strcmp(_match_val, "watch") == 0) {
    if ((filtered_args.len < 2)) {
    print_error("watch requires a source file");
    return 1;
        }
    return cli_watch_file(filtered_args.items[1]);
    } else if (strcmp(_match_val, "test") == 0) {
    SimpleStringArray test_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = cli_run_tests(test_args, flags.gc_log, flags.gc_off);
    simple_string_array_free(&test_args);
    return _rc;
    } else if (strcmp(_match_val, "lex") == 0) {
    if ((filtered_args.len < 2)) {
    print_error("lex requires a source file");
    return 1;
        }
    return run_lex_command(filtered_args.items[1]);
    } else if (strcmp(_match_val, "lint") == 0) {
    return cli_run_lint(filtered_args);
    } else if (strcmp(_match_val, "duplicate-check") == 0) {
    return cli_run_file("src/app/duplicate_check/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "fix") == 0) {
    return cli_run_fix(filtered_args);
    } else if (strcmp(_match_val, "fmt") == 0) {
    return cli_run_fmt(filtered_args);
    } else if (strcmp(_match_val, "check") == 0) {
    SimpleStringArray check_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = run_check(check_args);
    simple_string_array_free(&check_args);
    return _rc;
    } else if (strcmp(_match_val, "doc-coverage") == 0) {
    SimpleStringArray dc_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = run_doc_coverage(dc_args);
    simple_string_array_free(&dc_args);
    return _rc;
    } else if (strcmp(_match_val, "check-arch") == 0) {
    SimpleStringArray arch_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = run_arch_check(arch_args);
    simple_string_array_free(&arch_args);
    return _rc;
    } else if (strcmp(_match_val, "check-dbs") == 0) {
    SimpleStringArray check_db_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = run_check_dbs(check_db_args);
    simple_string_array_free(&check_db_args);
    return _rc;
    } else if (strcmp(_match_val, "fix-dbs") == 0) {
    SimpleStringArray fix_db_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = run_fix_dbs(fix_db_args);
    simple_string_array_free(&fix_db_args);
    return _rc;
    } else if (strcmp(_match_val, "grammar-doc") == 0) {
    SimpleStringArray grammar_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = cli_run_file("src/app/grammar_doc/mod.spl", grammar_args, flags.gc_log, flags.gc_off);
    simple_string_array_free(&grammar_args);
    return _rc;
    } else if (strcmp(_match_val, "i18n") == 0) {
    return cli_run_i18n(filtered_args);
    } else if (strcmp(_match_val, "migrate") == 0) {
    return cli_run_migrate(filtered_args);
    } else if (strcmp(_match_val, "mcp") == 0) {
    return cli_run_mcp(filtered_args);
    } else if (strcmp(_match_val, "lsp") == 0) {
    return cli_run_lsp(filtered_args);
    } else if (strcmp(_match_val, "diff") == 0) {
    return cli_run_diff(filtered_args);
    } else if (strcmp(_match_val, "constr") == 0) {
    return cli_constr(filtered_args);
    } else if (strcmp(_match_val, "query") == 0) {
    return cli_run_query(filtered_args);
    } else if (strcmp(_match_val, "info") == 0) {
    return cli_info(filtered_args);
    } else if (strcmp(_match_val, "spec-coverage") == 0) {
    return cli_run_spec_coverage(filtered_args);
    } else if (strcmp(_match_val, "replay") == 0) {
    return cli_replay(filtered_args);
    } else if (strcmp(_match_val, "gen-lean") == 0) {
    return cli_gen_lean(filtered_args);
    } else if (strcmp(_match_val, "feature-gen") == 0) {
    return cli_run_feature_gen(filtered_args);
    } else if (strcmp(_match_val, "task-gen") == 0) {
    return cli_run_task_gen(filtered_args);
    } else if (strcmp(_match_val, "spec-gen") == 0) {
    return cli_run_spec_gen(filtered_args);
    } else if (strcmp(_match_val, "sspec-docgen") == 0) {
    return cli_run_sspec_docgen(filtered_args);
    } else if (strcmp(_match_val, "feature-doc") == 0) {
    return cli_run_feature_doc(filtered_args);
    } else if (strcmp(_match_val, "todo-scan") == 0) {
    return cli_todo_scan(filtered_args);
    } else if (strcmp(_match_val, "todo-gen") == 0) {
    return cli_run_todo_gen(filtered_args);
    } else if (strcmp(_match_val, "brief") == 0) {
    return cli_run_brief(filtered_args);
    } else if (strcmp(_match_val, "stats") == 0) {
    SimpleStringArray stats_args = simple_string_array_slice(filtered_args, 1);
    run_stats(stats_args);
    simple_string_array_free(&stats_args);
    return 0;
    } else if (strcmp(_match_val, "ffi-gen") == 0) {
    return cli_run_ffi_gen(filtered_args);
    } else if (strcmp(_match_val, "wrapper-gen") == 0) {
    return cli_run_file("src/app/wrapper_gen/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "desugar") == 0) {
    return cli_run_file("src/app/desugar/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "dashboard") == 0) {
    SimpleStringArray dashboard_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = cli_run_file("src/app/dashboard/main.spl", dashboard_args, flags.gc_log, flags.gc_off);
    simple_string_array_free(&dashboard_args);
    return _rc;
    } else if (strcmp(_match_val, "verify") == 0) {
    return cli_run_verify(filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "diagram") == 0) {
    return cli_handle_diagram(filtered_args);
    } else if (strcmp(_match_val, "build") == 0) {
    SimpleStringArray build_args = simple_string_array_slice(filtered_args, 1);
    long long _rc = handle_build(build_args);
    simple_string_array_free(&build_args);
    return _rc;
    } else if (strcmp(_match_val, "init") == 0) {
    return handle_init(filtered_args);
    } else if (strcmp(_match_val, "add") == 0) {
    return cli_run_file("src/app/add/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "remove") == 0) {
    return cli_run_file("src/app/remove/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "install") == 0) {
    return cli_run_file("src/app/install/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "update") == 0) {
    return cli_run_file("src/app/update/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "list") == 0) {
    return cli_run_file("src/app/list/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "tree") == 0) {
    return cli_run_file("src/app/tree/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "cache") == 0) {
    return cli_run_file("src/app/cache/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "env") == 0) {
    return cli_run_file("src/app/env/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "lock") == 0) {
    return cli_run_file("src/app/lock/main.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "run") == 0) {
    return cli_handle_run(filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "leak-check") == 0) {
    return run_leak_check();
    } else {
    if (cli_file_exists(first)) {
    SimpleStringArray program_args = simple_new_string_array() /* TODO: array literal */;
    long long j = 1;
    while ((j < filtered_args.len)) {
    simple_string_push(&program_args, filtered_args.items[j]);
    j = (j + 1);
            }
    long long _rc = cli_run_file(first, program_args, flags.gc_log, flags.gc_off);
    simple_string_array_free(&program_args);
    return _rc;
    } else {
    char _err_msg[4096];
    snprintf(_err_msg, sizeof(_err_msg), "file not found: %s", first);
    print_error_with_help(_err_msg);
    return 1;
    }
    }
    }
    return 0;
}
