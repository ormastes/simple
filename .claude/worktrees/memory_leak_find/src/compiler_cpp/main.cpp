#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include <math.h>
#include <unistd.h>
#include <time.h>
#include <sys/stat.h>

#define nil NULL
#define pass_do_nothing ((void)0)
#define pass_dn ((void)0)
#define pass_todo ((void)0)

#pragma GCC diagnostic ignored "-Wdeprecated-non-prototype"
#pragma GCC diagnostic ignored "-Wparentheses-equality"
#pragma GCC diagnostic ignored "-Wunused-value"

static long long simple_strlen(const char* s) { return s ? (long long)strlen(s) : 0; }

static char* simple_str_concat(const char* a, const char* b) {
    if (!a) a = ""; if (!b) b = "";
    size_t la = strlen(a), lb = strlen(b);
    char* r = (char*)malloc(la + lb + 1);
    memcpy(r, a, la); memcpy(r + la, b, lb); r[la+lb] = 0;
    return r;
}

static int simple_starts_with(const char* s, const char* p) { if (!s||!p) return 0; return strncmp(s,p,strlen(p))==0; }
static int simple_ends_with(const char* s, const char* x) { if(!s||!x) return 0; size_t sl=strlen(s),xl=strlen(x); return sl>=xl && strcmp(s+sl-xl,x)==0; }
static int simple_contains(const char* s, const char* n) { if(!s||!n) return 0; return strstr(s,n)!=NULL; }
static char* simple_replace(const char* s, const char* o, const char* n) {
    if(!s) return strdup(""); if(!o||!n||!*o) return strdup(s);
    size_t ol=strlen(o),nl=strlen(n); const char*p=s; char*r=malloc(strlen(s)*2+1); char*d=r;
    while(*p){if(strncmp(p,o,ol)==0){memcpy(d,n,nl);d+=nl;p+=ol;}else{*d++=*p++;}}
    *d=0; return r;
}

typedef struct { const char** items; long long len; long long cap; } SimpleStringArray;
static SimpleStringArray simple_new_string_array(void) { SimpleStringArray a; a.items=(const char**)malloc(16*sizeof(const char*)); a.len=0; a.cap=16; return a; }
static void simple_string_push(SimpleStringArray* a, const char* s) { if(a->len>=a->cap){a->cap*=2;a->items=(const char**)realloc(a->items,a->cap*sizeof(const char*));} a->items[a->len++]=strdup(s?s:""); }
static SimpleStringArray simple_string_array_slice(SimpleStringArray a, long long start) { SimpleStringArray r=simple_new_string_array(); for(long long i=start;i<a.len;i++) simple_string_push(&r,a.items[i]); return r; }

static char* simple_format_long(const char* b, long long v, const char* a) { char buf[256]; snprintf(buf,256,"%s%lld%s",b?b:"",v,a?a:""); return strdup(buf); }
static char* simple_format_str(const char* b, const char* v, const char* a) { size_t t=strlen(b?b:"")+strlen(v?v:"")+strlen(a?a:"")+1; char*r=malloc(t); snprintf(r,t,"%s%s%s",b?b:"",v?v:"",a?a:""); return r; }
static char* simple_int_to_str(long long v) { char b[32]; snprintf(b,32,"%lld",v); return strdup(b); }
static const char* simple_substr_from(const char* s, long long start) { if(!s) return ""; long long l=strlen(s); if(start>=l) return ""; return strdup(s+start); }

typedef struct { long long* items; long long len; long long cap; } SimpleIntArray;
static SimpleIntArray simple_new_int_array(void) { SimpleIntArray a; a.items=(long long*)malloc(16*sizeof(long long)); a.len=0; a.cap=16; return a; }
static void simple_int_push(SimpleIntArray* a, long long v) { if(a->len>=a->cap){a->cap*=2;a->items=(long long*)realloc(a->items,a->cap*sizeof(long long));} a->items[a->len++]=v; }
static long long simple_int_get(SimpleIntArray a, long long i) { return a.items[i]; }

typedef struct { SimpleStringArray* items; long long len; long long cap; } SimpleStringArrayArray;
static SimpleStringArrayArray simple_new_string_array_array(void) { SimpleStringArrayArray a; a.items=(SimpleStringArray*)malloc(8*sizeof(SimpleStringArray)); a.len=0; a.cap=8; return a; }
static void simple_str_arr_push(SimpleStringArrayArray* a, SimpleStringArray v) { if(a->len>=a->cap){a->cap*=2;a->items=(SimpleStringArray*)realloc(a->items,a->cap*sizeof(SimpleStringArray));} a->items[a->len++]=v; }

typedef struct { SimpleIntArray* items; long long len; long long cap; } SimpleIntArrayArray;
static SimpleIntArrayArray simple_new_int_array_array(void) { SimpleIntArrayArray a; a.items=(SimpleIntArray*)malloc(8*sizeof(SimpleIntArray)); a.len=0; a.cap=8; return a; }

typedef struct { void** items; long long len; long long cap; } SimpleStructArray;
static SimpleStructArray simple_new_struct_array(void) { SimpleStructArray a; a.items=NULL; a.len=0; a.cap=0; return a; }
static void simple_struct_push(SimpleStructArray* a, void* v) { if(a->len>=a->cap){a->cap=a->cap?a->cap*2:8;a->items=(void**)realloc(a->items,a->cap*sizeof(void*));} a->items[a->len++]=v; }

static char* simple_trim(const char* s) {
    if(!s) return strdup("");
    while(*s==' '||*s=='\t'||*s=='\n'||*s=='\r') s++;
    long long l=strlen(s);
    while(l>0&&(s[l-1]==' '||s[l-1]=='\t'||s[l-1]=='\n'||s[l-1]=='\r')) l--;
    char* r=malloc(l+1); memcpy(r,s,l); r[l]=0; return r;
}
static long long simple_index_of(const char* s, const char* n) { if(!s||!n) return -1; const char* f=strstr(s,n); return f?(long long)(f-s):-1; }
static long long simple_last_index_of(const char* s, const char* n) { if(!s||!n) return -1; long long nl=strlen(n),sl=strlen(s); if(nl>sl) return -1; for(long long i=sl-nl;i>=0;i--) if(strncmp(s+i,n,nl)==0) return i; return -1; }
static char* simple_substring(const char* s, long long a, long long b) { if(!s) return strdup(""); long long l=strlen(s); if(a<0)a=0; if(b>l)b=l; if(a>=b) return strdup(""); long long n=b-a; char*r=malloc(n+1); memcpy(r,s+a,n); r[n]=0; return r; }
static char* simple_char_at(const char* s, long long i) { if(!s||i<0||i>=(long long)strlen(s)) return strdup(""); char*r=malloc(2); r[0]=s[i]; r[1]=0; return r; }
static SimpleStringArray simple_split(const char* s, const char* d) {
    SimpleStringArray a=simple_new_string_array();
    if(!s) return a; if(!d||!*d){simple_string_push(&a,s);return a;}
    long long dl=strlen(d); const char*p=s; const char*f;
    while((f=strstr(p,d))!=NULL){long long n=f-p;char*t=malloc(n+1);memcpy(t,p,n);t[n]=0;simple_string_push(&a,t);free(t);p=f+dl;}
    simple_string_push(&a,p); return a;
}
static char* simple_string_join(SimpleStringArray* a, const char* d) {
    if(!a||a->len==0) return strdup(""); long long dl=strlen(d),t=0;
    for(long long i=0;i<a->len;i++){t+=strlen(a->items[i]);if(i<a->len-1)t+=dl;}
    char*r=malloc(t+1);char*p=r;
    for(long long i=0;i<a->len;i++){long long l=strlen(a->items[i]);memcpy(p,a->items[i],l);p+=l;if(i<a->len-1){memcpy(p,d,dl);p+=dl;}}
    *p=0; return r;
}
static const char* simple_string_pop(SimpleStringArray* a) { if(a->len==0) return ""; return a->items[--a->len]; }
static long long simple_int_pop(SimpleIntArray* a) { if(a->len==0) return 0; return a->items[--a->len]; }

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
static const char* env_get(const char* k) { (void)k; return ""; }
static void env_set(const char* k, const char* v) { (void)k; (void)v; }
static long long shell(void) { return 0; }
static long long file_size_raw(void) { return 0; }
static int cli_file_exists(const char* p) { (void)p; return 0; }
static long long cli_read_file(SimpleStringArray a) { (void)a; return 0; }
static SimpleStringArray cli_get_args(void) { return simple_new_string_array(); }
static long long cli_run_code(const char* c, int g, int o) { (void)c;(void)g;(void)o; return 0; }
static long long cli_run_file(const char* p, SimpleStringArray a, int g, int o) { (void)p;(void)a;(void)g;(void)o; return 0; }
static long long cli_watch_file(const char* p) { (void)p; return 0; }
static long long cli_run_repl(int g, int o) { (void)g;(void)o; return 0; }
static long long cli_run_tests(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }
static long long cli_run_lint(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_fmt(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_fix(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_verify(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }
static long long cli_run_migrate(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_mcp(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_lsp(SimpleStringArray a) { (void)a; return 0; }
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
static long long cli_todo_scan(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_todo_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_lex(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_brief(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_ffi_gen(SimpleStringArray a) { (void)a; return 0; }
static long long cli_run_i18n(SimpleStringArray a) { (void)a; return 0; }
static long long cli_compile(SimpleStringArray a) { (void)a; return 0; }
static long long cli_handle_web(SimpleStringArray a) { (void)a; return 0; }
static long long cli_handle_diagram(SimpleStringArray a) { (void)a; return 0; }
static long long cli_handle_run(SimpleStringArray a, int g, int o) { (void)a;(void)g;(void)o; return 0; }
static void fault_set_stack_overflow_detection(long long v) { (void)v; }
static void fault_set_max_recursion_depth(long long v) { (void)v; }
static void fault_set_timeout(long long v) { (void)v; }
static void fault_set_execution_limit(long long v) { (void)v; }
static int jit_available(void) { return 0; }
static long long handle_build(SimpleStringArray a) { (void)a; return 0; }
static long long run_check(SimpleStringArray a) { (void)a; return 0; }
static long long run_arch_check(SimpleStringArray a) { (void)a; return 0; }
static long long run_check_dbs(SimpleStringArray a) { (void)a; return 0; }
static long long run_fix_dbs(SimpleStringArray a) { (void)a; return 0; }
static long long run_doc_coverage(SimpleStringArray a) { (void)a; return 0; }
static long long run_stats(SimpleStringArray a) { (void)a; return 0; }
static long long run_leak_check(void) { return 0; }
static void print_cli_help(void) { }
static long long handle_init(SimpleStringArray a) { (void)a; return 0; }
static const char* read_sdn_run_config(void) { return ""; }
static long long sdn_line_indent(void) { return 0; }
static const char* strip_sdn_quotes(void) { return ""; }
static int check_self_contained(void) { return 0; }
static void simple_error(const char* cat, const char* msg) { fprintf(stderr, "%s: %s\n", cat, msg); }
static int jit_native_available(void) { return 0; }
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
    return args;
}

const char* get_version(void) {
    const char* version = env_get("SIMPLE_VERSION");
    if (((strcmp(version, "") != 0) && (version != NULL))) {
    return version;
    }
    return "0.5.0";
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
    return cli_run_lex(args);
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
    const char* val_str = simple_substr_from(arg, 16);
    jit_threshold = atoll(val_str);
    } else if (((strcmp(arg, "--jit-threshold") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    jit_threshold = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--interpreter-mode=")) {
    interpreter_mode = simple_substr_from(arg, 19);
    } else if (((strcmp(arg, "--interpreter-mode") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    interpreter_mode = args.items[i];
    } else if (simple_starts_with(arg, "--run-config=")) {
    run_config = simple_substr_from(arg, 13);
    } else if (((strcmp(arg, "--run-config") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    run_config = args.items[i];
    } else if (simple_starts_with(arg, "--backend=")) {
    backend = simple_substr_from(arg, 10);
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
    const char* val_str = simple_substr_from(arg, 21);
    max_recursion_depth = atoll(val_str);
    } else if (((strcmp(arg, "--max-recursion-depth") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    max_recursion_depth = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--timeout=")) {
    const char* val_str = simple_substr_from(arg, 10);
    timeout_secs = atoll(val_str);
    } else if (((strcmp(arg, "--timeout") == 0) && ((i + 1) < args.len))) {
    i = (i + 1);
    timeout_secs = atoll(args.items[i]);
    } else if (simple_starts_with(arg, "--execution-limit=")) {
    const char* val_str = simple_substr_from(arg, 18);
    execution_limit = atoll(val_str);
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
    const char* t = "{flags.jit_threshold}";
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

int main(void) {
    SimpleStringArray args = get_cli_args();
    if ((args.len == 0)) {
    if (check_self_contained()) {
    return 0;
        }
    }
    GlobalFlags flags = parse_global_flags(args);
    apply_fault_detection(flags);
    apply_jit_env_vars(flags);
    SimpleStringArray filtered_args = filter_internal_flags(args);
    if (((strcmp(flags.backend, "auto") != 0) && !(flags.force_interpret))) {
    if (!(jit_native_available())) {
    print_error("requested JIT backend '{flags.backend}' but runtime has no native exec_manager support");
    return 1;
        }
    }
    if (((strcmp(flags.backend, "auto") == 0) && !(flags.force_interpret))) {
    if (!((jit_native_available() && jit_available()))) {
    printf("%s\n", "[jit] Using soft exec_manager fallback (interpreted); native JIT not present.");
        }
    }
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
    return cli_run_tests(test_args, flags.gc_log, flags.gc_off);
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
    return run_check(check_args);
    } else if (strcmp(_match_val, "doc-coverage") == 0) {
    SimpleStringArray dc_args = simple_string_array_slice(filtered_args, 1);
    return run_doc_coverage(dc_args);
    } else if (strcmp(_match_val, "check-arch") == 0) {
    SimpleStringArray arch_args = simple_string_array_slice(filtered_args, 1);
    return run_arch_check(arch_args);
    } else if (strcmp(_match_val, "check-dbs") == 0) {
    SimpleStringArray check_db_args = simple_string_array_slice(filtered_args, 1);
    return run_check_dbs(check_db_args);
    } else if (strcmp(_match_val, "fix-dbs") == 0) {
    SimpleStringArray fix_db_args = simple_string_array_slice(filtered_args, 1);
    return run_fix_dbs(fix_db_args);
    } else if (strcmp(_match_val, "grammar-doc") == 0) {
    SimpleStringArray grammar_args = simple_string_array_slice(filtered_args, 1);
    return cli_run_file("src/app/grammar_doc/mod.spl", grammar_args, flags.gc_log, flags.gc_off);
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
    run_stats(simple_string_array_slice(filtered_args, 1));
    return 0;
    } else if (strcmp(_match_val, "ffi-gen") == 0) {
    return cli_run_ffi_gen(filtered_args);
    } else if (strcmp(_match_val, "wrapper-gen") == 0) {
    return cli_run_file("src/app/wrapper_gen/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "desugar") == 0) {
    return cli_run_file("src/app/desugar/mod.spl", filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "dashboard") == 0) {
    SimpleStringArray dashboard_args = simple_string_array_slice(filtered_args, 1);
    return cli_run_file("src/app/dashboard/main.spl", dashboard_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "verify") == 0) {
    return cli_run_verify(filtered_args, flags.gc_log, flags.gc_off);
    } else if (strcmp(_match_val, "diagram") == 0) {
    return cli_handle_diagram(filtered_args);
    } else if (strcmp(_match_val, "build") == 0) {
    SimpleStringArray build_args = simple_string_array_slice(filtered_args, 1);
    return handle_build(build_args);
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
    return cli_run_file(first, program_args, flags.gc_log, flags.gc_off);
    } else {
    print_error_with_help("file not found: {first}");
    return 1;
    }
    }
    }
    return 0;
}
