/*
 * Bootstrap Seed Compiler — Simple → C++ Transpiler
 *
 * A minimal, self-contained C++ program that reads Core Simple source code
 * and emits equivalent C++ code. This is the "seed" that bootstraps the
 * full Simple compiler written in Simple.
 *
 * Bootstrap chain:
 *   1. c++ (clang++/g++) compiles seed.cpp → seed binary
 *   2. seed compiles src/core/ .spl files (Core Simple) → C++ code
 *   3. c++ compiles C++ code + runtime.c → core compiler binary
 *   4. Core compiler compiles src/compiler/ .spl files (Full Simple)
 *
 * Supported Core Simple subset:
 *   - val/var declarations with type annotations
 *   - fn declarations with typed params and return type
 *   - extern fn declarations
 *   - struct definitions with typed fields
 *   - enum definitions (simple variants, no data)
 *   - impl blocks (methods on structs)
 *   - if/elif/else
 *   - for i in 0..N (range loops), for item in array
 *   - while loops
 *   - match/case (integer patterns, enum variants)
 *   - return, break, continue
 *   - Expressions: arithmetic, comparison, logical, calls, indexing,
 *     field access, method calls, constructor calls
 *   - Array literals, string literals, string interpolation
 *   - Comments (#)
 *   - use/export (tracked for multi-module)
 *
 * NOT supported (Full Simple only):
 *   - generics (<T>), traits, class (use struct), actor, async/await
 *   - lambdas (\x: expr), comprehensions, pipe operators
 *   - math blocks, GPU kernels, bitfields, pattern binding
 *
 * Usage:
 *   c++ -std=c++20 -o build/seed seed/seed.cpp
 *   build/seed input.spl > output.cpp
 *   c++ -std=c++20 -o output output.cpp src/compiler_seed/runtime.c -Isrc/compiler_seed
 */

#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <cctype>
#include <cstdint>
#include <cstdarg>
#include <cassert>
#include <cmath>
#include <vector>

/* ===== Windows Compatibility ===== */
#ifdef _WIN32
  /* ClangCL (MSVC ABI) uses UCRT with _strdup */
  #if defined(_MSC_VER) || defined(SPL_TOOLCHAIN_CLANGCL)
    #define strdup _strdup
    #define snprintf _snprintf
  #endif
  /* MinGW Clang provides POSIX strdup directly */
#endif

/* ===== Configuration ===== */
#define MAX_LINE 4096
#define MAX_LINES 300000        /* Increased for large compiler_core (439 files) - conservative */
#define MAX_IDENT 256          /* Increased for longer identifiers */
#define MAX_OUTPUT (1024 * 1024 * 128)  /* 128 MB output buffer (2x increase) */
#define MAX_INDENT_STACK 512   /* Increased for deeper nesting */
#define MAX_PARAMS 64          /* Increased for functions with many params */
#define MAX_FUNCS 16384        /* Increased for large codebases (2x) */
#define MAX_STRUCTS 4096       /* Increased for large codebases (2x) */
#define MAX_FIELDS 256         /* Increased for structs with many fields */
#define MAX_ENUMS 2048         /* Increased for large codebases (2x) */
#define MAX_VARIANTS 512       /* Increased for enums with many variants */
#define MAX_METHODS 16384      /* Increased for large codebases (2x) */
#define MAX_ASM_TEXT (MAX_LINE * 4)

/* ===== Output Buffer ===== */
static char *output = nullptr;  /* Dynamically allocated to avoid .bss overflow */
static int out_pos = 0;

static void emit(const char *fmt, ...) {
    va_list args;
    va_start(args, fmt);
    out_pos += vsnprintf(output + out_pos, MAX_OUTPUT - out_pos, fmt, args);
    va_end(args);
}

static void emit_indent(int level) {
    for (int i = 0; i < level; i++) emit("    ");
}

/* ===== Source Loading ===== */
static char *source_lines[MAX_LINES];
static int num_lines = 0;

static void strip_inline_comment(char *line);
static void load_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "Cannot open: %s\n", path); exit(1); }
    int file_start = num_lines;
    char buf[MAX_LINE];
    bool in_docstring = false;
    bool in_conflict_theirs = false;  /* Skip "theirs" side of merge conflicts */
    bool in_jj_conflict = false;     /* Inside jj conflict block (skip until +++++++/end) */
    while (fgets(buf, sizeof(buf), f) && num_lines < MAX_LINES) {
        int len = strlen(buf);
        if (len > 0 && buf[len-1] == '\n') buf[len-1] = '\0';
        /* Handle git merge conflict markers — keep "ours" side */
        if (strncmp(buf, "<<<<<<<", 7) == 0) {
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (strncmp(buf, "=======", 7) == 0) {
            in_conflict_theirs = true;
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (strncmp(buf, ">>>>>>>", 7) == 0) {
            in_conflict_theirs = false;
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (in_conflict_theirs) {
            source_lines[num_lines++] = strdup("");
            continue;
        }
        /* Handle jj conflict markers — skip diff/conflict sections entirely */
        if (strncmp(buf, "%%%%%%%", 7) == 0 || strncmp(buf, "|||||||", 7) == 0) {
            in_jj_conflict = true;
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (strncmp(buf, "+++++++", 7) == 0) {
            in_jj_conflict = false;  /* Keep lines after +++++++ (resolved) */
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (in_jj_conflict) {
            source_lines[num_lines++] = strdup("");
            continue;
        }
        /* Skip triple-quote docstrings """...""" and r"""...""" */
        const char *tb = buf;
        while (*tb == ' ' || *tb == '\t') tb++;
        /* Also handle r""" raw docstrings */
        if (tb[0] == 'r' && strncmp(tb + 1, "\"\"\"", 3) == 0) tb++;
        if (strncmp(tb, "\"\"\"", 3) == 0) {
            if (in_docstring) {
                /* End of multi-line docstring */
                in_docstring = false;
                source_lines[num_lines++] = strdup("");
                continue;
            }
            /* Check if docstring opens and closes on same line */
            const char *after = tb + 3;
            const char *close = strstr(after, "\"\"\"");
            if (close) {
                /* Single-line docstring — skip entirely */
                source_lines[num_lines++] = strdup("");
                continue;
            }
            /* Multi-line docstring starts */
            in_docstring = true;
            source_lines[num_lines++] = strdup("");
            continue;
        }
        if (in_docstring) {
            source_lines[num_lines++] = strdup("");
            continue;
        }
        /* Keep conditional directives intact; they are handled in a pre-pass. */
        const char *comment_probe = buf;
        while (*comment_probe == ' ' || *comment_probe == '\t') comment_probe++;
        bool is_conditional_directive =
            strncmp(comment_probe, "@when(", 6) == 0 ||
            strncmp(comment_probe, "@elif(", 6) == 0 ||
            strcmp(comment_probe, "@else") == 0 ||
            strncmp(comment_probe, "@else:", 6) == 0 ||
            strcmp(comment_probe, "@end") == 0 ||
            strncmp(comment_probe, "@cfg(", 5) == 0;
        if (!is_conditional_directive) {
            strip_inline_comment(buf);
        }
        source_lines[num_lines++] = strdup(buf);
    }
    int file_end = num_lines;
    fclose(f);

    /* Post-process: join multi-line continuations WITHIN THIS FILE ONLY */
    for (int i = file_start; i < file_end; i++) {
        /* Count open/close parens and brackets */
        int depth = 0;
        bool in_str = false;
        for (const char *c = source_lines[i]; *c; c++) {
            if (*c == '"' && !in_str) { in_str = true; continue; }
            if (*c == '"' && in_str) { in_str = false; continue; }
            if (*c == '\\' && in_str) { c++; continue; }
            if (in_str) continue;
            if (*c == '(' || *c == '[') depth++;
            if (*c == ')' || *c == ']') depth--;
        }
        if (depth > 0 && (i + 1) < file_end) {
            /* Join with next line(s) until balanced, but stay within file */
            char joined[MAX_LINE * 4] = "";
            strncpy(joined, source_lines[i], sizeof(joined) - 1);
            free(source_lines[i]);
            int j = i + 1;
            while (depth > 0 && j < file_end) {
                /* Never consume the next top-level declaration while joining continuations. */
                const char *next_line = source_lines[j];
                const char *next_trim = next_line;
                bool next_is_top_level = true;
                while (*next_trim == ' ' || *next_trim == '\t') {
                    next_is_top_level = false;
                    next_trim++;
                }
                bool next_is_decl =
                    strncmp(next_trim, "fn ", 3) == 0 ||
                    strncmp(next_trim, "extern fn ", 10) == 0 ||
                    strncmp(next_trim, "struct ", 7) == 0 ||
                    strncmp(next_trim, "class ", 6) == 0 ||
                    strncmp(next_trim, "enum ", 5) == 0 ||
                    strncmp(next_trim, "impl ", 5) == 0;
                if (next_is_top_level && next_is_decl) {
                    break;
                }

                /* Skip leading whitespace manually (trim not yet declared) */
                const char *cont = source_lines[j];
                while (*cont == ' ' || *cont == '\t') cont++;
                /* Append continuation with a space */
                int jl = strlen(joined);
                if (jl < (int)sizeof(joined) - 2) {
                    joined[jl] = ' ';
                    strncpy(joined + jl + 1, cont, sizeof(joined) - jl - 2);
                }
                free(source_lines[j]);
                source_lines[j] = strdup("");
                /* Recount depth on joined content */
                in_str = false;
                for (const char *c = cont; *c; c++) {
                    if (*c == '"' && !in_str) { in_str = true; continue; }
                    if (*c == '"' && in_str) { in_str = false; continue; }
                    if (*c == '\\' && in_str) { c++; continue; }
                    if (in_str) continue;
                    if (*c == '(' || *c == '[') depth++;
                    if (*c == ')' || *c == ']') depth--;
                }
                j++;
            }
            source_lines[i] = strdup(joined);
        }
    }
}

/* ===== String Utilities ===== */
static const char *skip_spaces(const char *s) {
    while (*s == ' ' || *s == '\t') s++;
    return s;
}

static int indent_level(const char *line) {
    int level = 0;
    while (*line == ' ') { level++; line++; }
    while (*line == '\t') { level += 4; line++; }
    return level / 4;
}

static bool starts_with(const char *s, const char *prefix) {
    return strncmp(s, prefix, strlen(prefix)) == 0;
}

static bool ends_with(const char *s, const char *suffix) {
    int slen = strlen(s), suflen = strlen(suffix);
    if (slen < suflen) return false;
    return strcmp(s + slen - suflen, suffix) == 0;
}

#define TRIM_BUFS 8
static char trim_bufs[TRIM_BUFS][MAX_LINE];
static int trim_idx = 0;

static char *trim(const char *s) {
    char *buf = trim_bufs[trim_idx];
    trim_idx = (trim_idx + 1) % TRIM_BUFS;
    while (*s == ' ' || *s == '\t') s++;
    strncpy(buf, s, MAX_LINE-1);
    buf[MAX_LINE-1] = '\0';
    int len = strlen(buf);
    while (len > 0 && (buf[len-1] == ' ' || buf[len-1] == '\t' || buf[len-1] == '\n'))
        buf[--len] = '\0';
    return buf;
}

/* Parse declaration/type owner names and strip generic suffixes like <T, U>. */
static void parse_decl_name(const char *start, char *out, int outsz) {
    if (outsz <= 0) return;
    const char *p = skip_spaces(start ? start : "");
    int n = 0;
    while (*p &&
           *p != ':' &&
           *p != '(' &&
           *p != ' ' &&
           *p != '<' &&
           *p != '[' &&
           *p != ',' &&
           *p != '>') {
        if (n < outsz - 1) out[n++] = *p;
        p++;
    }
    out[n] = '\0';
}

/* Parse impl owner name.
 * - impl Type:
 * - impl Trait for Type:
 * Returns the concrete owner type name (Type), generic suffix stripped. */
static void parse_impl_owner_name(const char *start, char *out, int outsz) {
    if (outsz <= 0) return;
    out[0] = '\0';

    const char *p = skip_spaces(start ? start : "");
    const char *owner_start = p;

    int angle_depth = 0;
    for (const char *it = p; *it; it++) {
        char ch = *it;
        if (ch == '<') {
            angle_depth++;
            continue;
        }
        if (ch == '>') {
            if (angle_depth > 0) angle_depth--;
            continue;
        }
        if (ch == ':' && angle_depth == 0) {
            break;
        }
        if (angle_depth == 0 && strncmp(it, " for ", 5) == 0) {
            owner_start = it + 5;
            break;
        }
    }

    parse_decl_name(owner_start, out, outsz);
}

static void replace_source_line(int idx, const char *value) {
    if (idx < 0 || idx >= num_lines) return;
    free(source_lines[idx]);
    source_lines[idx] = strdup(value ? value : "");
}

static const char *env_or_empty(const char *key) {
    const char *value = getenv(key);
    return value ? value : "";
}

static void trim_copy(const char *src, char *out, int outsz) {
    if (outsz <= 0) return;
    strncpy(out, src ? src : "", outsz - 1);
    out[outsz - 1] = '\0';
    char *t = trim(out);
    if (t != out) memmove(out, t, strlen(t) + 1);
}

static void ascii_lower_copy(const char *src, char *out, int outsz) {
    if (outsz <= 0) return;
    int i = 0;
    for (; src && src[i] && i < outsz - 1; i++) {
        char ch = src[i];
        if (ch >= 'A' && ch <= 'Z') out[i] = (char)(ch - 'A' + 'a');
        else out[i] = ch;
    }
    out[i] = '\0';
}

static void strip_quotes_copy(const char *raw, char *out, int outsz) {
    char tmp[MAX_LINE];
    trim_copy(raw, tmp, sizeof(tmp));
    size_t len = strlen(tmp);
    if (len >= 2) {
        bool is_double = (tmp[0] == '"' && tmp[len - 1] == '"');
        bool is_single = (tmp[0] == '\'' && tmp[len - 1] == '\'');
        if (is_double || is_single) {
            tmp[len - 1] = '\0';
            memmove(tmp, tmp + 1, len - 1);
        }
    }
    strncpy(out, tmp, outsz - 1);
    out[outsz - 1] = '\0';
}

static void normalize_os_token(const char *raw, char *out, int outsz) {
    out[0] = '\0';
    char no_quotes[MAX_LINE];
    strip_quotes_copy(raw, no_quotes, sizeof(no_quotes));
    char value[MAX_LINE];
    ascii_lower_copy(no_quotes, value, sizeof(value));
    if (value[0] == '\0') return;

    if (strcmp(value, "win") == 0 || strcmp(value, "windows") == 0 ||
        strcmp(value, "windows_nt") == 0 || strstr(value, "windows")) {
        strncpy(out, "windows", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "linux") == 0 || strstr(value, "linux")) {
        strncpy(out, "linux", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "mac") == 0 || strcmp(value, "macos") == 0 ||
        strcmp(value, "darwin") == 0 || strstr(value, "darwin") ||
        strstr(value, "mac")) {
        strncpy(out, "macos", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "freebsd") == 0 || strstr(value, "freebsd")) {
        strncpy(out, "freebsd", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "openbsd") == 0 || strstr(value, "openbsd")) {
        strncpy(out, "openbsd", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "netbsd") == 0 || strstr(value, "netbsd")) {
        strncpy(out, "netbsd", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "android") == 0 || strstr(value, "android")) {
        strncpy(out, "android", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "unix") == 0 || strstr(value, "unix")) {
        strncpy(out, "unix", outsz - 1);
        out[outsz - 1] = '\0';
    }
}

static void normalize_arch_token(const char *raw, char *out, int outsz) {
    out[0] = '\0';
    char no_quotes[MAX_LINE];
    strip_quotes_copy(raw, no_quotes, sizeof(no_quotes));
    char value[MAX_LINE];
    ascii_lower_copy(no_quotes, value, sizeof(value));
    if (value[0] == '\0') return;

    if (strcmp(value, "x86_64") == 0 || strcmp(value, "amd64") == 0 ||
        strcmp(value, "x64") == 0 || strstr(value, "x86_64") ||
        strstr(value, "amd64")) {
        strncpy(out, "x86_64", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "x86") == 0 || strcmp(value, "i386") == 0 ||
        strcmp(value, "i686") == 0 || strstr(value, "i386") ||
        strstr(value, "i686")) {
        strncpy(out, "x86", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "aarch64") == 0 || strcmp(value, "arm64") == 0 ||
        strstr(value, "aarch64") || strstr(value, "arm64")) {
        strncpy(out, "aarch64", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "arm") == 0 || strcmp(value, "armv7") == 0 ||
        strcmp(value, "armv6") == 0 || strstr(value, "armv7") ||
        strstr(value, "armv6")) {
        strncpy(out, "arm", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "riscv64") == 0 || strstr(value, "riscv64")) {
        strncpy(out, "riscv64", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "riscv32") == 0 || strstr(value, "riscv32")) {
        strncpy(out, "riscv32", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    if (strcmp(value, "ppc64le") == 0 || strcmp(value, "ppc64el") == 0 ||
        strcmp(value, "powerpc64le") == 0 || strstr(value, "ppc64le") ||
        strstr(value, "powerpc64le")) {
        strncpy(out, "ppc64le", outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
}

static void detect_target_os(char *out, int outsz) {
    out[0] = '\0';
    normalize_os_token(env_or_empty("SIMPLE_TARGET_OS"), out, outsz);
    if (out[0]) return;

    const char *env_keys[] = {"OS", "OSTYPE", "PLATFORM", "UNAME", nullptr};
    for (int i = 0; env_keys[i]; i++) {
        normalize_os_token(env_or_empty(env_keys[i]), out, outsz);
        if (out[0]) return;
    }

#if defined(_WIN32)
    strncpy(out, "windows", outsz - 1);
#elif defined(__APPLE__) && defined(__MACH__)
    strncpy(out, "macos", outsz - 1);
#elif defined(__ANDROID__)
    strncpy(out, "android", outsz - 1);
#elif defined(__FreeBSD__)
    strncpy(out, "freebsd", outsz - 1);
#elif defined(__OpenBSD__)
    strncpy(out, "openbsd", outsz - 1);
#elif defined(__NetBSD__)
    strncpy(out, "netbsd", outsz - 1);
#elif defined(__linux__)
    strncpy(out, "linux", outsz - 1);
#else
    strncpy(out, "unknown", outsz - 1);
#endif
    out[outsz - 1] = '\0';
}

static void detect_target_arch(char *out, int outsz) {
    out[0] = '\0';
    normalize_arch_token(env_or_empty("SIMPLE_TARGET_ARCH"), out, outsz);
    if (out[0]) return;

    const char *env_keys[] = {
        "PROCESSOR_ARCHITECTURE",
        "HOSTTYPE",
        "MACHTYPE",
        "CPU",
        nullptr
    };
    for (int i = 0; env_keys[i]; i++) {
        normalize_arch_token(env_or_empty(env_keys[i]), out, outsz);
        if (out[0]) return;
    }

#if defined(__x86_64__) || defined(_M_X64) || defined(__amd64__)
    strncpy(out, "x86_64", outsz - 1);
#elif defined(__i386__) || defined(_M_IX86)
    strncpy(out, "x86", outsz - 1);
#elif defined(__aarch64__) || defined(_M_ARM64)
    strncpy(out, "aarch64", outsz - 1);
#elif defined(__arm__) || defined(_M_ARM)
    strncpy(out, "arm", outsz - 1);
#elif defined(__riscv) && (__riscv_xlen == 64)
    strncpy(out, "riscv64", outsz - 1);
#elif defined(__riscv) && (__riscv_xlen == 32)
    strncpy(out, "riscv32", outsz - 1);
#elif defined(__powerpc64__) && defined(__BYTE_ORDER__) && (__BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__)
    strncpy(out, "ppc64le", outsz - 1);
#else
    strncpy(out, "unknown", outsz - 1);
#endif
    out[outsz - 1] = '\0';
}

static void detect_target_cpu(char *out, int outsz) {
    out[0] = '\0';
    normalize_arch_token(env_or_empty("SIMPLE_TARGET_CPU"), out, outsz);
    if (out[0]) return;

    normalize_arch_token(env_or_empty("PROCESSOR_IDENTIFIER"), out, outsz);
    if (out[0]) return;

    detect_target_arch(out, outsz);
}

/* Global target info for asm match/assert (populated in preprocess_conditional_directives) */
static char g_host_arch[64];
static char g_host_os[64];

#define MAX_COND_TOKENS 128
#define MAX_COND_TOKEN_LEN 96

typedef struct {
    char tokens[MAX_COND_TOKENS][MAX_COND_TOKEN_LEN];
    int count;
    int pos;
} CondParser;

static void cond_push_token(CondParser *p, const char *token) {
    if (p->count >= MAX_COND_TOKENS) return;
    strncpy(p->tokens[p->count], token, MAX_COND_TOKEN_LEN - 1);
    p->tokens[p->count][MAX_COND_TOKEN_LEN - 1] = '\0';
    p->count++;
}

static void tokenize_condition(const char *condition, CondParser *parser) {
    parser->count = 0;
    parser->pos = 0;
    char current[MAX_COND_TOKEN_LEN];
    int cur_len = 0;

    for (int i = 0; condition && condition[i];) {
        char ch = condition[i];
        bool is_ws = (ch == ' ' || ch == '\t' || ch == '\r');
        if (is_ws) {
            if (cur_len > 0) {
                current[cur_len] = '\0';
                cond_push_token(parser, current);
                cur_len = 0;
            }
            i++;
            continue;
        }

        bool is_paren = (ch == '(' || ch == ')');
        if (is_paren) {
            if (cur_len > 0) {
                current[cur_len] = '\0';
                cond_push_token(parser, current);
                cur_len = 0;
            }
            char one[2] = {ch, '\0'};
            cond_push_token(parser, one);
            i++;
            continue;
        }

        if (ch == '&' && condition[i + 1] == '&') {
            if (cur_len > 0) {
                current[cur_len] = '\0';
                cond_push_token(parser, current);
                cur_len = 0;
            }
            cond_push_token(parser, "&&");
            i += 2;
            continue;
        }

        if (ch == '|' && condition[i + 1] == '|') {
            if (cur_len > 0) {
                current[cur_len] = '\0';
                cond_push_token(parser, current);
                cur_len = 0;
            }
            cond_push_token(parser, "||");
            i += 2;
            continue;
        }

        if (ch == '!') {
            if (cur_len > 0) {
                current[cur_len] = '\0';
                cond_push_token(parser, current);
                cur_len = 0;
            }
            cond_push_token(parser, "!");
            i++;
            continue;
        }

        if (cur_len < MAX_COND_TOKEN_LEN - 1) {
            current[cur_len++] = ch;
        }
        i++;
    }

    if (cur_len > 0) {
        current[cur_len] = '\0';
        cond_push_token(parser, current);
    }
}

static const char *cond_peek(CondParser *p) {
    if (p->pos >= p->count) return "";
    return p->tokens[p->pos];
}

static const char *cond_take(CondParser *p) {
    const char *token = cond_peek(p);
    if (p->pos < p->count) p->pos++;
    return token;
}

static bool eval_key_value_condition(
    const char *key_raw,
    const char *value_raw,
    const char *host_os,
    const char *host_arch,
    const char *host_cpu
) {
    char key[MAX_COND_TOKEN_LEN];
    char value[MAX_COND_TOKEN_LEN];
    strip_quotes_copy(key_raw, key, sizeof(key));
    strip_quotes_copy(value_raw, value, sizeof(value));

    char key_lower[MAX_COND_TOKEN_LEN];
    ascii_lower_copy(key, key_lower, sizeof(key_lower));

    if (strcmp(key_lower, "feature") == 0) {
        return false;
    }
    if (strcmp(key_lower, "os") == 0 || strcmp(key_lower, "platform") == 0) {
        char norm[MAX_COND_TOKEN_LEN];
        normalize_os_token(value, norm, sizeof(norm));
        if (strcmp(norm, "unix") == 0) {
            return strcmp(host_os, "linux") == 0 || strcmp(host_os, "macos") == 0 ||
                   strcmp(host_os, "freebsd") == 0 || strcmp(host_os, "openbsd") == 0 ||
                   strcmp(host_os, "netbsd") == 0 || strcmp(host_os, "android") == 0 ||
                   strcmp(host_os, "unix") == 0;
        }
        return norm[0] != '\0' && strcmp(host_os, norm) == 0;
    }
    if (strcmp(key_lower, "arch") == 0) {
        char norm[MAX_COND_TOKEN_LEN];
        normalize_arch_token(value, norm, sizeof(norm));
        return norm[0] != '\0' && strcmp(host_arch, norm) == 0;
    }
    if (strcmp(key_lower, "cpu") == 0) {
        char norm[MAX_COND_TOKEN_LEN];
        normalize_arch_token(value, norm, sizeof(norm));
        return norm[0] != '\0' && strcmp(host_cpu, norm) == 0;
    }
    return false;
}

static bool eval_atom_condition(
    const char *atom_raw,
    const char *host_os,
    const char *host_arch,
    const char *host_cpu
) {
    char atom[MAX_COND_TOKEN_LEN];
    strip_quotes_copy(atom_raw, atom, sizeof(atom));
    char token[MAX_COND_TOKEN_LEN];
    ascii_lower_copy(atom, token, sizeof(token));
    if (token[0] == '\0') return false;

    if (strcmp(token, "true") == 0) return true;
    if (strcmp(token, "false") == 0) return false;
    if (strcmp(token, "debug") == 0) return true;
    if (strcmp(token, "release") == 0) return false;
    if (strcmp(token, "compiled") == 0) return true;
    if (strcmp(token, "interpreter") == 0) return false;

    if (strcmp(token, "win") == 0 || strcmp(token, "windows") == 0) return strcmp(host_os, "windows") == 0;
    if (strcmp(token, "linux") == 0) return strcmp(host_os, "linux") == 0;
    if (strcmp(token, "mac") == 0 || strcmp(token, "macos") == 0 || strcmp(token, "darwin") == 0) return strcmp(host_os, "macos") == 0;
    if (strcmp(token, "freebsd") == 0) return strcmp(host_os, "freebsd") == 0;
    if (strcmp(token, "openbsd") == 0) return strcmp(host_os, "openbsd") == 0;
    if (strcmp(token, "netbsd") == 0) return strcmp(host_os, "netbsd") == 0;
    if (strcmp(token, "android") == 0) return strcmp(host_os, "android") == 0;
    if (strcmp(token, "unix") == 0) {
        return strcmp(host_os, "linux") == 0 || strcmp(host_os, "macos") == 0 ||
               strcmp(host_os, "freebsd") == 0 || strcmp(host_os, "openbsd") == 0 ||
               strcmp(host_os, "netbsd") == 0 || strcmp(host_os, "android") == 0 ||
               strcmp(host_os, "unix") == 0;
    }

    if (strcmp(token, "x86_64") == 0 || strcmp(token, "amd64") == 0 || strcmp(token, "x64") == 0) return strcmp(host_arch, "x86_64") == 0;
    if (strcmp(token, "x86") == 0 || strcmp(token, "i386") == 0 || strcmp(token, "i686") == 0) return strcmp(host_arch, "x86") == 0;
    if (strcmp(token, "aarch64") == 0 || strcmp(token, "arm64") == 0) return strcmp(host_arch, "aarch64") == 0;
    if (strcmp(token, "arm") == 0 || strcmp(token, "armv7") == 0 || strcmp(token, "armv6") == 0) return strcmp(host_arch, "arm") == 0;
    if (strcmp(token, "riscv64") == 0) return strcmp(host_arch, "riscv64") == 0;
    if (strcmp(token, "riscv32") == 0) return strcmp(host_arch, "riscv32") == 0;
    if (strcmp(token, "ppc64le") == 0 || strcmp(token, "ppc64el") == 0 || strcmp(token, "powerpc64le") == 0) {
        return strcmp(host_arch, "ppc64le") == 0;
    }

    const char *eq2 = strstr(token, "==");
    if (eq2) {
        char key[MAX_COND_TOKEN_LEN];
        char value[MAX_COND_TOKEN_LEN];
        int klen = (int)(eq2 - token);
        if (klen >= MAX_COND_TOKEN_LEN) klen = MAX_COND_TOKEN_LEN - 1;
        strncpy(key, token, klen);
        key[klen] = '\0';
        strncpy(value, eq2 + 2, sizeof(value) - 1);
        value[sizeof(value) - 1] = '\0';
        return eval_key_value_condition(key, value, host_os, host_arch, host_cpu);
    }

    const char *eq1 = strchr(token, '=');
    if (eq1) {
        char key[MAX_COND_TOKEN_LEN];
        char value[MAX_COND_TOKEN_LEN];
        int klen = (int)(eq1 - token);
        if (klen >= MAX_COND_TOKEN_LEN) klen = MAX_COND_TOKEN_LEN - 1;
        strncpy(key, token, klen);
        key[klen] = '\0';
        strncpy(value, eq1 + 1, sizeof(value) - 1);
        value[sizeof(value) - 1] = '\0';
        return eval_key_value_condition(key, value, host_os, host_arch, host_cpu);
    }

    return false;
}

static bool eval_cond_or(CondParser *p, const char *host_os, const char *host_arch, const char *host_cpu);

static bool eval_cond_primary(CondParser *p, const char *host_os, const char *host_arch, const char *host_cpu) {
    const char *tok = cond_peek(p);
    if (strcmp(tok, "(") == 0) {
        cond_take(p);
        bool value = eval_cond_or(p, host_os, host_arch, host_cpu);
        if (strcmp(cond_peek(p), ")") == 0) cond_take(p);
        return value;
    }
    return eval_atom_condition(cond_take(p), host_os, host_arch, host_cpu);
}

static bool eval_cond_not(CondParser *p, const char *host_os, const char *host_arch, const char *host_cpu) {
    const char *tok = cond_peek(p);
    if (strcmp(tok, "!") == 0 || strcmp(tok, "not") == 0) {
        cond_take(p);
        return !eval_cond_not(p, host_os, host_arch, host_cpu);
    }
    return eval_cond_primary(p, host_os, host_arch, host_cpu);
}

static bool eval_cond_and(CondParser *p, const char *host_os, const char *host_arch, const char *host_cpu) {
    bool left = eval_cond_not(p, host_os, host_arch, host_cpu);
    for (int i = 0; i < 1024; i++) {
        const char *tok = cond_peek(p);
        if (strcmp(tok, "&&") != 0 && strcmp(tok, "and") != 0) break;
        cond_take(p);
        bool right = eval_cond_not(p, host_os, host_arch, host_cpu);
        left = left && right;
    }
    return left;
}

static bool eval_cond_or(CondParser *p, const char *host_os, const char *host_arch, const char *host_cpu) {
    bool left = eval_cond_and(p, host_os, host_arch, host_cpu);
    for (int i = 0; i < 1024; i++) {
        const char *tok = cond_peek(p);
        if (strcmp(tok, "||") != 0 && strcmp(tok, "or") != 0) break;
        cond_take(p);
        bool right = eval_cond_and(p, host_os, host_arch, host_cpu);
        left = left || right;
    }
    return left;
}

static bool eval_condition(const char *condition, const char *host_os, const char *host_arch, const char *host_cpu) {
    CondParser parser;
    tokenize_condition(condition, &parser);
    if (parser.count == 0) return false;
    return eval_cond_or(&parser, host_os, host_arch, host_cpu);
}

/* Extract condition from @when(condition): or @cfg(condition) syntax.
   Finds the '(' after the prefix and reads until the matching ')'. */
static void extract_paren_condition(const char *trimmed_line, char *out, int outsz) {
    if (outsz <= 0) return;
    out[0] = '\0';
    const char *p = strchr(trimmed_line, '(');
    if (!p) return;
    p++; /* skip '(' */
    int depth = 1;
    int i = 0;
    while (*p && depth > 0 && i < outsz - 1) {
        if (*p == '(') depth++;
        else if (*p == ')') { depth--; if (depth == 0) break; }
        out[i++] = *p++;
    }
    out[i] = '\0';
    char *t = trim(out);
    if (t != out) memmove(out, t, strlen(t) + 1);
}

static void preprocess_conditional_directives() {
    char host_os[32];
    char host_arch[32];
    char host_cpu[32];
    detect_target_os(host_os, sizeof(host_os));
    detect_target_arch(host_arch, sizeof(host_arch));
    detect_target_cpu(host_cpu, sizeof(host_cpu));

    /* Populate global arch/os for asm match/assert */
    strncpy(g_host_arch, host_arch, sizeof(g_host_arch)-1);
    g_host_arch[sizeof(g_host_arch)-1] = '\0';
    strncpy(g_host_os, host_os, sizeof(g_host_os)-1);
    g_host_os[sizeof(g_host_os)-1] = '\0';

    const int MAX_IF_DEPTH = 128;
    bool stack_parent_active[MAX_IF_DEPTH];
    bool stack_branch_taken[MAX_IF_DEPTH];
    bool stack_branch_active[MAX_IF_DEPTH];
    int depth = 0;
    bool active = true;

    for (int i = 0; i < num_lines; i++) {
        char line_copy[MAX_LINE * 4];
        strncpy(line_copy, source_lines[i], sizeof(line_copy) - 1);
        line_copy[sizeof(line_copy) - 1] = '\0';
        char *t = trim(line_copy);

        bool is_when = starts_with(t, "@when(");
        if (is_when) {
            char cond[MAX_LINE * 2];
            extract_paren_condition(t, cond, sizeof(cond));
            bool parent = active;
            bool cond_ok = eval_condition(cond, host_os, host_arch, host_cpu);
            bool current = parent && cond_ok;

            if (depth < MAX_IF_DEPTH) {
                stack_parent_active[depth] = parent;
                stack_branch_taken[depth] = current;
                stack_branch_active[depth] = current;
                depth++;
            }
            active = current;
            replace_source_line(i, "");
            continue;
        }

        bool is_elif = starts_with(t, "@elif(");
        if (is_elif) {
            if (depth > 0) {
                int idx = depth - 1;
                bool parent = stack_parent_active[idx];
                bool taken = stack_branch_taken[idx];
                bool current = false;
                if (parent && !taken) {
                    char cond[MAX_LINE * 2];
                    extract_paren_condition(t, cond, sizeof(cond));
                    current = eval_condition(cond, host_os, host_arch, host_cpu);
                    if (current) taken = true;
                }
                stack_branch_taken[idx] = taken;
                stack_branch_active[idx] = current;
                active = current;
            }
            replace_source_line(i, "");
            continue;
        }

        if (strcmp(t, "@else") == 0 || starts_with(t, "@else:")) {
            if (depth > 0) {
                int idx = depth - 1;
                bool parent = stack_parent_active[idx];
                bool taken = stack_branch_taken[idx];
                bool current = parent && !taken;
                stack_branch_taken[idx] = taken || current;
                stack_branch_active[idx] = current;
                active = current;
            }
            replace_source_line(i, "");
            continue;
        }

        if (strcmp(t, "@end") == 0) {
            if (depth > 0) depth--;
            if (depth <= 0) active = true;
            else active = stack_branch_active[depth - 1];
            replace_source_line(i, "");
            continue;
        }

        if (!active) {
            replace_source_line(i, "");
        }
    }

    /* Second pass: @cfg(condition) per-declaration conditionals */
    for (int i = 0; i < num_lines; i++) {
        char line_copy[MAX_LINE * 4];
        strncpy(line_copy, source_lines[i], sizeof(line_copy) - 1);
        line_copy[sizeof(line_copy) - 1] = '\0';
        char *t = trim(line_copy);

        if (!starts_with(t, "@cfg(")) continue;

        char cond[MAX_LINE * 2];
        extract_paren_condition(t, cond, sizeof(cond));

        /* Convert @cfg("key", "value") to key=value form */
        char *comma = NULL;
        {
            bool in_str = false;
            for (char *p = cond; *p; p++) {
                if (*p == '"') in_str = !in_str;
                if (*p == ',' && !in_str) { comma = p; break; }
            }
        }
        char eval_buf[MAX_LINE * 2];
        if (comma) {
            *comma = '\0';
            char *key = trim(cond);
            char *val = trim(comma + 1);
            /* Strip quotes */
            int klen = (int)strlen(key);
            if (klen >= 2 && key[0] == '"' && key[klen-1] == '"') { key[klen-1] = '\0'; key++; }
            int vlen = (int)strlen(val);
            if (vlen >= 2 && val[0] == '"' && val[vlen-1] == '"') { val[vlen-1] = '\0'; val++; }
            snprintf(eval_buf, sizeof(eval_buf), "%s=%s", key, val);
        } else {
            strncpy(eval_buf, cond, sizeof(eval_buf) - 1);
            eval_buf[sizeof(eval_buf) - 1] = '\0';
        }

        bool cond_ok = eval_condition(eval_buf, host_os, host_arch, host_cpu);
        if (cond_ok) {
            /* Condition true: blank only the @cfg line, keep declaration */
            replace_source_line(i, "");
        } else {
            /* Condition false: blank @cfg line + following declaration body */
            replace_source_line(i, "");
            /* Determine indentation of the @cfg line */
            int cfg_indent = 0;
            for (const char *p = source_lines[i]; *p == ' ' || *p == '\t'; p++) cfg_indent++;
            /* Blank following lines that are part of the declaration */
            for (int j = i + 1; j < num_lines; j++) {
                const char *jline = source_lines[j];
                if (!jline[0] || jline[0] == '\0') break; /* empty line = end */
                /* Count leading indent */
                int jindent = 0;
                for (const char *p = jline; *p == ' ' || *p == '\t'; p++) jindent++;
                /* If this line has content and deeper indent, or is the first decl line, blank it */
                char *jtrim = trim(line_copy);
                strncpy(line_copy, jline, sizeof(line_copy) - 1);
                line_copy[sizeof(line_copy) - 1] = '\0';
                jtrim = trim(line_copy);
                if (j == i + 1) {
                    /* Always blank the declaration line right after @cfg */
                    replace_source_line(j, "");
                    /* If the declaration line ends with ':', there's a body */
                    int dlen = (int)strlen(jtrim);
                    if (dlen > 0 && jtrim[dlen - 1] == ':') {
                        /* Blank indented body lines */
                        for (int k = j + 1; k < num_lines; k++) {
                            const char *kline = source_lines[k];
                            if (!kline[0]) break;
                            int kindent = 0;
                            for (const char *p = kline; *p == ' ' || *p == '\t'; p++) kindent++;
                            if (kindent > jindent) {
                                replace_source_line(k, "");
                            } else {
                                break;
                            }
                        }
                    }
                    break;
                }
            }
        }
    }
}

/* Strip inline # comments (not inside strings) */
static void strip_inline_comment(char *line) {
    bool in_str = false;
    char quote = 0;
    for (int i = 0; line[i]; i++) {
        if (in_str) {
            if (line[i] == '\\') { i++; continue; }
            if (line[i] == quote) in_str = false;
        } else {
            if (line[i] == '"' || line[i] == '\'') { in_str = true; quote = line[i]; }
            else if (line[i] == '#') {
                /* Trim trailing spaces before the comment */
                int j = i;
                while (j > 0 && (line[j-1] == ' ' || line[j-1] == '\t')) j--;
                line[j] = '\0';
                return;
            }
        }
    }
}

/* Parse a full Simple string literal (or raw r"...") into plain text.
 * Returns true on success, false if input is not exactly one literal. */
static bool parse_simple_string_literal_full(const char *s, char *out, int outsz) {
    const char *p = skip_spaces(s);
    bool is_raw = false;
    if (p[0] == 'r' && (p[1] == '"' || p[1] == '\'')) {
        is_raw = true;
        p++;
    }
    if (*p != '"' && *p != '\'') return false;
    char quote = *p++;
    int oi = 0;
    while (*p && *p != quote) {
        if (!is_raw && *p == '\\' && p[1]) {
            p++;
            char esc = *p++;
            if (esc == 'n') out[oi++] = '\n';
            else if (esc == 't') out[oi++] = '\t';
            else if (esc == 'r') out[oi++] = '\r';
            else if (esc == '0') {
                if (oi < outsz - 2) {
                    out[oi++] = '\\';
                    out[oi++] = '0';
                } else if (oi < outsz - 1) {
                    out[oi++] = '0';
                }
            }
            else out[oi++] = esc;
        } else {
            out[oi++] = *p++;
        }
        if (oi >= outsz - 1) break;
    }
    if (*p != quote) return false;
    p++;
    p = skip_spaces(p);
    if (*p != '\0') return false;
    out[oi] = '\0';
    return true;
}

static void c_escape_string_text(const char *src, char *dst, int dstsz) {
    int di = 0;
    for (int si = 0; src[si] && di < dstsz - 1; si++) {
        unsigned char ch = (unsigned char)src[si];
        if (ch == '\\') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = '\\';
        } else if (ch == '"') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = '"';
        } else if (ch == '\n') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = 'n';
        } else if (ch == '\t') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = 't';
        } else if (ch == '\r') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = 'r';
        } else if (ch == '\0') {
            if (di + 2 >= dstsz) break;
            dst[di++] = '\\';
            dst[di++] = '0';
        } else {
            dst[di++] = (char)ch;
        }
    }
    dst[di] = '\0';
}

static void normalize_asm_line(const char *src, char *out, int outsz) {
    char parsed[MAX_LINE];
    if (parse_simple_string_literal_full(src, parsed, sizeof(parsed))) {
        strncpy(out, parsed, outsz - 1);
        out[outsz - 1] = '\0';
        return;
    }
    strncpy(out, trim(src), outsz - 1);
    out[outsz - 1] = '\0';
}

static void asm_append_line(char *acc, int accsz, const char *line) {
    if (!line || line[0] == '\0') return;
    if (acc[0] != '\0') {
        strncat(acc, "\n", accsz - strlen(acc) - 1);
    }
    strncat(acc, line, accsz - strlen(acc) - 1);
}

static void emit_asm_stmt(const char *asm_text, int c_indent) {
    char escaped[MAX_ASM_TEXT];
    c_escape_string_text(asm_text ? asm_text : "", escaped, sizeof(escaped));
    emit_indent(c_indent);
    emit("asm volatile(\"%s\");\n", escaped);
}

/* ===== Asm Match/Assert Support ===== */

struct AsmTargetSpec {
    char archs[8][64]; int num_archs;
    char os[64]; bool has_os;
    char abi[64]; bool has_abi;
    char backend[64]; bool has_backend;
    char ver_op[4][16]; int ver_val[4]; int num_ver; /* up to 4 version constraints */
};

/* Parse [arch | arch2, os, abi, backend >= ver] from a string.
 * Input s should be the content between [ and ] (brackets already stripped). */
static bool parse_asm_target_spec(const char *s, AsmTargetSpec *out) {
    memset(out, 0, sizeof(*out));
    if (!s || s[0] == '\0') return false;

    /* Tokenize by comma first to get positional fields */
    char buf[512];
    strncpy(buf, s, sizeof(buf)-1); buf[sizeof(buf)-1] = '\0';

    char *fields[4]; int nfields = 0;
    char *p = buf;
    while (*p && nfields < 4) {
        while (*p == ' ') p++;
        fields[nfields] = p;
        /* find comma or end */
        char *comma = strchr(p, ',');
        if (comma) { *comma = '\0'; p = comma + 1; } else { p += strlen(p); }
        nfields++;
    }

    /* Field 0: arch(es) with | grouping */
    if (nfields < 1) return false;
    {
        char arch_buf[256];
        strncpy(arch_buf, fields[0], sizeof(arch_buf)-1); arch_buf[sizeof(arch_buf)-1] = '\0';
        char *ap = arch_buf;
        while (*ap && out->num_archs < 8) {
            while (*ap == ' ') ap++;
            char *pipe = strchr(ap, '|');
            char *end = pipe ? pipe : ap + strlen(ap);
            /* trim trailing spaces */
            char *te = end - 1;
            while (te > ap && *te == ' ') { *te = '\0'; te--; }
            if (pipe) *pipe = '\0';
            if (*ap) {
                strncpy(out->archs[out->num_archs], ap, 63);
                out->archs[out->num_archs][63] = '\0';
                out->num_archs++;
            }
            ap = pipe ? pipe + 1 : end;
        }
    }

    /* Field 1: os */
    if (nfields >= 2) {
        const char *f = skip_spaces(fields[1]);
        if (f[0] && strcmp(f, "_") != 0) {
            strncpy(out->os, f, 63); out->os[63] = '\0';
            out->has_os = true;
        }
    }

    /* Field 2: abi */
    if (nfields >= 3) {
        const char *f = skip_spaces(fields[2]);
        if (f[0] && strcmp(f, "_") != 0) {
            strncpy(out->abi, f, 63); out->abi[63] = '\0';
            out->has_abi = true;
        }
    }

    /* Field 3: backend [version constraints] */
    if (nfields >= 4) {
        char be_buf[256];
        strncpy(be_buf, fields[3], sizeof(be_buf)-1); be_buf[sizeof(be_buf)-1] = '\0';
        char *bp = be_buf;
            while (*bp == ' ') bp++;
        if (*bp && strcmp(bp, "_") != 0) {
            /* Extract backend name (first word) */
            char *sp = bp;
            while (*sp && *sp != ' ' && *sp != '>' && *sp != '<' && *sp != '=' && *sp != '~') sp++;
            char saved = *sp; *sp = '\0';
            strncpy(out->backend, bp, 63); out->backend[63] = '\0';
            out->has_backend = true;
            *sp = saved;

            /* Parse version constraints */
            char *vp = sp;
            while (*vp && out->num_ver < 4) {
                while (*vp == ' ') vp++;
                if (!*vp) break;
                if (vp[0] == '>' && vp[1] == '=') {
                    strncpy(out->ver_op[out->num_ver], ">=", 15);
                    vp += 2; while (*vp == ' ') vp++;
                    out->ver_val[out->num_ver] = atoi(vp);
                    while (*vp >= '0' && *vp <= '9') vp++;
                    out->num_ver++;
                } else if (vp[0] == '=' && vp[1] == '=') {
                    strncpy(out->ver_op[out->num_ver], "==", 15);
                    vp += 2; while (*vp == ' ') vp++;
                    out->ver_val[out->num_ver] = atoi(vp);
                    while (*vp >= '0' && *vp <= '9') vp++;
                    out->num_ver++;
                } else if (vp[0] == '<') {
                    strncpy(out->ver_op[out->num_ver], "<", 15);
                    vp += 1; while (*vp == ' ') vp++;
                    out->ver_val[out->num_ver] = atoi(vp);
                    while (*vp >= '0' && *vp <= '9') vp++;
                    out->num_ver++;
                } else if (vp[0] == '~' && vp[1] == '=') {
                    strncpy(out->ver_op[out->num_ver], "~=", 15);
                    vp += 2; while (*vp == ' ') vp++;
                    out->ver_val[out->num_ver] = atoi(vp);
                    while (*vp >= '0' && *vp <= '9') vp++;
                    out->num_ver++;
                } else {
                    break;
                }
            }
        }
    }

    return out->num_archs > 0;
}

/* Normalize arch name for comparison */
static void normalize_spec_arch(const char *in, char *out, int outsz) {
    char lower[64];
    int i = 0;
    for (; in[i] && i < 63; i++) lower[i] = (char)tolower((unsigned char)in[i]);
    lower[i] = '\0';

    if (strcmp(lower, "x86-64") == 0 || strcmp(lower, "amd64") == 0 || strcmp(lower, "x64") == 0) {
        strncpy(out, "x86_64", outsz-1);
    } else if (strcmp(lower, "arm64") == 0) {
        strncpy(out, "aarch64", outsz-1);
    } else if (strcmp(lower, "armv7") == 0 || strcmp(lower, "arm32") == 0) {
        strncpy(out, "arm", outsz-1);
    } else if (strcmp(lower, "riscv32gc") == 0 || strcmp(lower, "rv32") == 0) {
        strncpy(out, "riscv32", outsz-1);
    } else if (strcmp(lower, "riscv64gc") == 0 || strcmp(lower, "rv64") == 0) {
        strncpy(out, "riscv64", outsz-1);
    } else if (strcmp(lower, "i686") == 0 || strcmp(lower, "i386") == 0) {
        strncpy(out, "x86", outsz-1);
    } else if (strcmp(lower, "wasm") == 0) {
        strncpy(out, "wasm32", outsz-1);
    } else {
        strncpy(out, lower, outsz-1);
    }
    out[outsz-1] = '\0';
}

static bool match_asm_target_spec(const AsmTargetSpec *spec) {
    /* Check arch */
    bool arch_ok = false;
    for (int i = 0; i < spec->num_archs; i++) {
        char norm_spec[64], norm_host[64];
        normalize_spec_arch(spec->archs[i], norm_spec, sizeof(norm_spec));
        normalize_spec_arch(g_host_arch, norm_host, sizeof(norm_host));
        if (strcmp(norm_spec, norm_host) == 0) { arch_ok = true; break; }
    }
    if (!arch_ok) return false;

    /* Check os */
    if (spec->has_os) {
        char lower_spec[64], lower_host[64];
        int si;
        for (si = 0; spec->os[si] && si < 63; si++) lower_spec[si] = (char)tolower((unsigned char)spec->os[si]);
        lower_spec[si] = '\0';
        int hi;
        for (hi = 0; g_host_os[hi] && hi < 63; hi++) lower_host[hi] = (char)tolower((unsigned char)g_host_os[hi]);
        lower_host[hi] = '\0';
        if (strcmp(lower_spec, lower_host) != 0) return false;
    }

    /* Version constraints — seed doesn't know backend version, skip */
    return true;
}

/* Parse content between brackets from source line like "case [x86_64, linux]:" */
static bool extract_bracket_content(const char *s, char *out, int outsz) {
    const char *open = strchr(s, '[');
    if (!open) return false;
    const char *close = strchr(open, ']');
    if (!close) return false;
    int len = (int)(close - open - 1);
    if (len < 0 || len >= outsz) return false;
    strncpy(out, open + 1, len);
    out[len] = '\0';
    return true;
}

/* Parse compile_error("message") and extract the message */
static bool parse_compile_error_msg(const char *s, char *out, int outsz) {
    const char *p = skip_spaces(s);
    if (!starts_with(p, "compile_error(")) return false;
    p += 14; /* skip compile_error( */
    while (*p == ' ') p++;
    if (*p == '"' || *p == '\'') {
        char quote = *p++;
        int oi = 0;
        while (*p && *p != quote && oi < outsz - 1) {
            out[oi++] = *p++;
        }
        out[oi] = '\0';
        return true;
    }
    return false;
}

/* Rename C++ keywords that can't be handled by #define (char, return, etc.) */
static void sanitize_cpp_name(char *name) {
    /* Rename C++ keywords used as identifiers */
    if (strcmp(name, "char") == 0 || strcmp(name, "return") == 0 ||
        strcmp(name, "signed") == 0 || strcmp(name, "unsigned") == 0 ||
        strcmp(name, "short") == 0 || strcmp(name, "long") == 0 ||
        strcmp(name, "auto") == 0 || strcmp(name, "volatile") == 0 ||
        strcmp(name, "this") == 0 || strcmp(name, "inline") == 0 ||
        strcmp(name, "mutable") == 0 || strcmp(name, "explicit") == 0 ||
        strcmp(name, "typedef") == 0 || strcmp(name, "static") == 0 ||
        strcmp(name, "const") == 0 || strcmp(name, "extern") == 0 ||
        strcmp(name, "int") == 0 || strcmp(name, "float") == 0 ||
        strcmp(name, "double") == 0 || strcmp(name, "void") == 0 ||
        strcmp(name, "bool") == 0 || strcmp(name, "true") == 0 ||
        strcmp(name, "false") == 0 || strcmp(name, "struct") == 0 ||
        strcmp(name, "switch") == 0 || strcmp(name, "break") == 0 ||
        strcmp(name, "continue") == 0 || strcmp(name, "default") == 0 ||
        strcmp(name, "do") == 0 || strcmp(name, "while") == 0 ||
        strcmp(name, "for") == 0 || strcmp(name, "goto") == 0 ||
        strcmp(name, "if") == 0 || strcmp(name, "else") == 0 ||
        strcmp(name, "sizeof") == 0 || strcmp(name, "enum") == 0) {
        int len = strlen(name);
        name[len] = '_';
        name[len+1] = '\0';
    }
}

/* Convert arbitrary Simple token/type text into a safe C++ identifier fragment. */
static void sanitize_cpp_ident_fragment(const char *src, char *dst, int dstsz) {
    if (!src || dstsz <= 1) return;
    int j = 0;
    if (*src >= '0' && *src <= '9') {
        dst[j++] = '_';
    }
    for (int i = 0; src[i] && j < dstsz - 1; i++) {
        unsigned char c = (unsigned char)src[i];
        if ((c >= 'a' && c <= 'z') ||
            (c >= 'A' && c <= 'Z') ||
            (c >= '0' && c <= '9') ||
            c == '_') {
            dst[j++] = (char)c;
        } else {
            dst[j++] = '_';
        }
    }
    dst[j] = '\0';
    if (dst[0] == '\0') {
        strncpy(dst, "_", dstsz - 1);
        dst[dstsz - 1] = '\0';
    }
    sanitize_cpp_name(dst);
}

/* ===== Struct Registry ===== */
typedef struct {
    char name[MAX_IDENT];
    int field_count;
    char field_names[MAX_FIELDS][MAX_IDENT];
    char field_stypes[MAX_FIELDS][MAX_IDENT]; /* Simple types */
} StructInfo;

static StructInfo structs[MAX_STRUCTS];
static int num_structs = 0;

static StructInfo *find_struct(const char *name) {
    for (int i = 0; i < num_structs; i++) {
        if (strcmp(structs[i].name, name) == 0) return &structs[i];
    }
    return nullptr;
}

/* ===== Enum Registry ===== */
typedef struct {
    char name[MAX_IDENT];
    int variant_count;
    char variants[MAX_VARIANTS][MAX_IDENT];
} EnumInfo;

static EnumInfo enums[MAX_ENUMS];
static int num_enums = 0;

static EnumInfo *find_enum(const char *name) {
    for (int i = 0; i < num_enums; i++) {
        if (strcmp(enums[i].name, name) == 0) return &enums[i];
    }
    return nullptr;
}

/* Check if an identifier is an enum variant */
static const char *find_variant_enum(const char *variant) {
    for (int i = 0; i < num_enums; i++) {
        for (int j = 0; j < enums[i].variant_count; j++) {
            if (strcmp(enums[i].variants[j], variant) == 0)
                return enums[i].name;
        }
    }
    return nullptr;
}

/* ===== Option Type Registry ===== */
/* Tracks which Option<T> types are needed, generates C++ structs with constructors */
#define MAX_OPTION_TYPES 4096
typedef struct {
    char simple_base[MAX_IDENT];  /* Base Simple type: "text", "i64", "MyStruct" */
    char cpp_base[MAX_IDENT];     /* Base C++ type: "const char*", "int64_t", etc. */
    char option_name[MAX_IDENT];  /* C++ struct name: "Option_text", etc. */
} OptionTypeInfo;

static OptionTypeInfo option_types[MAX_OPTION_TYPES];
static int num_option_types = 0;
static bool option_registry_full_warned = false;

/* ===== Result Type Registry ===== */
/* Tracks which Result<T, E> types are needed, generates C++ structs */
#define MAX_RESULT_TYPES 4096
typedef struct {
    char ok_type[MAX_IDENT];    /* Success type T */
    char err_type[MAX_IDENT];   /* Error type E */
    char cpp_ok[MAX_IDENT];     /* C++ ok type */
    char cpp_err[MAX_IDENT];    /* C++ err type */
    char result_name[MAX_IDENT]; /* C++ struct name: "Result_T_E" */
} ResultTypeInfo;

static ResultTypeInfo result_types[MAX_RESULT_TYPES];
static int num_result_types = 0;
static bool result_registry_full_warned = false;

static bool type_is_option(const char *stype) {
    int len = strlen(stype);
    return len > 1 && stype[len-1] == '?';
}

static void option_base_stype(const char *stype, char *base, int basesz) {
    int len = strlen(stype);
    if (len > 1 && stype[len-1] == '?') {
        int blen = len - 1;
        if (blen >= basesz) blen = basesz - 1;
        strncpy(base, stype, blen);
        base[blen] = '\0';
    } else {
        strncpy(base, stype, basesz - 1);
        base[basesz - 1] = '\0';
    }
}

/* Extract type parameter from generic syntax like Option<T> → T */
static bool extract_generic_param(const char *stype, char *param, int param_sz) {
    const char *lt = strchr(stype, '<');
    const char *gt = strrchr(stype, '>');
    if (!lt || !gt || gt <= lt) return false;

    int param_len = gt - lt - 1;
    if (param_len <= 0 || param_len >= param_sz) return false;

    strncpy(param, lt + 1, param_len);
    param[param_len] = '\0';
    return true;
}

/* Extract two type parameters from generic syntax like Result<T, E> → T, E */
static bool extract_two_generic_params(const char *stype, char *param1, int p1sz, char *param2, int p2sz) {
    const char *lt = strchr(stype, '<');
    const char *gt = strrchr(stype, '>');
    if (!lt || !gt || gt <= lt) return false;

    /* Find comma separator */
    const char *comma = strchr(lt, ',');
    if (!comma || comma >= gt) return false;

    /* Extract first parameter */
    int p1_len = comma - lt - 1;
    if (p1_len <= 0 || p1_len >= p1sz) return false;
    strncpy(param1, lt + 1, p1_len);
    param1[p1_len] = '\0';
    /* Trim spaces */
    while (p1_len > 0 && param1[p1_len-1] == ' ') param1[--p1_len] = '\0';

    /* Extract second parameter */
    const char *p2_start = comma + 1;
    while (*p2_start == ' ') p2_start++;
    int p2_len = gt - p2_start;
    if (p2_len <= 0 || p2_len >= p2sz) return false;
    strncpy(param2, p2_start, p2_len);
    param2[p2_len] = '\0';
    /* Trim spaces */
    while (p2_len > 0 && param2[p2_len-1] == ' ') param2[--p2_len] = '\0';

    return true;
}

/* Build a stable and valid C++ Option_* type name from Simple and C++ base type text. */
static void build_option_type_name(const char *simple_base, const char *cpp_base, char *out, int outsz) {
    if (!simple_base || !cpp_base || !out || outsz <= 0) return;

    if (simple_base[0] == '[') {
        char frag[MAX_IDENT];
        sanitize_cpp_ident_fragment(simple_base, frag, sizeof(frag));
        snprintf(out, outsz, "Option_%s", frag);
        return;
    }

    char frag[MAX_IDENT];
    if (strncmp(simple_base, "fn(", 3) == 0 ||
        strncmp(simple_base, "Fn<", 3) == 0 ||
        strchr(simple_base, '<')) {
        /* Generic/function-based Option names are derived from resolved C++ base type. */
        sanitize_cpp_ident_fragment(cpp_base, frag, sizeof(frag));
    } else {
        sanitize_cpp_ident_fragment(simple_base, frag, sizeof(frag));
    }

    snprintf(out, outsz, "Option_%s", frag);
}

/* ===== Type Conversion ===== */
/* Forward declarations (used by simple_type_to_cpp before definition) */
static bool type_is_struct_array(const char *stype);
static void struct_array_elem_type(const char *stype, char *out, int outsz);

static const char *simple_type_to_cpp(const char *stype) {
    /* Option types: text?, i64?, StructName?, etc. */
    if (type_is_option(stype)) {
        char base[MAX_IDENT];
        option_base_stype(stype, base, sizeof(base));
        /* Register this option type if not already registered */
        bool found = false;
        for (int i = 0; i < num_option_types; i++) {
            if (strcmp(option_types[i].simple_base, base) == 0) { found = true; break; }
        }
        if (!found) {
            if (num_option_types < MAX_OPTION_TYPES) {
                OptionTypeInfo *oi = &option_types[num_option_types];
                strcpy(oi->simple_base, base);
                /* Recursive call for base type */
                strcpy(oi->cpp_base, simple_type_to_cpp(base));
                build_option_type_name(base, oi->cpp_base, oi->option_name, MAX_IDENT);
                num_option_types++;
            } else if (!option_registry_full_warned) {
                fprintf(stderr, "WARNING: Option type registry full (%d)\n", MAX_OPTION_TYPES);
                option_registry_full_warned = true;
            }
        }
        /* Return option struct name */
        static char option_buf[MAX_IDENT];
        /* Prefer registered name when available to keep naming stable across recursion. */
        for (int i = 0; i < num_option_types; i++) {
            if (strcmp(option_types[i].simple_base, base) == 0) {
                snprintf(option_buf, sizeof(option_buf), "%s", option_types[i].option_name);
                return option_buf;
            }
        }
        build_option_type_name(base, simple_type_to_cpp(base), option_buf, sizeof(option_buf));
        return option_buf;
    }
    if (strcmp(stype, "i64") == 0) return "int64_t";
    if (strcmp(stype, "i32") == 0) return "int32_t";
    if (strcmp(stype, "u8") == 0) return "uint8_t";
    if (strcmp(stype, "u32") == 0) return "uint32_t";
    if (strcmp(stype, "u64") == 0) return "uint64_t";
    if (strcmp(stype, "f64") == 0) return "double";
    if (strcmp(stype, "f32") == 0) return "float";
    if (strcmp(stype, "text") == 0) return "const char*";
    if (strcmp(stype, "bool") == 0) return "bool";
    if (strcmp(stype, "void") == 0) return "void";
    /* Array types → SplArray* or std::vector<StructType> for struct arrays */
    if (stype[0] == '[') {
        if (type_is_struct_array(stype)) {
            static char vec_buf[MAX_IDENT];
            char elem[MAX_IDENT];
            struct_array_elem_type(stype, elem, sizeof(elem));
            snprintf(vec_buf, sizeof(vec_buf), "std::vector<%s>", elem);
            return vec_buf;
        }
        return "SplArray*";
    }
    /* Check if it's a known struct type → pass as struct */
    if (find_struct(stype)) {
        /* Return struct name directly (value type) */
        static char struct_type_buf[MAX_IDENT];
        snprintf(struct_type_buf, sizeof(struct_type_buf), "%s", stype);
        return struct_type_buf;
    }
    /* Check if enum type */
    if (find_enum(stype)) return "int64_t";
    /* Dict types → SplDict* */
    if (strncmp(stype, "Dict<", 5) == 0 || strncmp(stype, "Dict", 4) == 0) return "SplDict*";
    /* Generic container types */
    if (strncmp(stype, "List<", 5) == 0 || strncmp(stype, "Set<", 4) == 0 ||
        strncmp(stype, "Map<", 4) == 0) return "SplArray*";
    /* Option<T> generic syntax - monomorphize to Option_T */
    if (strncmp(stype, "Option<", 7) == 0) {
        char param[MAX_IDENT];
        if (extract_generic_param(stype, param, sizeof(param))) {
            /* Register this option type if not already registered */
            bool found = false;
            for (int i = 0; i < num_option_types; i++) {
                if (strcmp(option_types[i].simple_base, param) == 0) { found = true; break; }
            }
            if (!found) {
                if (num_option_types < MAX_OPTION_TYPES) {
                    OptionTypeInfo *oi = &option_types[num_option_types];
                    strcpy(oi->simple_base, param);
                    /* Recursive call for base type */
                    strcpy(oi->cpp_base, simple_type_to_cpp(param));
                    build_option_type_name(param, oi->cpp_base, oi->option_name, MAX_IDENT);
                    num_option_types++;
                } else if (!option_registry_full_warned) {
                    fprintf(stderr, "WARNING: Option type registry full (%d)\n", MAX_OPTION_TYPES);
                    option_registry_full_warned = true;
                }
            }
            /* Return option struct name */
            static char option_buf[MAX_IDENT];
            for (int i = 0; i < num_option_types; i++) {
                if (strcmp(option_types[i].simple_base, param) == 0) {
                    snprintf(option_buf, sizeof(option_buf), "%s", option_types[i].option_name);
                    return option_buf;
                }
            }
            build_option_type_name(param, simple_type_to_cpp(param), option_buf, sizeof(option_buf));
            return option_buf;
        }
    }
    /* Result<T, E> generic syntax - monomorphize to Result_T_E */
    if (strncmp(stype, "Result<", 7) == 0) {
        char ok_type[MAX_IDENT], err_type[MAX_IDENT];
        if (extract_two_generic_params(stype, ok_type, sizeof(ok_type), err_type, sizeof(err_type))) {
            /* Register this result type if not already registered */
            bool found = false;
            for (int i = 0; i < num_result_types; i++) {
                if (strcmp(result_types[i].ok_type, ok_type) == 0 &&
                    strcmp(result_types[i].err_type, err_type) == 0) {
                    found = true;
                    break;
                }
            }
            if (!found) {
                if (num_result_types < MAX_RESULT_TYPES) {
                    ResultTypeInfo *ri = &result_types[num_result_types];
                    strcpy(ri->ok_type, ok_type);
                    strcpy(ri->err_type, err_type);
                    strcpy(ri->cpp_ok, simple_type_to_cpp(ok_type));
                    strcpy(ri->cpp_err, simple_type_to_cpp(err_type));
                    char ok_id[MAX_IDENT], err_id[MAX_IDENT];
                    sanitize_cpp_ident_fragment(ok_type, ok_id, sizeof(ok_id));
                    sanitize_cpp_ident_fragment(err_type, err_id, sizeof(err_id));
                    snprintf(ri->result_name, MAX_IDENT, "Result_%s_%s", ok_id, err_id);
                    fprintf(stderr, "Registered Result type: %s\n", ri->result_name);
                    num_result_types++;
                } else if (!result_registry_full_warned) {
                    fprintf(stderr, "WARNING: Result type registry full (%d)\n", MAX_RESULT_TYPES);
                    result_registry_full_warned = true;
                }
            }
            /* Return result struct name */
            static char result_buf[MAX_IDENT];
            char ok_id[MAX_IDENT], err_id[MAX_IDENT];
            sanitize_cpp_ident_fragment(ok_type, ok_id, sizeof(ok_id));
            sanitize_cpp_ident_fragment(err_type, err_id, sizeof(err_id));
            snprintf(result_buf, sizeof(result_buf), "Result_%s_%s", ok_id, err_id);
            return result_buf;
        }
    }
    /* Common generic types that Simple uses but aren't structs */
    if (strcmp(stype, "Result") == 0) return "int64_t"; /* bare Result without type params */
    if (strcmp(stype, "Option") == 0) return "int64_t"; /* bare Option without type param */
    if (strncmp(stype, "Effect<", 7) == 0 || strcmp(stype, "Effect") == 0) return "int64_t";
    if (strcmp(stype, "Any") == 0) return "int64_t";
    if (strncmp(stype, "Iterator<", 9) == 0) return "int64_t";
    /* Function types: fn() -> T or fn(A, B) -> T */
    /* Use typedef names to avoid C++ function pointer syntax issues */
    if (strncmp(stype, "fn(", 3) == 0) {
        const char *arrow = strstr(stype, "->");
        const char *rparen = strchr(stype, ')');

        if (rparen && arrow && arrow > rparen) {
            /* Extract return type after -> */
            const char *ret_start = arrow + 2;
            while (*ret_start == ' ') ret_start++;
            char ret_type[MAX_IDENT];
            int ret_len = 0;
            int angle_depth = 0;
            /* Parse return type, handling nested generics like Option<Result<T, E>> */
            const char *p = ret_start;
            while (*p && ret_len < MAX_IDENT - 1) {
                char c = *p;
                if (c == '<') {
                    angle_depth++;
                    ret_type[ret_len++] = c;
                } else if (c == '>') {
                    angle_depth--;
                    ret_type[ret_len++] = c;
                    if (angle_depth == 0) break; /* End of return type */
                } else if (c == ' ' && angle_depth == 0) {
                    break; /* Space outside brackets ends type */
                } else {
                    ret_type[ret_len++] = c;
                }
                p++;
            }
            ret_type[ret_len] = '\0';

            /* Convert return type through type system first for proper Option/Result handling */
            const char *cpp_ret_type = simple_type_to_cpp(ret_type);

            /* Use typedef name: FnPtr_RetType */
            static char fn_typedef_buf[MAX_IDENT * 2];
            if (strcmp(ret_type, "Any") == 0 || strcmp(ret_type, "i64") == 0 || strcmp(cpp_ret_type, "int64_t") == 0)
                return "FnPtr_i64";
            else if (strcmp(ret_type, "text") == 0 || strcmp(cpp_ret_type, "const char*") == 0)
                return "FnPtr_text";
            else if (strcmp(ret_type, "void") == 0)
                return "FnPtr_void";
            else if (strcmp(ret_type, "bool") == 0)
                return "FnPtr_bool";
            else if (ret_type[0] == '[' || strcmp(cpp_ret_type, "SplArray*") == 0) {
                /* Array return type: fn() -> [T] */
                return "FnPtr_array";
            } else if (strstr(cpp_ret_type, "Option_") || strstr(cpp_ret_type, "Result_")) {
                /* Complex generic types: use int64_t fallback (all fn pointers are int64_t at runtime) */
                return "int64_t";
            } else {
                /* Use cpp_ret_type which is already sanitized */
                snprintf(fn_typedef_buf, sizeof(fn_typedef_buf), "FnPtr_%s", cpp_ret_type);
                return fn_typedef_buf;
            }
        }
        /* Fallback */
        return "FnPtr_i64";
    }
    if (strncmp(stype, "Fn<", 3) == 0) return "FnPtr_i64"; /* Generic Fn<...> */
    /* Default fallback */
    return "int64_t";
}

/* Check if a simple type is a struct type */
static bool type_is_struct(const char *stype) {
    return find_struct(stype) != nullptr;
}

/* ===== Function Registry ===== */
typedef struct {
    char name[MAX_IDENT];
    char ret_type[MAX_IDENT];    /* C++ return type */
    char simple_ret[MAX_IDENT];  /* Simple return type */
    int param_count;
    char param_names[MAX_PARAMS][MAX_IDENT];
    char param_types[MAX_PARAMS][MAX_IDENT];   /* C++ types */
    char param_stypes[MAX_PARAMS][MAX_IDENT];  /* Simple types */
    bool is_extern;
    char owner_struct[MAX_IDENT]; /* Non-empty if this is a method */
    bool is_mutable;              /* 'me' method (mutable self) */
    bool is_static_method;        /* static fn in impl block */
    bool emitted;                 /* Already emitted in code gen */
} FuncInfo;

static FuncInfo funcs[MAX_FUNCS];
static int num_funcs = 0;
static bool has_main_func = false;

static FuncInfo *find_func(const char *name) {
    for (int i = 0; i < num_funcs; i++) {
        if (strcmp(funcs[i].name, name) == 0) return &funcs[i];
    }
    return nullptr;
}

/* Find a method: looks for StructName__method_name */
static FuncInfo *find_method(const char *struct_name, const char *method_name) {
    char mangled[MAX_IDENT * 2];
    snprintf(mangled, sizeof(mangled), "%s__%s", struct_name, method_name);
    return find_func(mangled);
}

/* ===== Variable Type Registry ===== */
typedef struct {
    char name[MAX_IDENT];
    char stype[MAX_IDENT];
    int scope_depth;
} VarInfo;

#define MAX_VARS 8192
static VarInfo vars[MAX_VARS];
static int num_vars = 0;
static int current_scope = 0;

/* Tracks the current struct name when translating impl method bodies */
static char current_impl_struct[MAX_IDENT] = "";

static void add_var(const char *name, const char *stype) {
    if (num_vars < MAX_VARS) {
        strncpy(vars[num_vars].name, name, MAX_IDENT-1);
        strncpy(vars[num_vars].stype, stype, MAX_IDENT-1);
        vars[num_vars].scope_depth = current_scope;
        num_vars++;
    }
}

static const char *find_var_type(const char *name) {
    for (int i = num_vars - 1; i >= 0; i--) {
        if (strcmp(vars[i].name, name) == 0) return vars[i].stype;
    }
    /* Check self.field pattern when inside impl block */
    if (current_impl_struct[0] != '\0' && starts_with(name, "self.")) {
        const char *field = name + 5;
        StructInfo *si = find_struct(current_impl_struct);
        if (si) {
            for (int i = 0; i < si->field_count; i++) {
                if (strcmp(si->field_names[i], field) == 0)
                    return si->field_stypes[i];
            }
        }
    }
    /* Check obj.field pattern: look up obj type then field type in struct */
    const char *dot = strchr(name, '.');
    if (dot && dot != name) {
        char obj_name[MAX_IDENT];
        int olen = (int)(dot - name);
        if (olen >= MAX_IDENT) olen = MAX_IDENT - 1;
        memcpy(obj_name, name, olen);
        obj_name[olen] = '\0';
        const char *obj_type = find_var_type(obj_name);
        if (obj_type) {
            StructInfo *si = find_struct(obj_type);
            if (si) {
                const char *field = dot + 1;
                for (int i = 0; i < si->field_count; i++) {
                    if (strcmp(si->field_names[i], field) == 0)
                        return si->field_stypes[i];
                }
            }
        }
    }
    return nullptr;
}

static bool var_is_array(const char *name) {
    const char *t = find_var_type(name);
    return t && t[0] == '[';
}

static bool var_is_text(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "text") == 0;
}

static bool var_is_text_array(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "[text]") == 0;
}

static bool var_is_float_array(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "[f64]") == 0;
}

static bool var_is_nested_array(const char *name) {
    const char *t = find_var_type(name);
    return t && t[0] == '[' && t[1] == '[';
}

/* Get the element type when indexing an array type. [X] -> X, [[X]] -> [X] */
static void array_elem_stype(const char *arr_stype, char *out, int outsz) {
    if (!arr_stype || arr_stype[0] != '[') { strncpy(out, "i64", outsz); return; }
    /* Remove outermost [ ] */
    const char *s = arr_stype + 1;
    int len = strlen(s);
    if (len > 0 && s[len-1] == ']') len--;
    if (len >= outsz) len = outsz - 1;
    memcpy(out, s, len);
    out[len] = '\0';
}


static const char *var_struct_type(const char *name) {
    /* "self" in an impl block refers to the current struct */
    if (strcmp(name, "self") == 0 && current_impl_struct[0] != '\0') {
        return current_impl_struct;
    }
    const char *t = find_var_type(name);
    if (t && find_struct(t)) return t;
    return nullptr;
}

static bool var_is_option(const char *name) {
    const char *t = find_var_type(name);
    return t && type_is_option(t);
}

/* Check if a Simple type is a struct array type like [CoreExpr] */
static bool type_is_struct_array(const char *stype) {
    if (!stype || stype[0] != '[') return false;
    char elem[MAX_IDENT];
    int ei = 0;
    const char *p = stype + 1;
    while (*p && *p != ']' && ei < MAX_IDENT - 1) elem[ei++] = *p++;
    elem[ei] = '\0';
    if (strcmp(elem, "i64") == 0 || strcmp(elem, "text") == 0 ||
        strcmp(elem, "bool") == 0 || strcmp(elem, "f64") == 0 ||
        elem[0] == '[') return false;
    return find_struct(elem) != nullptr;
}

/* Extract element type from struct array type [StructName] → StructName */
static void struct_array_elem_type(const char *stype, char *out, int outsz) {
    out[0] = '\0';
    if (!stype || stype[0] != '[') return;
    const char *p = stype + 1;
    int ei = 0;
    while (*p && *p != ']' && ei < outsz - 1) out[ei++] = *p++;
    out[ei] = '\0';
}

/* Check if a variable has a struct array type */
static bool var_is_struct_array(const char *name) {
    const char *t = find_var_type(name);
    return t && type_is_struct_array(t);
}

/* Look up a struct field's Simple type. Returns null if not found. */
static const char *struct_field_stype(const char *struct_name, const char *field_name) {
    StructInfo *si = find_struct(struct_name);
    if (!si) return nullptr;
    for (int i = 0; i < si->field_count; i++) {
        if (strcmp(si->field_names[i], field_name) == 0)
            return si->field_stypes[i];
    }
    return nullptr;
}

/* Check if a type is a struct array: [StructName] */
static bool is_struct_array_type(const char *stype) {
    if (!stype || stype[0] != '[') return false;
    /* Extract element type from [ElementType] */
    const char *elem_start = stype + 1;
    const char *elem_end = strchr(elem_start, ']');
    if (!elem_end) return false;
    char elem_type[MAX_IDENT] = "";
    int len = elem_end - elem_start;
    if (len >= MAX_IDENT) return false;
    strncpy(elem_type, elem_start, len);
    elem_type[len] = '\0';
    /* Check if element type is a struct */
    return find_struct(trim(elem_type)) != nullptr;
}

static bool is_simple_identifier_token(const char *s) {
    if (!s || !*s) return false;
    if (!(isalpha((unsigned char)s[0]) || s[0] == '_')) return false;
    for (int i = 1; s[i]; i++) {
        if (!(isalnum((unsigned char)s[i]) || s[i] == '_')) return false;
    }
    return true;
}

/* Check if a dot expression (obj.field) refers to an Option struct field */
static bool dot_expr_is_option(const char *e) {
    const char *dot = strchr(e, '.');
    if (!dot) return false;
    char obj[MAX_IDENT] = "";
    int oi = 0;
    const char *p = e;
    while (p < dot && oi < MAX_IDENT - 1) obj[oi++] = *p++;
    obj[oi] = '\0';
    char field[MAX_IDENT] = "";
    int fi2 = 0;
    p = dot + 1;
    while (*p && *p != '.' && *p != '(' && *p != ' ' && fi2 < MAX_IDENT - 1) field[fi2++] = *p++;
    field[fi2] = '\0';
    const char *stype = var_struct_type(trim(obj));
    if (!stype) return false;
    const char *ft = struct_field_stype(stype, field);
    return ft && type_is_option(ft);
}


/* Check if an expression evaluates to an Option type */
static bool expr_is_option(const char *e) {
    e = skip_spaces(e);
    if (var_is_option(e)) return true;
    /* Check struct field: obj.field */
    if (dot_expr_is_option(e)) return true;
    /* Check if it's a function call returning Option */
    char func_name[MAX_IDENT] = "";
    int fi = 0;
    while (*e && *e != '(' && *e != '.' && *e != ' ' && fi < MAX_IDENT-1)
        func_name[fi++] = *e++;
    func_name[fi] = '\0';
    FuncInfo *fn = find_func(func_name);
    if (fn && type_is_option(fn->simple_ret)) return true;
    return false;
}


/* ===== Helpers ===== */

static bool is_constant_expr(const char *e) {
    e = skip_spaces(e);
    if (*e == '\0') return true;
    if (isdigit(*e) || (*e == '-' && isdigit(e[1]))) return true;
    if (*e == '"') return true;
    if (strcmp(e, "true") == 0 || strcmp(e, "false") == 0 || strcmp(e, "nil") == 0) return true;
    return false;
}

/* Check if an identifier starts with uppercase (potential struct constructor or enum) */
static bool is_upper_ident(const char *s) {
    return s && isupper((unsigned char)s[0]);
}

/* Check if an expression evaluates to text type.
 * Handles: simple vars, struct field access (e.g. tok.value), string literals */
static bool expr_is_text(const char *e) {
    e = skip_spaces(e);
    if (*e == '"') return true;
    if (strcmp(e, "NL") == 0) return true;  /* NL is always text */
    if (var_is_text(e)) return true;
    /* Check for struct field access: obj.field where field is text */
    const char *dot = strrchr(e, '.');
    if (dot && dot > e) {
        char obj_name[MAX_IDENT] = "";
        int oi = 0;
        const char *p = e;
        while (p < dot && oi < MAX_IDENT - 1) obj_name[oi++] = *p++;
        obj_name[oi] = '\0';
        const char *field = dot + 1;
        const char *stype = var_struct_type(trim(obj_name));
        if (stype) {
            StructInfo *si = find_struct(stype);
            if (si) {
                for (int i = 0; i < si->field_count; i++) {
                    if (strcmp(si->field_names[i], field) == 0) {
                        return strcmp(si->field_stypes[i], "text") == 0;
                    }
                }
            }
        }
    }
    /* Check for struct method return type: obj.method() */
    if (dot && dot > e) {
        char obj_nm[MAX_IDENT] = "";
        int oni = 0;
        const char *pp = skip_spaces(e);
        while (pp < dot && oni < MAX_IDENT - 1) obj_nm[oni++] = *pp++;
        obj_nm[oni] = '\0';
        const char *rest = dot + 1;
        char mname[MAX_IDENT] = "";
        int mni = 0;
        while (*rest && *rest != '(' && mni < MAX_IDENT - 1) mname[mni++] = *rest++;
        mname[mni] = '\0';
        const char *obj_st = var_struct_type(trim(obj_nm));
        if (obj_st) {
            FuncInfo *meth = find_method(obj_st, mname);
            if (meth && strcmp(meth->simple_ret, "text") == 0) return true;
        }
    }
    /* Check for function return type */
    const char *e2 = skip_spaces(e);
    char func_name[MAX_IDENT] = "";
    int fi = 0;
    while (*e2 && *e2 != '(' && *e2 != '.' && *e2 != ' ' && fi < MAX_IDENT - 1)
        func_name[fi++] = *e2++;
    func_name[fi] = '\0';
    FuncInfo *fn = find_func(func_name);
    if (fn && strcmp(fn->simple_ret, "text") == 0) return true;
    return false;
}

/* ===== Stub Body Detection & Emission ===== */

/* Check if the C++ output generated between saved_pos and out_pos looks broken */
static bool output_has_problems(int saved_pos) {
    /* Disabled for core bootstrap: every function is critical, better to let */
    /* the C++ compiler catch real issues than to stub out critical functions */
    return false;
    if (out_pos <= saved_pos) return false;
    int len = out_pos - saved_pos;
    const char *start = output + saved_pos;

    /* Count problem indicators */
    int problems = 0;
    int todos = 0;
    int nested_funcs = 0;

    /* Check for extremely long lines (garbled output signature) */
    int line_len = 0;
    int max_line_len = 0;

    /* Check brace balance */
    int brace_depth = 0;

    for (int i = 0; i < len; i++) {
        if (start[i] == '\n') {
            if (line_len > max_line_len) max_line_len = line_len;
            line_len = 0;
        } else {
            line_len++;
        }

        if (start[i] == '{') brace_depth++;
        if (start[i] == '}') brace_depth--;

        if (i >= len - 4) continue;

        /* Nested function/struct/class definitions (not allowed in C++ function body) */
        if (i == 0 || start[i-1] == '\n' || start[i-1] == ' ') {
            if (strncmp(start + i, "struct ", 7) == 0 && i > 0) nested_funcs++;
            if (strncmp(start + i, "class ", 6) == 0 && i > 0) nested_funcs++;
            if (strncmp(start + i, "enum ", 5) == 0 && i > 0) nested_funcs++;
        }
        /* TODO stubs indicate untranslated code */
        if (strncmp(start + i, "/* TODO", 7) == 0) todos++;
        /* Raw Simple syntax leaked into C++ — only flag truly garbled output */
        /* Note: val/var/elif may appear due to minor translation misses but are */
        /* better caught by the C++ compiler than by stubbing entire functions */
        if (i == 0 || start[i-1] == '\n' || start[i-1] == ' ' || start[i-1] == '(') {
            if (strncmp(start + i, "fn ", 3) == 0) problems++;
            if (strncmp(start + i, "impl ", 5) == 0) problems++;
            if (strncmp(start + i, "trait ", 6) == 0) problems++;
        }
    }
    if (line_len > max_line_len) max_line_len = line_len;

    /* Garbled output produces extremely long lines */
    /* 600 threshold: spl_str_concat chains from string concatenation can be 400+ chars */
    if (max_line_len > 600) { fprintf(stderr, "[seed_cpp] problem: max_line_len=%d\n", max_line_len); return true; }
    /* Unbalanced braces indicate broken output */
    if (brace_depth != 0) { fprintf(stderr, "[seed_cpp] problem: brace_depth=%d\n", brace_depth); return true; }
    /* If too many problems, the body is garbled */
    if (nested_funcs > 0) { fprintf(stderr, "[seed_cpp] problem: nested_funcs=%d\n", nested_funcs); return true; }
    if (todos > 0) { fprintf(stderr, "[seed_cpp] problem: todos=%d\n", todos); return true; }
    if (problems > 0) { fprintf(stderr, "[seed_cpp] problem: problems=%d\n", problems); return true; }
    /* No problems detected - body is good! */
    return false;
}

/* Emit a stub return statement appropriate for the C++ return type */
static void emit_stub_return(const char *ret_type) {
    if (!ret_type || strcmp(ret_type, "void") == 0) {
        emit("    /* stub */\n");
        return;
    }
    if (strcmp(ret_type, "int64_t") == 0 || strcmp(ret_type, "int32_t") == 0 ||
        strcmp(ret_type, "uint8_t") == 0 || strcmp(ret_type, "uint32_t") == 0 ||
        strcmp(ret_type, "uint64_t") == 0) {
        emit("    return 0; /* stub */\n");
        return;
    }
    if (strcmp(ret_type, "bool") == 0) {
        emit("    return false; /* stub */\n");
        return;
    }
    if (strcmp(ret_type, "double") == 0 || strcmp(ret_type, "float") == 0) {
        emit("    return 0.0; /* stub */\n");
        return;
    }
    if (strcmp(ret_type, "const char*") == 0) {
        emit("    return \"\"; /* stub */\n");
        return;
    }
    if (strstr(ret_type, "*")) {
        emit("    return nullptr; /* stub */\n");
        return;
    }
    /* Struct type — return zero-initialized */
    emit("    return %s{}; /* stub */\n", ret_type);
}

/* ===== Expression Translation ===== */

static void translate_expr(const char *expr, char *out, int outsz);
static void translate_block(int *line_idx, int base_indent, int c_indent);
static void translate_statement(const char *trimmed, int c_indent);

/* Translate comma-separated argument list: each arg translated individually */
static void translate_args(const char *args, char *out, int outsz) {
    out[0] = '\0';
    if (!args || !*args) return;
    char arg_buf[MAX_LINE];
    int ab = 0;
    int adepth = 0;
    bool first_arg = true;
    for (int i = 0; args[i]; i++) {
        if (args[i] == '(' || args[i] == '[') adepth++;
        else if (args[i] == ')' || args[i] == ']') adepth--;
        else if (args[i] == '"') {
            arg_buf[ab++] = args[i++];
            while (args[i] && args[i] != '"') {
                if (args[i] == '\\') arg_buf[ab++] = args[i++];
                if (args[i]) arg_buf[ab++] = args[i++];
            }
            if (args[i]) arg_buf[ab++] = args[i];
            continue;
        }
        if (args[i] == ',' && adepth == 0) {
            arg_buf[ab] = '\0';
            char arg_c[MAX_LINE];
            translate_expr(trim(arg_buf), arg_c, sizeof(arg_c));
            if (!first_arg) strncat(out, ", ", outsz - strlen(out) - 1);
            strncat(out, arg_c, outsz - strlen(out) - 1);
            first_arg = false;
            ab = 0;
            continue;
        }
        arg_buf[ab++] = args[i];
    }
    arg_buf[ab] = '\0';
    if (ab > 0) {
        char arg_c[MAX_LINE];
        translate_expr(trim(arg_buf), arg_c, sizeof(arg_c));
        if (!first_arg) strncat(out, ", ", outsz - strlen(out) - 1);
        strncat(out, arg_c, outsz - strlen(out) - 1);
    }
}

/* Current function being translated (for Option return type tracking) */
static FuncInfo *current_func = nullptr;

static void translate_expr(const char *expr, char *out, int outsz) {
    const char *e = skip_spaces(expr);

    /* Empty */
    if (*e == '\0') { snprintf(out, outsz, "0"); return; }

    /* String literal with interpolation */
    if (*e == '"') {
        /* Check if this is a pure string literal or part of a binary expression.
         * If there's content after the closing ", let the binary operator handler
         * process it (e.g., "text" + expr should use spl_str_concat). */
        {
            const char *cq = e + 1;
            while (*cq && *cq != '"') { if (*cq == '\\') cq++; cq++; }
            if (*cq == '"') cq++;
            const char *after = skip_spaces(cq);
            if (*after != '\0') {
                /* Not a pure string literal — has operator/content after.
                 * Skip string handler, let binary operator handler deal with it. */
                goto skip_string_handler;
            }
        }

        /* Make a local copy of the string to avoid corruption when recursive
         * translate_expr calls overwrite trim()'s static buffer (which 'e'
         * may point into, e.g. from 'return "..."' handler). */
        char str_local_copy[MAX_LINE];
        strncpy(str_local_copy, e, MAX_LINE - 1);
        str_local_copy[MAX_LINE - 1] = '\0';
        e = str_local_copy;

        bool has_interp = false;
        for (const char *p = e + 1; *p && *p != '"'; p++) {
            if (*p == '\\') { p++; continue; }
            if (*p == '{') {
                const char *q = p + 1;
                int depth = 1;
                while (*q && depth > 0) {
                    if (*q == '{') depth++;
                    else if (*q == '}') { depth--; if (depth == 0) break; }
                    else if (*q == '"') break;
                    q++;
                }
                if (*q == '}' && (q - p) > 1) {
                    char expr_probe[MAX_LINE];
                    int probe_len = (int)(q - (p + 1));
                    if (probe_len >= MAX_LINE) probe_len = MAX_LINE - 1;
                    strncpy(expr_probe, p + 1, probe_len);
                    expr_probe[probe_len] = '\0';
                    if (strcmp(trim(expr_probe), "...") != 0) {
                        has_interp = true;
                        break;
                    }
                }
            }
        }
        if (!has_interp) {
            snprintf(out, outsz, "%s", e);
        } else {
            char buf[MAX_LINE] = "";
            char part[MAX_LINE];
            const char *p = e + 1;
            char str_buf[MAX_LINE] = "\"";
            int str_pos = 1;
            bool first = true;

            while (*p && *p != '"') {
                if (*p == '\\') {
                    str_buf[str_pos++] = *p++;
                    if (*p) str_buf[str_pos++] = *p++;
                    continue;
                }
                if (*p == '{') {
                    const char *interp_end = p + 1;
                    int preview_depth = 1;
                    while (*interp_end && preview_depth > 0) {
                        if (*interp_end == '{') preview_depth++;
                        else if (*interp_end == '}') {
                            preview_depth--;
                            if (preview_depth == 0) break;
                        } else if (*interp_end == '"') {
                            break;
                        }
                        interp_end++;
                    }

                    if (*interp_end == '}' && (interp_end - p) > 1) {
                        char expr_probe[MAX_LINE];
                        int probe_len = (int)(interp_end - (p + 1));
                        if (probe_len >= MAX_LINE) probe_len = MAX_LINE - 1;
                        strncpy(expr_probe, p + 1, probe_len);
                        expr_probe[probe_len] = '\0';
                        if (strcmp(trim(expr_probe), "...") == 0) {
                            while (p <= interp_end && *p) {
                                str_buf[str_pos++] = *p++;
                            }
                            continue;
                        }
                    }

                    str_buf[str_pos++] = '"';
                    str_buf[str_pos] = '\0';
                    if (str_pos > 2) {
                        if (first) {
                            snprintf(buf, sizeof(buf), "%s", str_buf);
                            first = false;
                        } else {
                            snprintf(part, sizeof(part), "spl_str_concat(%s, ", buf);
                            snprintf(buf, sizeof(buf), "%s%s)", part, str_buf);
                        }
                    }

                    p++;
                    char expr_buf[MAX_LINE] = "";
                    int eb = 0;
                    int depth = 1;
                    while (*p && depth > 0) {
                        if (*p == '{') depth++;
                        else if (*p == '}') { depth--; if (depth == 0) break; }
                        expr_buf[eb++] = *p++;
                    }
                    expr_buf[eb] = '\0';
                    if (*p == '}') p++;

                    char inner_c[MAX_LINE];
                    translate_expr(expr_buf, inner_c, sizeof(inner_c));

                    char as_str[MAX_LINE];
                    char *trimmed_expr = trim(expr_buf);
                    if (var_is_text(trimmed_expr) || trimmed_expr[0] == '"' || expr_is_text(trimmed_expr) || strcmp(trimmed_expr, "NL") == 0) {
                        snprintf(as_str, sizeof(as_str), "%s", inner_c);
                    } else {
                        snprintf(as_str, sizeof(as_str), "spl_i64_to_str(%s)", inner_c);
                    }

                    if (first) {
                        snprintf(buf, sizeof(buf), "%s", as_str);
                        first = false;
                    } else {
                        snprintf(part, sizeof(part), "spl_str_concat(%s, %s)", buf, as_str);
                        snprintf(buf, sizeof(buf), "%s", part);
                    }

                    str_pos = 0;
                    str_buf[str_pos++] = '"';
                    continue;
                }
                str_buf[str_pos++] = *p++;
            }
            if (*p == '"') p++;

            str_buf[str_pos++] = '"';
            str_buf[str_pos] = '\0';
            if (str_pos > 2) {
                if (first) {
                    snprintf(buf, sizeof(buf), "%s", str_buf);
                } else {
                    snprintf(part, sizeof(part), "spl_str_concat(%s, %s)", buf, str_buf);
                    snprintf(buf, sizeof(buf), "%s", part);
                }
            }

            if (buf[0] == '\0') snprintf(out, outsz, "\"\"");
            else snprintf(out, outsz, "%s", buf);
        }
        return;
    }
    skip_string_handler:

    /* Integer/float literal */
    if (isdigit(*e) || (*e == '-' && isdigit(e[1]))) {
        /* Verify it's a pure number, not an expression starting with a digit */
        const char *np = e;
        if (*np == '-') np++;
        while (isdigit(*np)) np++;
        if (*np == '.') { np++; while (isdigit(*np)) np++; }
        if (*np == '\0') {
            snprintf(out, outsz, "%s", e);
            return;
        }
    }

    /* Bool/nil literals */
    if (strcmp(e, "true") == 0) { snprintf(out, outsz, "true"); return; }
    if (strcmp(e, "false") == 0) { snprintf(out, outsz, "false"); return; }
    if (strcmp(e, "nil") == 0) { snprintf(out, outsz, "spl_nil()"); return; }

    /* 'not' prefix */
    if (starts_with(e, "not ")) {
        char inner[MAX_LINE];
        translate_expr(e + 4, inner, sizeof(inner));
        snprintf(out, outsz, "!(%s)", inner);
        return;
    }

    /* Parenthesized expression */
    if (*e == '(') {
        int depth = 1;
        const char *p = e + 1;
        while (*p && depth > 0) {
            if (*p == '(') depth++;
            else if (*p == ')') depth--;
            p++;
        }
        const char *after = skip_spaces(p);
        if (*after == '\0') {
            char inner[MAX_LINE];
            int len = (p - 1) - (e + 1);
            strncpy(inner, e + 1, len);
            inner[len] = '\0';
            if (inner[0] == '\0') {
                snprintf(out, outsz, "0 /* unit */");
            } else {
                char inner_c[MAX_LINE];
                translate_expr(trim(inner), inner_c, sizeof(inner_c));
                snprintf(out, outsz, "(%s)", inner_c);
            }
            return;
        }
    }

    /* Array literal: [1, 2, 3] */
    if (*e == '[') {
        snprintf(out, outsz, "spl_array_new()");
        return;
    }

    /* Binary operators: find the lowest precedence operator not inside parens/brackets */
    {
        int paren = 0;
        int best_pos = -1;
        int best_prec = 999;
        const char *p = e;

        while (*p) {
            if (*p == '(' || *p == '[') { paren++; p++; continue; }
            if (*p == ')' || *p == ']') { paren--; p++; continue; }
            if (*p == '"') { p++; while (*p && *p != '"') { if (*p == '\\') p++; p++; } if (*p) p++; continue; }

            if (paren == 0) {
                int pos = p - e;
                int prec = 999;
                const char *op = nullptr;
                if (starts_with(p, " and ")) { prec = 2; op = "&&"; }
                else if (starts_with(p, " or ")) { prec = 1; op = "||"; }
                else if (starts_with(p, " == ")) { prec = 4; op = "=="; }
                else if (starts_with(p, " != ")) { prec = 4; op = "!="; }
                else if (starts_with(p, " >= ")) { prec = 5; op = ">="; }
                else if (starts_with(p, " <= ")) { prec = 5; op = "<="; }
                else if (starts_with(p, " ?? ")) { prec = 3; op = "??"; }
                else if (starts_with(p, " > ")) { prec = 5; op = ">"; }
                else if (starts_with(p, " < ")) { prec = 5; op = "<"; }
                else if (starts_with(p, " + ")) { prec = 6; op = "+"; }
                else if (starts_with(p, " - ")) { prec = 6; op = "-"; }
                else if (starts_with(p, " ** ")) { prec = 8; op = "**"; }
                else if (starts_with(p, " * ")) { prec = 7; op = "*"; }
                else if (starts_with(p, " / ")) { prec = 7; op = "/"; }
                else if (starts_with(p, " % ")) { prec = 7; op = "%"; }

                if (op && prec <= best_prec) {
                    best_prec = prec;
                    best_pos = pos;
                }
            }
            p++;
        }

        if (best_pos >= 0) {
            char left_str[MAX_LINE], right_str[MAX_LINE];
            strncpy(left_str, e, best_pos);
            left_str[best_pos] = '\0';

            const char *op_start = e + best_pos;
            const char *op_str = nullptr;
            int skip = 0;
            if (starts_with(op_start, " and ")) { op_str = "&&"; skip = 5; }
            else if (starts_with(op_start, " or ")) { op_str = "||"; skip = 4; }
            else if (starts_with(op_start, " == ")) { op_str = "=="; skip = 4; }
            else if (starts_with(op_start, " != ")) { op_str = "!="; skip = 4; }
            else if (starts_with(op_start, " >= ")) { op_str = ">="; skip = 4; }
            else if (starts_with(op_start, " <= ")) { op_str = "<="; skip = 4; }
            else if (starts_with(op_start, " ?? ")) { op_str = "??"; skip = 4; }
            else if (starts_with(op_start, " > ")) { op_str = ">"; skip = 3; }
            else if (starts_with(op_start, " < ")) { op_str = "<"; skip = 3; }
            else if (starts_with(op_start, " + ")) { op_str = "+"; skip = 3; }
            else if (starts_with(op_start, " - ")) { op_str = "-"; skip = 3; }
            else if (starts_with(op_start, " ** ")) { op_str = "**"; skip = 4; }
            else if (starts_with(op_start, " * ")) { op_str = "*"; skip = 3; }
            else if (starts_with(op_start, " / ")) { op_str = "/"; skip = 3; }
            else if (starts_with(op_start, " % ")) { op_str = "%"; skip = 3; }

            if (!op_str || skip <= 0) {
                /* False-positive binary operator match: fall through to non-binary parsing. */
                goto no_binary_match;
            }

            strncpy(right_str, e + best_pos + skip, MAX_LINE-1);
            right_str[MAX_LINE-1] = '\0';

            char left_norm[MAX_LINE], right_norm[MAX_LINE];
            strncpy(left_norm, trim(left_str), sizeof(left_norm) - 1);
            left_norm[sizeof(left_norm) - 1] = '\0';
            strncpy(right_norm, trim(right_str), sizeof(right_norm) - 1);
            right_norm[sizeof(right_norm) - 1] = '\0';
            if (left_norm[0] == '\0' || right_norm[0] == '\0' ||
                strcmp(left_norm, e) == 0 || strcmp(right_norm, e) == 0) {
                /* Ensure recursive split always makes progress. */
                goto no_binary_match;
            }

            char left_c[MAX_LINE], right_c[MAX_LINE];
            translate_expr(left_norm, left_c, sizeof(left_c));
            translate_expr(right_norm, right_c, sizeof(right_c));

            if (strcmp(op_str, "+") == 0) {
                bool left_is_str = expr_is_text(left_norm);
                bool right_is_str = expr_is_text(right_norm);
                if (left_is_str || right_is_str) {
                    snprintf(out, outsz, "spl_str_concat(%s, %s)", left_c, right_c);
                    return;
                }
            }

            /* Nil comparison */
            if (strcmp(op_str, "==") == 0 || strcmp(op_str, "!=") == 0) {
                bool nil_on_right = (strcmp(right_norm, "nil") == 0);
                bool nil_on_left = (strcmp(left_norm, "nil") == 0);
                if (nil_on_right || nil_on_left) {
                    const char *val_side = nil_on_right ? left_c : right_c;
                    const char *var_name = nil_on_right ? left_norm : right_norm;
                    const char *cmp = strcmp(op_str, "==") == 0 ? "==" : "!=";
                    /* Option type: check .has_value */
                    if (expr_is_option(var_name)) {
                        if (strcmp(cmp, "==") == 0)
                            snprintf(out, outsz, "(!%s.has_value)", val_side);
                        else
                            snprintf(out, outsz, "%s.has_value", val_side);
                        return;
                    }
                    if (var_is_text(var_name)) {
                        snprintf(out, outsz, "(%s %s NULL)", val_side, cmp);
                    } else {
                        snprintf(out, outsz, "(%s %s -1)", val_side, cmp);
                    }
                    return;
                }
            }

            /* String equality */
            if (strcmp(op_str, "==") == 0 || strcmp(op_str, "!=") == 0) {
                bool left_is_str = expr_is_text(left_norm);
                bool right_is_str = expr_is_text(right_norm);
                if (left_is_str || right_is_str) {
                    if (strcmp(op_str, "==") == 0) {
                        snprintf(out, outsz, "spl_str_eq(%s, %s)", left_c, right_c);
                    } else {
                        snprintf(out, outsz, "(!spl_str_eq(%s, %s))", left_c, right_c);
                    }
                    return;
                }
            }

            if (strcmp(op_str, "??") == 0) {
                /* Option type: use .has_value and .value */
                if (expr_is_option(left_norm)) {
                    snprintf(out, outsz, "(%s.has_value ? %s.value : %s)", left_c, left_c, right_c);
                } else {
                    snprintf(out, outsz, "((%s) ? (%s) : (%s))", left_c, left_c, right_c);
                }
                return;
            }

            /* Power operator: a ** b -> pow(a, b) */
            if (strcmp(op_str, "**") == 0) {
                snprintf(out, outsz, "(int64_t)pow((double)%s, (double)%s)", left_c, right_c);
                return;
            }

            snprintf(out, outsz, "(%s %s %s)", left_c, op_str, right_c);
            return;
        }
no_binary_match:
        ;
    }

    /* Method calls and field access: obj.method(args) or obj.field */
    {
        int paren = 0;
        int last_dot = -1;
        for (int i = 0; e[i]; i++) {
            if (e[i] == '(' || e[i] == '[') paren++;
            else if (e[i] == ')' || e[i] == ']') paren--;
            else if (e[i] == '"') { i++; while (e[i] && e[i] != '"') { if (e[i] == '\\') i++; i++; } }
            else if (e[i] == '.' && paren == 0) last_dot = i;
        }

        if (last_dot > 0) {
            char obj[MAX_LINE], rest[MAX_LINE];
            strncpy(obj, e, last_dot);
            obj[last_dot] = '\0';
            strcpy(rest, e + last_dot + 1);

            char obj_c[MAX_LINE];
            translate_expr(trim(obj), obj_c, sizeof(obj_c));

            /* .? operator: Optional chaining / has-value check */
            if (strcmp(rest, "?") == 0 || starts_with(rest, "?.")) {
                if (strcmp(rest, "?") == 0) {
                    /* Simple boolean check: x.? → x.has_value (for Option) or !x.empty() (for arrays) */
                    if (var_is_option(trim(obj)) || dot_expr_is_option(trim(obj)) || expr_is_option(trim(obj))) {
                        snprintf(out, outsz, "%s.has_value", obj_c);
                    } else if (var_is_array(trim(obj)) || var_is_struct_array(trim(obj))) {
                        snprintf(out, outsz, "(spl_array_len(%s) > 0)", obj_c);
                    } else {
                        /* For other types, treat as truthiness check */
                        snprintf(out, outsz, "(%s != 0)", obj_c);
                    }
                    return;
                } else {
                    /* Optional chaining: x.?.field or x.?.method() */
                    const char *after_q = rest + 2; /* Skip "?." */
                    char chained_expr[MAX_LINE];
                    snprintf(chained_expr, sizeof(chained_expr), "%s.%s", obj, after_q);

                    /* Translate the chained part */
                    char chained_c[MAX_LINE];
                    translate_expr(chained_expr, chained_c, sizeof(chained_c));

                    /* Wrap in ternary: (x.has_value ? x.value.field : default) */
                    if (var_is_option(trim(obj)) || dot_expr_is_option(trim(obj)) || expr_is_option(trim(obj))) {
                        snprintf(out, outsz, "(%s.has_value ? %s.value.%s : 0)", obj_c, obj_c, after_q);
                    } else {
                        /* For non-option types, just emit the chained expression */
                        snprintf(out, outsz, "%s", chained_c);
                    }
                    return;
                }
            }

            /* Option type methods: .unwrap(), .is_some(), .is_none() */
            if (var_is_option(trim(obj)) || dot_expr_is_option(trim(obj)) || expr_is_option(trim(obj))) {
                if (strcmp(rest, "unwrap()") == 0) {
                    snprintf(out, outsz, "%s.value", obj_c);
                    return;
                }
                if (strcmp(rest, "is_some()") == 0) {
                    snprintf(out, outsz, "%s.has_value", obj_c);
                    return;
                }
                if (strcmp(rest, "is_none()") == 0) {
                    snprintf(out, outsz, "(!%s.has_value)", obj_c);
                    return;
                }
            }

            /* Built-in methods: len, push, pop, contains, etc. */
            if (starts_with(rest, "len()")) {
                if (var_is_text(trim(obj)) || expr_is_text(trim(obj))) {
                    snprintf(out, outsz, "spl_str_len(%s)", obj_c);
                } else if (var_is_struct_array(trim(obj))) {
                    snprintf(out, outsz, "(int64_t)%s.size()", obj_c);
                } else {
                    snprintf(out, outsz, "spl_array_len(%s)", obj_c);
                }
                return;
            }
            if (starts_with(rest, "push(")) {
                char arg[MAX_LINE];
                const char *a = rest + 5;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') {
                    strncpy(arg, a, len - 1);
                    arg[len-1] = '\0';
                }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                if (var_is_struct_array(trim(obj))) {
                    snprintf(out, outsz, "%s.push_back(%s)", obj_c, arg_c);
                } else if (var_is_nested_array(trim(obj))) {
                    snprintf(out, outsz, "spl_array_push(%s, spl_array_val(%s))", obj_c, arg_c);
                } else if (var_is_text_array(trim(obj))) {
                    snprintf(out, outsz, "spl_array_push(%s, spl_str(%s))", obj_c, arg_c);
                } else if (var_is_float_array(trim(obj))) {
                    snprintf(out, outsz, "spl_array_push(%s, spl_float(%s))", obj_c, arg_c);
                } else {
                    snprintf(out, outsz, "spl_array_push(%s, spl_int(%s))", obj_c, arg_c);
                }
                return;
            }
            if (starts_with(rest, "pop()")) {
                if (var_is_struct_array(trim(obj))) {
                    snprintf(out, outsz, "([&](){ auto __v = %s.back(); %s.pop_back(); return __v; }())", obj_c, obj_c);
                } else {
                    snprintf(out, outsz, "spl_array_pop(%s).as_int", obj_c);
                }
                return;
            }
            if (starts_with(rest, "contains(")) {
                char arg[MAX_LINE];
                const char *a = rest + 9;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_contains(%s, %s)", obj_c, arg_c);
                return;
            }
            if (starts_with(rest, "starts_with(")) {
                char arg[MAX_LINE];
                const char *a = rest + 12;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_starts_with(%s, %s)", obj_c, arg_c);
                return;
            }
            if (starts_with(rest, "ends_with(")) {
                char arg[MAX_LINE];
                const char *a = rest + 10;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_ends_with(%s, %s)", obj_c, arg_c);
                return;
            }
            if (starts_with(rest, "index_of(")) {
                char arg[MAX_LINE];
                const char *a = rest + 9;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_index_of(%s, %s)", obj_c, arg_c);
                return;
            }
            if (strcmp(rest, "trim()") == 0) {
                snprintf(out, outsz, "spl_str_trim(%s)", obj_c);
                return;
            }
            if (starts_with(rest, "slice(")) {
                const char *a = rest + 6;
                char args_buf[MAX_LINE];
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(args_buf, a, len-1); args_buf[len-1] = '\0'; }
                else { strncpy(args_buf, a, MAX_LINE-1); args_buf[MAX_LINE-1] = '\0'; }
                char arg1[MAX_LINE] = "", arg2[MAX_LINE] = "";
                int depth = 0, split = -1;
                for (int i = 0; args_buf[i]; i++) {
                    if (args_buf[i] == '(' || args_buf[i] == '[') depth++;
                    else if (args_buf[i] == ')' || args_buf[i] == ']') depth--;
                    else if (args_buf[i] == ',' && depth == 0) { split = i; break; }
                }
                if (split > 0) {
                    strncpy(arg1, args_buf, split); arg1[split] = '\0';
                    strcpy(arg2, args_buf + split + 1);
                }
                char a1c[MAX_LINE], a2c[MAX_LINE];
                translate_expr(trim(arg1), a1c, sizeof(a1c));
                translate_expr(trim(arg2), a2c, sizeof(a2c));
                snprintf(out, outsz, "spl_str_slice(%s, %s, %s)", obj_c, a1c, a2c);
                return;
            }
            if (starts_with(rest, "replace(")) {
                const char *a = rest + 8;
                char args_buf[MAX_LINE];
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(args_buf, a, len-1); args_buf[len-1] = '\0'; }
                else { strncpy(args_buf, a, MAX_LINE-1); args_buf[MAX_LINE-1] = '\0'; }
                char arg1[MAX_LINE] = "", arg2[MAX_LINE] = "";
                int depth = 0, split = -1;
                for (int i = 0; args_buf[i]; i++) {
                    if (args_buf[i] == '(' || args_buf[i] == '[') depth++;
                    else if (args_buf[i] == ')' || args_buf[i] == ']') depth--;
                    else if (args_buf[i] == ',' && depth == 0) { split = i; break; }
                }
                if (split > 0) {
                    strncpy(arg1, args_buf, split); arg1[split] = '\0';
                    strcpy(arg2, args_buf + split + 1);
                }
                char a1c[MAX_LINE], a2c[MAX_LINE];
                translate_expr(trim(arg1), a1c, sizeof(a1c));
                translate_expr(trim(arg2), a2c, sizeof(a2c));
                snprintf(out, outsz, "spl_str_replace(%s, %s, %s)", obj_c, a1c, a2c);
                return;
            }
            if (starts_with(rest, "split(")) {
                char arg[MAX_LINE];
                const char *a = rest + 6;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                else { strncpy(arg, a, MAX_LINE-1); arg[MAX_LINE-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_split(%s, %s)", obj_c, arg_c);
                return;
            }
            if (starts_with(rest, "join(")) {
                char arg[MAX_LINE];
                const char *a = rest + 5;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(arg, a, len-1); arg[len-1] = '\0'; }
                else { strncpy(arg, a, MAX_LINE-1); arg[MAX_LINE-1] = '\0'; }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_join(%s, %s)", obj_c, arg_c);
                return;
            }

            /* Check if rest has [ before ( — if so, it's field+brackets, not method call */
            bool rest_has_bracket_before_paren = false;
            {
                const char *first_bracket = strchr(rest, '[');
                const char *first_paren = strchr(rest, '(');
                if (first_bracket && (!first_paren || first_bracket < first_paren))
                    rest_has_bracket_before_paren = true;
            }

            /* Static method call: StructName.method(args) or EnumName.method(args) → Type__method(args) */
            if (!rest_has_bracket_before_paren && strchr(rest, '(') && (find_struct(trim(obj)) || find_enum(trim(obj)))) {
                char method[MAX_IDENT];
                int mi = 0;
                const char *r = rest;
                while (*r && *r != '(') method[mi++] = *r++;
                method[mi] = '\0';

                if (*r == '(') r++;
                char args_str[MAX_LINE] = "";
                int depth = 1, ai = 0;
                while (*r && depth > 0) {
                    if (*r == '"') {
                        args_str[ai++] = *r++;
                        while (*r && *r != '"') {
                            if (*r == '\\') args_str[ai++] = *r++;
                            if (*r) args_str[ai++] = *r++;
                        }
                        if (*r == '"') args_str[ai++] = *r++;
                        continue;
                    }
                    if (*r == '(') depth++;
                    else if (*r == ')') { depth--; if (depth == 0) break; }
                    args_str[ai++] = *r++;
                }
                args_str[ai] = '\0';

                if (strlen(args_str) > 0) {
                    char args_c[MAX_LINE];
                    translate_args(trim(args_str), args_c, sizeof(args_c));
                    snprintf(out, outsz, "%s__%s(%s)", trim(obj), method, args_c);
                } else {
                    snprintf(out, outsz, "%s__%s()", trim(obj), method);
                }
                return;
            }

            /* Instance method call: obj.method(args) where obj is a known struct type */
            if (!rest_has_bracket_before_paren && strchr(rest, '(')) {
                const char *obj_stype = var_struct_type(trim(obj));
                if (obj_stype) {
                    /* It's a struct method → StructName__method(&obj, args) */
                    char method[MAX_IDENT];
                    int mi = 0;
                    const char *r = rest;
                    while (*r && *r != '(') method[mi++] = *r++;
                    method[mi] = '\0';

                    /* Extract args */
                    if (*r == '(') r++;
                    char args_str[MAX_LINE] = "";
                    int depth = 1, ai = 0;
                    while (*r && depth > 0) {
                        if (*r == '"') {
                            args_str[ai++] = *r++;
                            while (*r && *r != '"') {
                                if (*r == '\\') args_str[ai++] = *r++;
                                if (*r) args_str[ai++] = *r++;
                            }
                            if (*r == '"') args_str[ai++] = *r++;
                            continue;
                        }
                        if (*r == '(') depth++;
                        else if (*r == ')') { depth--; if (depth == 0) break; }
                        args_str[ai++] = *r++;
                    }
                    args_str[ai] = '\0';

                    /* Check if this method is known to be mutable */
                    (void)find_method(obj_stype, method);
                    /* If obj is "self", it's already a pointer — don't add & */
                    const char *addr_op = "&";
                    if (strcmp(trim(obj), "self") == 0) addr_op = "";

                    if (strlen(args_str) > 0) {
                        char args_c[MAX_LINE];
                        translate_args(trim(args_str), args_c, sizeof(args_c));
                        snprintf(out, outsz, "%s__%s(%s%s, %s)",
                                 obj_stype, method, addr_op, obj_c, args_c);
                    } else {
                        snprintf(out, outsz, "%s__%s(%s%s)",
                                 obj_stype, method, addr_op, obj_c);
                    }
                    return;
                }

                /* Generic method call (non-struct): obj.method(args) → method(obj, args) */
                char method[MAX_IDENT];
                int mi = 0;
                const char *r = rest;
                while (*r && *r != '(') method[mi++] = *r++;
                method[mi] = '\0';

                if (*r == '(') r++;
                char args_str[MAX_LINE] = "";
                int depth = 1, ai = 0;
                while (*r && depth > 0) {
                    if (*r == '"') {
                        args_str[ai++] = *r++;
                        while (*r && *r != '"') {
                            if (*r == '\\') args_str[ai++] = *r++;
                            if (*r) args_str[ai++] = *r++;
                        }
                        if (*r == '"') args_str[ai++] = *r++;
                        continue;
                    }
                    if (*r == '(') depth++;
                    else if (*r == ')') { depth--; if (depth == 0) break; }
                    args_str[ai++] = *r++;
                }
                args_str[ai] = '\0';

                if (strlen(args_str) > 0) {
                    char args_c[MAX_LINE];
                    translate_args(trim(args_str), args_c, sizeof(args_c));
                    snprintf(out, outsz, "%s_%s(%s, %s)", obj_c, method, obj_c, args_c);
                } else {
                    snprintf(out, outsz, "%s_%s(%s)", obj_c, method, obj_c);
                }
                return;
            }

            /* Field access: obj.field or obj.field[idx] with indexing/slicing
             * If obj is "self" (method body), use -> since self is a pointer */
            {
                const char *rb = strchr(rest, '[');
                if (rb) {
                    /* Field with indexing/slicing: obj.field[idx_expr] */
                    char field_name[MAX_IDENT] = "";
                    int fni = 0;
                    const char *fp = rest;
                    while (fp < rb && fni < MAX_IDENT - 1) field_name[fni++] = *fp++;
                    field_name[fni] = '\0';

                    /* Build the base expression: self->field or obj.field */
                    char base_expr[MAX_LINE];
                    if (strcmp(trim(obj), "self") == 0) {
                        snprintf(base_expr, sizeof(base_expr), "self->%s", field_name);
                    } else {
                        snprintf(base_expr, sizeof(base_expr), "%s.%s", obj_c, field_name);
                    }

                    /* Parse bracket contents */
                    const char *bp = rb + 1;
                    char idx_buf[MAX_LINE] = "";
                    int bdepth = 1, bi = 0;
                    while (*bp && bdepth > 0) {
                        if (*bp == '[') bdepth++;
                        else if (*bp == ']') { bdepth--; if (bdepth == 0) break; }
                        idx_buf[bi++] = *bp++;
                    }
                    idx_buf[bi] = '\0';

                    /* Check for slice (colon) */
                    char *colon = strchr(idx_buf, ':');
                    if (colon) {
                        *colon = '\0';
                        char start_c[MAX_LINE], end_c[MAX_LINE];
                        if (strlen(idx_buf) > 0) translate_expr(trim(idx_buf), start_c, sizeof(start_c));
                        else snprintf(start_c, sizeof(start_c), "0");
                        if (strlen(colon + 1) > 0) translate_expr(trim(colon + 1), end_c, sizeof(end_c));
                        else snprintf(end_c, sizeof(end_c), "spl_str_len(%s)", base_expr);
                        snprintf(out, outsz, "spl_str_slice(%s, %s, %s)", base_expr, start_c, end_c);
                    } else {
                        char idx_c[MAX_LINE];
                        translate_expr(trim(idx_buf), idx_c, sizeof(idx_c));
                        /* Determine field type to pick correct accessor */
                        bool is_text_field = false;
                        bool is_text_arr_field = false;
                        bool is_arr_field = false;
                        const char *obj_stype = var_struct_type(trim(obj));
                        if (obj_stype) {
                            const char *ft = struct_field_stype(obj_stype, field_name);
                            if (ft) {
                                if (strcmp(ft, "text") == 0) is_text_field = true;
                                else if (strcmp(ft, "[text]") == 0) is_text_arr_field = true;
                                else if (ft[0] == '[') is_arr_field = true;
                            }
                        }
                        /* Check if the field is a struct array */
                        bool is_struct_arr_field = false;
                        if (obj_stype) {
                            const char *ft2 = struct_field_stype(obj_stype, field_name);
                            if (ft2 && type_is_struct_array(ft2)) is_struct_arr_field = true;
                        }
                        if (is_text_field) {
                            snprintf(out, outsz, "spl_str_index_char(%s, %s)", base_expr, idx_c);
                        } else if (is_struct_arr_field) {
                            snprintf(out, outsz, "%s[%s]", base_expr, idx_c);
                        } else if (is_text_arr_field) {
                            snprintf(out, outsz, "spl_array_get(%s, %s).as_str", base_expr, idx_c);
                        } else if (is_arr_field) {
                            snprintf(out, outsz, "spl_array_get(%s, %s).as_int", base_expr, idx_c);
                        } else {
                            snprintf(out, outsz, "%s[%s]", base_expr, idx_c);
                        }
                    }
                    return;
                }
                /* Simple field access */
                if (strcmp(trim(obj), "self") == 0) {
                    snprintf(out, outsz, "self->%s", rest);
                } else if (find_enum(trim(obj))) {
                    /* EnumName.Variant -> EnumName_Variant */
                    snprintf(out, outsz, "%s_%s", trim(obj), rest);
                } else {
                    snprintf(out, outsz, "%s.%s", obj_c, rest);
                }
            }
            return;
        }
    }

    /* Function call / Constructor call: func(args) or StructName(field: val, ...) */
    {
        const char *paren = strchr(e, '(');
        /* Check for dot BEFORE the paren (method call) — dots inside args are fine */
        bool has_dot_before_paren = false;
        if (paren) {
            for (const char *dp = e; dp < paren; dp++) {
                if (*dp == '.') { has_dot_before_paren = true; break; }
            }
        }
        if (paren && !has_dot_before_paren) {
            char func_name[MAX_IDENT];
            int fi = 0;
            const char *p = e;
            while (p < paren && fi < MAX_IDENT - 1) func_name[fi++] = *p++;
            func_name[fi] = '\0';

            /* Extract args */
            p = paren + 1;
            char args[MAX_LINE] = "";
            int depth = 1, ai = 0;
            while (*p && depth > 0) {
                if (*p == '"') {
                    args[ai++] = *p++;
                    while (*p && *p != '"') {
                        if (*p == '\\') args[ai++] = *p++;
                        if (*p) args[ai++] = *p++;
                    }
                    if (*p == '"') args[ai++] = *p++;
                    continue;
                }
                if (*p == '(') depth++;
                else if (*p == ')') { depth--; if (depth == 0) break; }
                args[ai++] = *p++;
            }
            args[ai] = '\0';

            /* Check if this is a struct constructor: StructName(field: val, ...) */
            StructInfo *si = find_struct(func_name);
            if (si) {
                /* Emit designated initializer: StructName{.field1 = val1, .field2 = val2} */
                char result[MAX_LINE];
                int rpos = snprintf(result, sizeof(result), "%s{", func_name);

                /* Parse named arguments: field: value, field: value */
                const char *ap = args;
                bool first_field = true;
                while (*ap) {
                    ap = skip_spaces(ap);
                    if (*ap == '\0') break;

                    /* Extract field name (before ':') */
                    char fname[MAX_IDENT] = "";
                    int fni = 0;
                    while (*ap && *ap != ':' && *ap != ',' && *ap != ')') {
                        if (*ap == '(' || *ap == '[') break; /* positional arg */
                        fname[fni++] = *ap++;
                    }
                    fname[fni] = '\0';

                    if (*ap == ':') {
                        /* Named argument: field: value */
                        ap++; /* skip ':' */
                        ap = skip_spaces(ap);

                        /* Extract value (until comma at depth 0 or end) */
                        char val_buf[MAX_LINE] = "";
                        int vbi = 0;
                        int vdepth = 0;
                        while (*ap) {
                            if (*ap == '(' || *ap == '[') vdepth++;
                            else if (*ap == ')' || *ap == ']') vdepth--;
                            else if (*ap == '"') {
                                val_buf[vbi++] = *ap++;
                                while (*ap && *ap != '"') {
                                    if (*ap == '\\') val_buf[vbi++] = *ap++;
                                    if (*ap) val_buf[vbi++] = *ap++;
                                }
                                if (*ap == '"') val_buf[vbi++] = *ap++;
                                continue;
                            }
                            if (*ap == ',' && vdepth == 0) { ap++; break; }
                            val_buf[vbi++] = *ap++;
                        }
                        val_buf[vbi] = '\0';

                        char val_c[MAX_LINE];
                        const char *trimmed_val = trim(val_buf);

                        /* Check if this is an empty array for a struct array field */
                        if (strcmp(trimmed_val, "[]") == 0) {
                            const char *field_stype = struct_field_stype(func_name, trim(fname));
                            if (field_stype && is_struct_array_type(field_stype)) {
                                /* Use empty C++ initializer {} for struct arrays */
                                snprintf(val_c, sizeof(val_c), "{}");
                            } else {
                                /* Regular dynamic array */
                                translate_expr(trimmed_val, val_c, sizeof(val_c));
                            }
                        } else if (is_simple_identifier_token(trimmed_val)) {
                            const char *field_stype = struct_field_stype(func_name, trim(fname));
                            const char *field_ctype = field_stype ? simple_type_to_cpp(field_stype) : nullptr;
                            FuncInfo *ref_fn = find_func(trimmed_val);
                            if (ref_fn && field_ctype && starts_with(field_ctype, "FnPtr_")) {
                                /* Seed Fn pointer typing is return-only; cast refs to field type in constructor inits. */
                                snprintf(val_c, sizeof(val_c), "(%s)%s", field_ctype, trimmed_val);
                            } else {
                                translate_expr(trimmed_val, val_c, sizeof(val_c));
                            }
                        } else {
                            translate_expr(trimmed_val, val_c, sizeof(val_c));
                        }

                        if (!first_field) rpos += snprintf(result + rpos, sizeof(result) - rpos, ", ");
                        rpos += snprintf(result + rpos, sizeof(result) - rpos,
                                         ".%s = %s", trim(fname), val_c);
                        first_field = false;
                    } else {
                        /* Positional argument (shouldn't happen in well-formed Core Simple) */
                        /* Re-parse: put back what we consumed and handle as positional */
                        break;
                    }
                }
                rpos += snprintf(result + rpos, sizeof(result) - rpos, "}");
                snprintf(out, outsz, "%s", result);
                return;
            }

            /* Check if this is an enum variant */
            const char *enum_name = find_variant_enum(func_name);
            if (enum_name) {
                /* Simple enum: variant is just an integer constant */
                char enum_id[MAX_IDENT], var_id[MAX_IDENT];
                sanitize_cpp_ident_fragment(enum_name, enum_id, sizeof(enum_id));
                sanitize_cpp_ident_fragment(func_name, var_id, sizeof(var_id));
                snprintf(out, outsz, "%s_%s", enum_id, var_id);
                return;
            }

            /* Special built-in: int() */
            if (strcmp(func_name, "int") == 0) {
                char arg_c[MAX_LINE];
                translate_expr(trim(args), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "atoll(%s)", arg_c);
                return;
            }

            /* Regular function call */
            if (strlen(args) > 0) {
                /* Split by commas (respecting nesting) */
                char translated_args[MAX_LINE] = "";
                char arg_buf[MAX_LINE];
                int ab = 0;
                int adepth = 0;
                bool first_arg = true;

                for (int i = 0; args[i]; i++) {
                    if (args[i] == '(' || args[i] == '[') adepth++;
                    else if (args[i] == ')' || args[i] == ']') adepth--;
                    else if (args[i] == '"') {
                        arg_buf[ab++] = args[i++];
                        while (args[i] && args[i] != '"') {
                            if (args[i] == '\\') arg_buf[ab++] = args[i++];
                            arg_buf[ab++] = args[i++];
                        }
                        if (args[i]) arg_buf[ab++] = args[i];
                        continue;
                    }

                    if (args[i] == ',' && adepth == 0) {
                        arg_buf[ab] = '\0';
                        char arg_c[MAX_LINE];
                        translate_expr(trim(arg_buf), arg_c, sizeof(arg_c));
                        if (!first_arg) strcat(translated_args, ", ");
                        strcat(translated_args, arg_c);
                        first_arg = false;
                        ab = 0;
                        continue;
                    }
                    arg_buf[ab++] = args[i];
                }
                arg_buf[ab] = '\0';
                if (ab > 0) {
                    char arg_c[MAX_LINE];
                    translate_expr(trim(arg_buf), arg_c, sizeof(arg_c));
                    if (!first_arg) strcat(translated_args, ", ");
                    strcat(translated_args, arg_c);
                }

                snprintf(out, outsz, "%s(%s)", func_name, translated_args);
            } else {
                snprintf(out, outsz, "%s()", func_name);
            }
            return;
        }
    }

    /* Array indexing: arr[i] — find bracket not inside string literals */
    {
        const char *bracket = nullptr;
        for (const char *__bp = e; *__bp; __bp++) {
            if (*__bp == '"') {
                __bp++;
                while (*__bp && *__bp != '"') { if (*__bp == '\\') __bp++; __bp++; }
                if (!*__bp) break;
                continue;
            }
            if (*__bp == '(') break; /* Stop before function calls */
            if (*__bp == '[') { bracket = __bp; break; }
        }
        if (bracket) {
            char arr_name[MAX_IDENT];
            int ni = 0;
            const char *p = e;
            while (p < bracket) arr_name[ni++] = *p++;
            arr_name[ni] = '\0';

            p = bracket + 1;
            char idx_expr[MAX_LINE] = "";
            int depth = 1, ii = 0;
            while (*p && depth > 0) {
                if (*p == '[') depth++;
                else if (*p == ']') { depth--; if (depth == 0) break; }
                idx_expr[ii++] = *p++;
            }
            idx_expr[ii] = '\0';

            /* Slice: arr[start:end] */
            char *colon = strchr(idx_expr, ':');
            if (colon) {
                *colon = '\0';
                char start_c[MAX_LINE], end_c[MAX_LINE];
                if (strlen(idx_expr) > 0) translate_expr(trim(idx_expr), start_c, sizeof(start_c));
                else snprintf(start_c, sizeof(start_c), "0");
                if (strlen(colon + 1) > 0) translate_expr(trim(colon + 1), end_c, sizeof(end_c));
                else snprintf(end_c, sizeof(end_c), "spl_str_len(%s)", arr_name);

                char arr_c[MAX_LINE];
                translate_expr(trim(arr_name), arr_c, sizeof(arr_c));
                snprintf(out, outsz, "spl_str_slice(%s, %s, %s)", arr_c, start_c, end_c);
                return;
            }

            char arr_c[MAX_LINE], idx_c[MAX_LINE];
            translate_expr(trim(arr_name), arr_c, sizeof(arr_c));
            translate_expr(trim(idx_expr), idx_c, sizeof(idx_c));

            if (var_is_struct_array(trim(arr_name))) {
                snprintf(out, outsz, "%s[%s]", arr_c, idx_c);
            } else if (var_is_nested_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_array", arr_c, idx_c);
            } else if (var_is_float_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_float", arr_c, idx_c);
            } else if (var_is_text_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_str", arr_c, idx_c);
            } else if (var_is_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_int", arr_c, idx_c);
            } else if (var_is_text(trim(arr_name))) {
                snprintf(out, outsz, "spl_str_index_char(%s, %s)", arr_c, idx_c);
            } else {
                snprintf(out, outsz, "%s[%s]", arr_c, idx_c);
            }
            return;
        }
    }

    /* Check for bare enum variant (uppercase identifier) */
    if (is_upper_ident(e) && isalpha(*e)) {
        const char *ename = find_variant_enum(e);
        if (ename) {
            char enum_id[MAX_IDENT], var_id[MAX_IDENT];
            sanitize_cpp_ident_fragment(ename, enum_id, sizeof(enum_id));
            sanitize_cpp_ident_fragment(e, var_id, sizeof(var_id));
            snprintf(out, outsz, "%s_%s", enum_id, var_id);
            return;
        }
    }

    /* Simple identifier */
    if (isalpha(*e) || *e == '_') {
        snprintf(out, outsz, "%s", e);
        return;
    }

    /* Fallback — use ((int64_t)0) to avoid suffix issues with 0.field */
    snprintf(out, outsz, "/* TODO: %s */((int64_t)0)", e);
}

/* ===== Statement Translation ===== */

static void parse_var_decl(const char **pp, char *name, char *stype) {
    const char *p = *pp;
    int ni = 0;
    while (*p && *p != ':' && *p != '=' && *p != ' ') name[ni++] = *p++;
    name[ni] = '\0';
    p = skip_spaces(p);

    strcpy(stype, "i64"); /* default type */
    if (*p == ':') {
        p++; p = skip_spaces(p);
        int ti = 0;
        if (*p == '[') {
            int bracket_depth = 0;
            do {
                if (*p == '[') bracket_depth++;
                else if (*p == ']') bracket_depth--;
                stype[ti++] = *p++;
            } while (*p && bracket_depth > 0);
            /* Capture trailing ? for Option array types like [i64]? */
            if (*p == '?') stype[ti++] = *p++;
        } else {
            while (*p && *p != '=' && *p != ' ') stype[ti++] = *p++;
        }
        stype[ti] = '\0';
        ti = strlen(stype);
        while (ti > 0 && stype[ti-1] == ' ') stype[--ti] = '\0';
        p = skip_spaces(p);
    }
    if (*p == '=') { p++; p = skip_spaces(p); }

    /* Type inference from RHS when no explicit annotation */
    if (strcmp(stype, "i64") == 0 && *p != '\0') {
        const char *rhs = skip_spaces(p);
        if (*rhs == '"') {
            strcpy(stype, "text");
        } else if (*rhs == '[') {
            strcpy(stype, "[i64]");
        } else if (starts_with(rhs, "true") || starts_with(rhs, "false")) {
            strcpy(stype, "bool");
        } else if (strstr(rhs, " == ") || strstr(rhs, " != ") ||
                   strstr(rhs, " >= ") || strstr(rhs, " <= ") ||
                   strstr(rhs, " > ")  || strstr(rhs, " < ")  ||
                   strstr(rhs, " and ") || strstr(rhs, " or ") ||
                   starts_with(rhs, "not ")) {
            strcpy(stype, "bool");
        } else if (strcmp(rhs, "nil") == 0) {
            /* nil: keep as i64 */
        } else {
            /* Check if RHS starts with an uppercase ident → struct constructor */
            if (is_upper_ident(rhs)) {
                char rhs_name[MAX_IDENT] = "";
                int rni = 0;
                const char *rp = rhs;
                while (*rp && *rp != '(' && *rp != ' ' && rni < MAX_IDENT-1)
                    rhs_name[rni++] = *rp++;
                rhs_name[rni] = '\0';
                if (find_struct(rhs_name)) {
                    strcpy(stype, rhs_name);
                }
            }
            /* Check for array indexing type inference: arr[i] */
            {
                const char *lb = strchr(rhs, '[');
                if (lb && lb > rhs) {
                    char arr_n[MAX_IDENT] = "";
                    int ani = 0;
                    const char *ap2 = rhs;
                    while (ap2 < lb && ani < MAX_IDENT-1) arr_n[ani++] = *ap2++;
                    arr_n[ani] = '\0';
                    const char *arr_t = find_var_type(trim(arr_n));
                    /* Nested array indexing: [[X]][i] → [X] */
                    if (arr_t && arr_t[0] == '[' && arr_t[1] == '[') {
                        char elem[MAX_IDENT];
                        array_elem_stype(arr_t, elem, sizeof(elem));
                        strcpy(stype, elem);
                    }
                    /* Float array indexing: [f64][i] → f64 */
                    else if (arr_t && strcmp(arr_t, "[f64]") == 0) {
                        strcpy(stype, "f64");
                    }
                    /* Text array indexing: [text][i] → text */
                    else if (arr_t && strcmp(arr_t, "[text]") == 0) {
                        strcpy(stype, "text");
                    }
                    /* Text indexing: text[i] → text (single-char string) */
                    else if (arr_t && strcmp(arr_t, "text") == 0) {
                        strcpy(stype, "text");
                    }
                    else if (arr_t && type_is_struct_array(arr_t)) {
                        char elem[MAX_IDENT];
                        struct_array_elem_type(arr_t, elem, sizeof(elem));
                        /* Check for field access after bracket: arr[i].field */
                        const char *rb2 = strchr(lb, ']');
                        const char *dot_after = rb2 ? strchr(rb2, '.') : nullptr;
                        if (dot_after) {
                            /* arr[i].field — infer from struct field type */
                            const char *fname = dot_after + 1;
                            char field_n[MAX_IDENT] = "";
                            int fni2 = 0;
                            while (*fname && *fname != '.' && *fname != '(' && *fname != '[' && *fname != ' ' && fni2 < MAX_IDENT-1)
                                field_n[fni2++] = *fname++;
                            field_n[fni2] = '\0';
                            const char *ft = struct_field_stype(elem, trim(field_n));
                            if (ft) strcpy(stype, ft);
                            else strcpy(stype, elem);
                        } else {
                            strcpy(stype, elem);
                        }
                    }
                }
            }
            /* Check for function return type */
            char func[MAX_IDENT] = "";
            int fni = 0;
            const char *fp = rhs;
            while (*fp && *fp != '(' && *fp != '.' && *fp != ' ' && fni < MAX_IDENT-1)
                func[fni++] = *fp++;
            func[fni] = '\0';
            /* Only infer text type for simple variable assignment, not method calls */
            const char *dot = strchr(rhs, '.');
            if (var_is_text(func) && !dot) {
                strcpy(stype, "text");
            }
            /* Method result type inference */
            if (dot) {
                char obj_name[MAX_IDENT] = "";
                int oi = 0;
                const char *op = rhs;
                while (op < dot && oi < MAX_IDENT-1) obj_name[oi++] = *op++;
                obj_name[oi] = '\0';
                const char *method = dot + 1;
                /* Extract method name (before '(') */
                char mname[MAX_IDENT] = "";
                int mni = 0;
                const char *mp = method;
                while (*mp && *mp != '(' && mni < MAX_IDENT-1) mname[mni++] = *mp++;
                mname[mni] = '\0';

                /* Option .unwrap() / .is_some() / .is_none() */
                if (var_is_option(obj_name)) {
                    if (strcmp(mname, "unwrap") == 0) {
                        char base[MAX_IDENT];
                        const char *vt = find_var_type(obj_name);
                        option_base_stype(vt, base, sizeof(base));
                        strcpy(stype, base);
                    } else if (strcmp(mname, "is_some") == 0 || strcmp(mname, "is_none") == 0) {
                        strcpy(stype, "bool");
                    }
                }
                /* Struct field Option: obj.field.unwrap() / obj.field.is_some() etc. */
                const char *second_dot = strchr(method, '.');
                if (second_dot) {
                    char field_name[MAX_IDENT] = "";
                    int fni3 = 0;
                    const char *fp2 = method;
                    while (fp2 < second_dot && fni3 < MAX_IDENT-1) field_name[fni3++] = *fp2++;
                    field_name[fni3] = '\0';
                    const char *after_field = second_dot + 1;
                    char after_mname[MAX_IDENT] = "";
                    int ami = 0;
                    const char *ap = after_field;
                    while (*ap && *ap != '(' && ami < MAX_IDENT-1) after_mname[ami++] = *ap++;
                    after_mname[ami] = '\0';
                    /* Check if obj is a struct and field is Option */
                    const char *o_st = var_struct_type(obj_name);
                    if (o_st) {
                        const char *ft = struct_field_stype(o_st, field_name);
                        if (ft && type_is_option(ft)) {
                            if (strcmp(after_mname, "unwrap") == 0) {
                                char base[MAX_IDENT];
                                option_base_stype(ft, base, sizeof(base));
                                strcpy(stype, base);
                            } else if (strcmp(after_mname, "is_some") == 0 || strcmp(after_mname, "is_none") == 0) {
                                strcpy(stype, "bool");
                            }
                        }
                    }
                }

                if (var_is_text(obj_name)) {
                    if (starts_with(method, "trim(") || starts_with(method, "replace(") ||
                        starts_with(method, "slice("))
                        strcpy(stype, "text");
                    else if (starts_with(method, "split("))
                        strcpy(stype, "[text]");
                    else if (starts_with(method, "starts_with(") || starts_with(method, "ends_with(") ||
                             starts_with(method, "contains("))
                        strcpy(stype, "bool");
                }
                if (var_is_array(obj_name) && starts_with(method, "join(")) {
                    strcpy(stype, "text");
                }
                /* Struct field access or method: obj.field / obj.method() */
                const char *obj_st = var_struct_type(obj_name);
                if (obj_st) {
                    /* First check if it's a struct field */
                    const char *fld_t = struct_field_stype(obj_st, mname);
                    if (fld_t) strcpy(stype, fld_t);
                    /* Then check if it's a method (overrides field if same name) */
                    FuncInfo *meth = find_method(obj_st, mname);
                    if (meth) strcpy(stype, meth->simple_ret);
                }
                /* Static method: StructName.method() → lookup StructName__method */
                if (find_struct(obj_name)) {
                    FuncInfo *meth = find_method(obj_name, mname);
                    if (meth) strcpy(stype, meth->simple_ret);
                }
            }
            FuncInfo *fn = find_func(func);
            if (fn) {
                if (type_is_option(fn->simple_ret)) strcpy(stype, fn->simple_ret);
                else if (strcmp(fn->simple_ret, "text") == 0) strcpy(stype, "text");
                else if (strcmp(fn->simple_ret, "bool") == 0) strcpy(stype, "bool");
                else if (fn->simple_ret[0] == '[') strcpy(stype, fn->simple_ret);
                else if (find_struct(fn->simple_ret)) {
                    /* Function returns a struct — check for field access after call */
                    if (dot) {
                        /* Find the field name after the last dot */
                        const char *last_d = strrchr(rhs, '.');
                        if (last_d) {
                            char fn_field[MAX_IDENT] = "";
                            int ffi = 0;
                            const char *ffp = last_d + 1;
                            while (*ffp && *ffp != '(' && *ffp != '[' && *ffp != ' ' && ffi < MAX_IDENT-1)
                                fn_field[ffi++] = *ffp++;
                            fn_field[ffi] = '\0';
                            const char *fft = struct_field_stype(fn->simple_ret, fn_field);
                            if (fft) strcpy(stype, fft);
                            else strcpy(stype, fn->simple_ret);
                        }
                    } else {
                        strcpy(stype, fn->simple_ret);
                    }
                }
            }
            /* ?? operator: result type is the base type of the Option (overrides fn lookup) */
            if (strstr(rhs, " ?? ")) {
                /* Find the LHS of ?? */
                char lhs_buf[MAX_LINE];
                strncpy(lhs_buf, rhs, MAX_LINE - 1);
                lhs_buf[MAX_LINE - 1] = '\0';
                char *qq = strstr(lhs_buf, " ?? ");
                if (qq) {
                    *qq = '\0';
                    char *lhs_trimmed = trim(lhs_buf);
                    /* Check if LHS variable is Option */
                    if (var_is_option(lhs_trimmed)) {
                        char base[MAX_IDENT];
                        const char *vt = find_var_type(lhs_trimmed);
                        option_base_stype(vt, base, sizeof(base));
                        strcpy(stype, base);
                    }
                    /* Check if LHS is a function call returning Option */
                    char fn_name[MAX_IDENT] = "";
                    int fni2 = 0;
                    const char *lp = lhs_trimmed;
                    while (*lp && *lp != '(' && fni2 < MAX_IDENT-1) fn_name[fni2++] = *lp++;
                    fn_name[fni2] = '\0';
                    FuncInfo *fn2 = find_func(fn_name);
                    if (fn2 && type_is_option(fn2->simple_ret)) {
                        char base[MAX_IDENT];
                        option_base_stype(fn2->simple_ret, base, sizeof(base));
                        strcpy(stype, base);
                    }
                }
            }
        }
        /* Slice expression: anything[a:b] returns text */
        if (strcmp(stype, "i64") == 0) {
            const char *br = strchr(rhs, '[');
            if (br) {
                const char *bp2 = br + 1;
                int d2 = 1;
                while (*bp2 && d2 > 0) {
                    if (*bp2 == '[') d2++;
                    else if (*bp2 == ']') { d2--; if (d2 == 0) break; }
                    else if (*bp2 == ':' && d2 == 1) { strcpy(stype, "text"); break; }
                    bp2++;
                }
            }
        }
        /* expr_is_text fallback: check if the RHS evaluates to text */
        bool has_bool_ops =
            strstr(rhs, " == ") || strstr(rhs, " != ") ||
            strstr(rhs, " >= ") || strstr(rhs, " <= ") ||
            strstr(rhs, " > ")  || strstr(rhs, " < ")  ||
            strstr(rhs, " and ") || strstr(rhs, " or ") ||
            starts_with(rhs, "not ");
        if (strcmp(stype, "i64") == 0 && !has_bool_ops && expr_is_text(rhs)) {
            strcpy(stype, "text");
        }
    }

    *pp = p;
}

static void extract_condition(const char *line, int skip, char *cond, int condsz) {
    const char *p = line + skip;
    int len = strlen(p);
    if (len > 0 && p[len-1] == ':') len--;
    if (len >= condsz) len = condsz - 1;
    strncpy(cond, p, len);
    cond[len] = '\0';
    len = strlen(cond);
    while (len > 0 && (cond[len-1] == ' ' || cond[len-1] == '\t')) cond[--len] = '\0';
}

static void emit_array_literal_pushes(const char *arr_name, const char *rhs, int c_indent) {
    if (rhs[0] != '[') return;
    bool is_struct_arr = var_is_struct_array(arr_name);
    bool is_text_arr = var_is_text_array(arr_name);
    bool is_nested_arr = var_is_nested_array(arr_name);
    const char *p = rhs + 1;
    char elem[MAX_LINE];
    int ei = 0;
    int depth = 0;

    while (*p && !(*p == ']' && depth == 0)) {
        if (*p == '"') { elem[ei++] = *p++; while (*p && *p != '"') { if (*p == '\\') elem[ei++] = *p++; elem[ei++] = *p++; } if (*p) elem[ei++] = *p++; continue; }
        if (*p == '[') depth++;
        else if (*p == ']') depth--;
        else if (*p == ',' && depth == 0) {
            elem[ei] = '\0';
            if (ei > 0) {
                char ec[MAX_LINE];
                translate_expr(trim(elem), ec, sizeof(ec));
                emit_indent(c_indent);
                if (is_struct_arr)
                    emit("%s.push_back(%s);\n", arr_name, ec);
                else if (is_text_arr)
                    emit("spl_array_push(%s, spl_str(%s));\n", arr_name, ec);
                else if (is_nested_arr)
                    emit("spl_array_push(%s, spl_array_val(%s));\n", arr_name, ec);
                else if (ec[0] == '"')
                    emit("spl_array_push(%s, spl_str(%s));\n", arr_name, ec);
                else
                    emit("spl_array_push(%s, spl_int(%s));\n", arr_name, ec);
            }
            ei = 0;
            p++;
            continue;
        }
        elem[ei++] = *p++;
    }
    elem[ei] = '\0';
    if (ei > 0) {
        char *te = trim(elem);
        if (strlen(te) > 0) {
            char ec[MAX_LINE];
            translate_expr(te, ec, sizeof(ec));
            emit_indent(c_indent);
            if (is_struct_arr)
                emit("%s.push_back(%s);\n", arr_name, ec);
            else if (is_text_arr)
                emit("spl_array_push(%s, spl_str(%s));\n", arr_name, ec);
            else if (is_nested_arr)
                emit("spl_array_push(%s, spl_array_val(%s));\n", arr_name, ec);
            else if (ec[0] == '"')
                emit("spl_array_push(%s, spl_str(%s));\n", arr_name, ec);
            else
                emit("spl_array_push(%s, spl_int(%s));\n", arr_name, ec);
        }
    }
}

/* translate_block: process indented lines starting at *line_idx.
 * Processes lines with indent > base_indent. c_indent is the C++ indentation level. */
static void translate_block(int *line_idx, int base_indent, int c_indent) {
    while (*line_idx < num_lines) {
        const char *line = source_lines[*line_idx];
        int ind = indent_level(line);
        const char *trimmed = trim(line);

        if (trimmed[0] == '\0' || trimmed[0] == '#') { (*line_idx)++; continue; }
        if (ind <= base_indent) break;

        /* asm match: — multi-target dispatch */
        if (strcmp(trimmed, "asm match:") == 0) {
            int match_base_indent = ind;
            (*line_idx)++;
            bool emitted = false;
            while (*line_idx < num_lines) {
                const char *aline = source_lines[*line_idx];
                const char *atrim = trim(aline);
                int aind = indent_level(aline);
                if (atrim[0] == '\0' || atrim[0] == '#') { (*line_idx)++; continue; }
                if (aind <= match_base_indent) break;

                /* case _: */
                if (strcmp(atrim, "case _:") == 0) {
                    (*line_idx)++;
                    /* Read body of wildcard arm */
                    int arm_base = aind;
                    if (!emitted) {
                        /* Collect asm body or compile_error */
                        while (*line_idx < num_lines) {
                            const char *bline = source_lines[*line_idx];
                            const char *btrim = trim(bline);
                            int bind = indent_level(bline);
                            if (btrim[0] == '\0' || btrim[0] == '#') { (*line_idx)++; continue; }
                            if (bind <= arm_base) break;
                            char ce_msg[256];
                            if (parse_compile_error_msg(btrim, ce_msg, sizeof(ce_msg))) {
                                emit_indent(c_indent);
                                emit("/* asm match wildcard: compile_error */\n");
                                emit_indent(c_indent);
                                emit("static_assert(false, \"%s\");\n", ce_msg);
                                emitted = true;
                                (*line_idx)++;
                                break;
                            }
                            /* Regular asm body */
                            char line_text[MAX_LINE];
                            normalize_asm_line(btrim, line_text, sizeof(line_text));
                            emit_asm_stmt(line_text, c_indent);
                            emitted = true;
                            (*line_idx)++;
                        }
                    }
                    /* Skip remaining body lines of this arm */
                    while (*line_idx < num_lines) {
                        const char *bline = source_lines[*line_idx];
                        const char *btrim = trim(bline);
                        int bind = indent_level(bline);
                        if (btrim[0] == '\0' || btrim[0] == '#') { (*line_idx)++; continue; }
                        if (bind <= arm_base) break;
                        (*line_idx)++;
                    }
                    continue;
                }

                /* case [...]: */
                if (starts_with(atrim, "case ") && strchr(atrim, '[')) {
                    char bracket_content[256];
                    AsmTargetSpec spec;
                    bool has_spec = extract_bracket_content(atrim, bracket_content, sizeof(bracket_content))
                                    && parse_asm_target_spec(bracket_content, &spec);

                    bool matches = has_spec && match_asm_target_spec(&spec);

                    (*line_idx)++;
                    int arm_base = aind;

                    if (matches && !emitted) {
                        /* This arm matches — collect its body */
                        while (*line_idx < num_lines) {
                            const char *bline = source_lines[*line_idx];
                            const char *btrim = trim(bline);
                            int bind = indent_level(bline);
                            if (btrim[0] == '\0' || btrim[0] == '#') { (*line_idx)++; continue; }
                            if (bind <= arm_base) break;
                            char ce_msg[256];
                            if (parse_compile_error_msg(btrim, ce_msg, sizeof(ce_msg))) {
                                emit_indent(c_indent);
                                emit("static_assert(false, \"%s\");\n", ce_msg);
                                emitted = true;
                                (*line_idx)++;
                                break;
                            }
                            char line_text[MAX_LINE];
                            normalize_asm_line(btrim, line_text, sizeof(line_text));
                            emit_asm_stmt(line_text, c_indent);
                            emitted = true;
                            (*line_idx)++;
                        }
                    }
                    /* Skip remaining body lines of this arm */
                    while (*line_idx < num_lines) {
                        const char *bline = source_lines[*line_idx];
                        const char *btrim = trim(bline);
                        int bind = indent_level(bline);
                        if (btrim[0] == '\0' || btrim[0] == '#') { (*line_idx)++; continue; }
                        if (bind <= arm_base) break;
                        (*line_idx)++;
                    }
                    continue;
                }

                /* Unknown line inside asm match */
                (*line_idx)++;
            }
            if (!emitted) {
                emit_indent(c_indent);
                emit("static_assert(false, \"no asm match case for target\");\n");
            }
            continue;
        }

        /* asm assert [...] — compile-time target guard */
        if (starts_with(trimmed, "asm assert ") && strchr(trimmed, '[')) {
            char bracket_content[256];
            AsmTargetSpec spec;
            if (extract_bracket_content(trimmed, bracket_content, sizeof(bracket_content))
                && parse_asm_target_spec(bracket_content, &spec)) {
                if (!match_asm_target_spec(&spec)) {
                    emit_indent(c_indent);
                    emit("static_assert(false, \"asm assert: target does not match\");\n");
                }
            }
            (*line_idx)++;
            continue;
        }

        /* compile_error("msg") — standalone */
        if (starts_with(trimmed, "compile_error(")) {
            char ce_msg[256];
            if (parse_compile_error_msg(trimmed, ce_msg, sizeof(ce_msg))) {
                emit_indent(c_indent);
                emit("static_assert(false, \"%s\");\n", ce_msg);
            }
            (*line_idx)++;
            continue;
        }

        /* asm: block form */
        if (strcmp(trimmed, "asm:") == 0) {
            int asm_base_indent = ind;
            char asm_text[MAX_ASM_TEXT];
            asm_text[0] = '\0';
            (*line_idx)++;
            while (*line_idx < num_lines) {
                const char *aline = source_lines[*line_idx];
                const char *atrim = trim(aline);
                int aind = indent_level(aline);
                if (atrim[0] == '\0' || atrim[0] == '#') { (*line_idx)++; continue; }
                if (aind <= asm_base_indent) break;
                char line_text[MAX_LINE];
                normalize_asm_line(atrim, line_text, sizeof(line_text));
                asm_append_line(asm_text, sizeof(asm_text), line_text);
                (*line_idx)++;
            }
            emit_asm_stmt(asm_text, c_indent);
            continue;
        }

        /* asm { ... } block */
        if (starts_with(trimmed, "asm {") || strcmp(trimmed, "asm{") == 0) {
            char asm_text[MAX_ASM_TEXT];
            asm_text[0] = '\0';
            const char *open = strchr(trimmed, '{');
            const char *close = open ? strrchr(open + 1, '}') : nullptr;
            if (open && close && close > open) {
                char inside[MAX_LINE];
                int ilen = (int)(close - open - 1);
                if (ilen >= (int)sizeof(inside)) ilen = (int)sizeof(inside) - 1;
                if (ilen < 0) ilen = 0;
                strncpy(inside, open + 1, ilen);
                inside[ilen] = '\0';
                char line_text[MAX_LINE];
                normalize_asm_line(inside, line_text, sizeof(line_text));
                asm_append_line(asm_text, sizeof(asm_text), line_text);
                (*line_idx)++;
            } else {
                (*line_idx)++;
                while (*line_idx < num_lines) {
                    const char *aline = source_lines[*line_idx];
                    const char *atrim = trim(aline);
                    if (atrim[0] == '\0' || atrim[0] == '#') { (*line_idx)++; continue; }
                    if (strcmp(atrim, "}") == 0) { (*line_idx)++; break; }
                    char line_text[MAX_LINE];
                    normalize_asm_line(atrim, line_text, sizeof(line_text));
                    asm_append_line(asm_text, sizeof(asm_text), line_text);
                    (*line_idx)++;
                }
            }
            emit_asm_stmt(asm_text, c_indent);
            continue;
        }

        /* asm "..." inline */
        if (starts_with(trimmed, "asm ")) {
            const char *payload = skip_spaces(trimmed + 3);
            char asm_text[MAX_ASM_TEXT];
            normalize_asm_line(payload, asm_text, sizeof(asm_text));
            emit_asm_stmt(asm_text, c_indent);
            (*line_idx)++;
            continue;
        }

        /* Single-line if */
        if (starts_with(trimmed, "if ") && !ends_with(trimmed, ":")) {
            const char *colon_pos = nullptr;
            int paren = 0;
            for (const char *cp = trimmed + 3; *cp; cp++) {
                if (*cp == '(' || *cp == '[') paren++;
                else if (*cp == ')' || *cp == ']') paren--;
                else if (*cp == '"') { cp++; while (*cp && *cp != '"') { if (*cp == '\\') cp++; cp++; } }
                else if (*cp == ':' && paren == 0) { colon_pos = cp; break; }
            }
            if (colon_pos) {
                char cond[MAX_LINE];
                int clen = colon_pos - (trimmed + 3);
                strncpy(cond, trimmed + 3, clen);
                cond[clen] = '\0';
                int cl = strlen(cond);
                while (cl > 0 && cond[cl-1] == ' ') cond[--cl] = '\0';

                char cond_c[MAX_LINE];
                translate_expr(cond, cond_c, sizeof(cond_c));

                const char *body = skip_spaces(colon_pos + 1);
                emit_indent(c_indent);
                emit("if (%s) { ", cond_c);
                if (starts_with(body, "return ")) {
                    const char *ret_val = skip_spaces(body + 7);
                    if (current_func && type_is_option(current_func->simple_ret) && strcmp(ret_val, "nil") == 0) {
                        emit("return {};");
                    } else {
                        char expr_c[MAX_LINE];
                        translate_expr(body + 7, expr_c, sizeof(expr_c));
                        emit("return %s;", expr_c);
                    }
                } else if (strcmp(body, "return") == 0) {
                    emit("return;");
                } else if (strcmp(body, "break") == 0) {
                    emit("break;");
                } else if (strcmp(body, "continue") == 0) {
                    emit("continue;");
                } else {
                    translate_statement(body, 0);
                }
                emit(" }\n");
                (*line_idx)++;
                continue;
            }
        }

        /* if cond: (block) */
        if (starts_with(trimmed, "if ") && ends_with(trimmed, ":")) {
            char cond[MAX_LINE], cond_c[MAX_LINE];
            extract_condition(trimmed, 3, cond, sizeof(cond));
            translate_expr(cond, cond_c, sizeof(cond_c));
            emit_indent(c_indent);
            emit("if (%s) {\n", cond_c);
            (*line_idx)++;
            translate_block(line_idx, ind, c_indent + 1);
            emit_indent(c_indent);
            emit("}");

            while (*line_idx < num_lines) {
                const char *next = source_lines[*line_idx];
                const char *nt = trim(next);
                int ni = indent_level(next);
                if (nt[0] == '\0' || nt[0] == '#') { (*line_idx)++; continue; }
                if (ni != ind) break;

                if (starts_with(nt, "elif ") && ends_with(nt, ":")) {
                    char econd[MAX_LINE], econd_c[MAX_LINE];
                    extract_condition(nt, 5, econd, sizeof(econd));
                    translate_expr(econd, econd_c, sizeof(econd_c));
                    emit(" else if (%s) {\n", econd_c);
                    (*line_idx)++;
                    translate_block(line_idx, ni, c_indent + 1);
                    emit_indent(c_indent);
                    emit("}");
                } else if (strcmp(nt, "else:") == 0) {
                    emit(" else {\n");
                    (*line_idx)++;
                    translate_block(line_idx, ni, c_indent + 1);
                    emit_indent(c_indent);
                    emit("}");
                } else {
                    break;
                }
            }
            emit("\n");
            continue;
        }

        /* while cond: */
        if (starts_with(trimmed, "while ") && ends_with(trimmed, ":")) {
            char cond[MAX_LINE], cond_c[MAX_LINE];
            extract_condition(trimmed, 6, cond, sizeof(cond));
            translate_expr(cond, cond_c, sizeof(cond_c));
            emit_indent(c_indent);
            emit("while (%s) {\n", cond_c);
            (*line_idx)++;
            translate_block(line_idx, ind, c_indent + 1);
            emit_indent(c_indent);
            emit("}\n");
            continue;
        }

        /* for loops */
        if (starts_with(trimmed, "for ") && ends_with(trimmed, ":")) {
            char body[MAX_LINE];
            extract_condition(trimmed, 4, body, sizeof(body));
            char var_name[MAX_IDENT] = "";
            int vi = 0;
            const char *p = body;
            while (*p && *p != ' ') var_name[vi++] = *p++;
            var_name[vi] = '\0';
            p = skip_spaces(p);
            if (starts_with(p, "in ")) p += 3;
            p = skip_spaces(p);

            add_var(var_name, "i64");

            char *dotdot = strstr((char*)p, "..");
            if (dotdot) {
                char start_s[MAX_LINE], end_s[MAX_LINE];
                int slen = dotdot - p;
                strncpy(start_s, p, slen);
                start_s[slen] = '\0';
                strcpy(end_s, dotdot + 2);

                char start_c[MAX_LINE], end_c[MAX_LINE];
                translate_expr(trim(start_s), start_c, sizeof(start_c));
                translate_expr(trim(end_s), end_c, sizeof(end_c));

                emit_indent(c_indent);
                emit("for (int64_t %s = %s; %s < %s; %s++) {\n",
                     var_name, start_c, var_name, end_c, var_name);
            } else if (starts_with(p, "range(")) {
                char range_arg[MAX_LINE];
                const char *ra = p + 6;
                int rai = 0;
                int rdepth = 1;
                while (*ra && rdepth > 0) {
                    if (*ra == '(') rdepth++;
                    else if (*ra == ')') { rdepth--; if (rdepth == 0) break; }
                    range_arg[rai++] = *ra++;
                }
                range_arg[rai] = '\0';
                char *comma = nullptr;
                int cdepth = 0;
                for (int ci = 0; range_arg[ci]; ci++) {
                    if (range_arg[ci] == '(' || range_arg[ci] == '[') cdepth++;
                    else if (range_arg[ci] == ')' || range_arg[ci] == ']') cdepth--;
                    else if (range_arg[ci] == ',' && cdepth == 0) { comma = &range_arg[ci]; break; }
                }
                if (comma) {
                    *comma = '\0';
                    char start_c[MAX_LINE], end_c[MAX_LINE];
                    translate_expr(trim(range_arg), start_c, sizeof(start_c));
                    translate_expr(trim(comma + 1), end_c, sizeof(end_c));
                    emit_indent(c_indent);
                    emit("for (int64_t %s = %s; %s < %s; %s++) {\n",
                         var_name, start_c, var_name, end_c, var_name);
                } else {
                    char range_c[MAX_LINE];
                    translate_expr(trim(range_arg), range_c, sizeof(range_c));
                    emit_indent(c_indent);
                    emit("for (int64_t %s = 0; %s < %s; %s++) {\n",
                         var_name, var_name, range_c, var_name);
                }
            } else if (!find_var_type(trim((char*)p)) &&
                       !strchr(p, '.') && !strchr(p, '(') && !strchr(p, '[')) {
                /* for i in N: — treat numeric/simple expr as range */
                char range_c[MAX_LINE];
                translate_expr(trim((char*)p), range_c, sizeof(range_c));
                emit_indent(c_indent);
                emit("for (int64_t %s = 0; %s < %s; %s++) {\n",
                     var_name, var_name, range_c, var_name);
            } else {
                /* for item in array */
                char arr_c[MAX_LINE];
                translate_expr(trim((char*)p), arr_c, sizeof(arr_c));
                const char *arr_stype = find_var_type(trim((char*)p));
                if (arr_stype && strcmp(arr_stype, "text") == 0) {
                    add_var(var_name, "text");
                    emit_indent(c_indent);
                    emit("for (int64_t __%s_i = 0; __%s_i < spl_str_len(%s); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("const char* %s = spl_str_index_char(%s, __%s_i);\n",
                         var_name, arr_c, var_name);
                } else if (arr_stype && type_is_struct_array(arr_stype)) {
                    char elem_type[MAX_IDENT];
                    struct_array_elem_type(arr_stype, elem_type, sizeof(elem_type));
                    add_var(var_name, elem_type);
                    emit_indent(c_indent);
                    emit("for (size_t __%s_i = 0; __%s_i < %s.size(); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("%s %s = %s[__%s_i];\n",
                         elem_type, var_name, arr_c, var_name);
                } else if (arr_stype && strcmp(arr_stype, "[text]") == 0) {
                    add_var(var_name, "text");
                    emit_indent(c_indent);
                    emit("for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("const char* %s = spl_array_get(%s, __%s_i).as_str;\n",
                         var_name, arr_c, var_name);
                } else if (arr_stype && strcmp(arr_stype, "[f64]") == 0) {
                    add_var(var_name, "f64");
                    emit_indent(c_indent);
                    emit("for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("double %s = spl_array_get(%s, __%s_i).as_float;\n",
                         var_name, arr_c, var_name);
                } else if (arr_stype && arr_stype[0] == '[' && arr_stype[1] == '[') {
                    /* Nested array: [[X]] → each element is SplArray* */
                    char elem_stype[MAX_IDENT];
                    array_elem_stype(arr_stype, elem_stype, sizeof(elem_stype));
                    add_var(var_name, elem_stype);
                    emit_indent(c_indent);
                    emit("for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("SplArray* %s = spl_array_get(%s, __%s_i).as_array;\n",
                         var_name, arr_c, var_name);
                } else {
                    emit_indent(c_indent);
                    emit("for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                         var_name, var_name, arr_c, var_name);
                    emit_indent(c_indent + 1);
                    emit("int64_t %s = spl_array_get(%s, __%s_i).as_int;\n",
                         var_name, arr_c, var_name);
                }
            }

            (*line_idx)++;
            translate_block(line_idx, ind, c_indent + 1);
            emit_indent(c_indent);
            emit("}\n");
            continue;
        }

        /* match expr: */
        if (starts_with(trimmed, "match ") && ends_with(trimmed, ":")) {
            char match_expr[MAX_LINE], match_c[MAX_LINE];
            extract_condition(trimmed, 6, match_expr, sizeof(match_expr));
            translate_expr(match_expr, match_c, sizeof(match_c));
            emit_indent(c_indent);
            emit("switch (%s) {\n", match_c);
            (*line_idx)++;

            while (*line_idx < num_lines) {
                const char *cline = source_lines[*line_idx];
                const char *ct = trim(cline);
                int ci = indent_level(cline);
                if (ct[0] == '\0' || ct[0] == '#') { (*line_idx)++; continue; }
                if (ci <= ind) break;

                if (starts_with(ct, "case ") && ends_with(ct, ":")) {
                    char case_val[MAX_LINE];
                    extract_condition(ct, 5, case_val, sizeof(case_val));
                    /* Handle pipe-separated values */
                    char *pipe = strchr(case_val, '|');
                    if (pipe) {
                        char *tok = case_val;
                        while (tok) {
                            char *next_pipe = strchr(tok, '|');
                            if (next_pipe) *next_pipe = '\0';
                            char *tv = trim(tok);
                            if (strcmp(tv, "_") == 0) {
                                emit_indent(c_indent + 1);
                                emit("default:\n");
                            } else {
                                /* Handle EnumName.Variant notation */
                                char *dot = strchr(tv, '.');
                                if (dot) {
                                    *dot = '\0';
                                    const char *enum_name = tv;
                                    const char *variant = dot + 1;
                                    char enum_id[MAX_IDENT], var_id[MAX_IDENT];
                                    sanitize_cpp_ident_fragment(enum_name, enum_id, sizeof(enum_id));
                                    sanitize_cpp_ident_fragment(variant, var_id, sizeof(var_id));
                                    emit_indent(c_indent + 1);
                                    emit("case %s_%s:\n", enum_id, var_id);
                                } else {
                                    /* Check if it's an enum variant */
                                    const char *ev_enum = find_variant_enum(tv);
                                    emit_indent(c_indent + 1);
                                    if (ev_enum) {
                                        char enum_id[MAX_IDENT], var_id[MAX_IDENT];
                                        sanitize_cpp_ident_fragment(ev_enum, enum_id, sizeof(enum_id));
                                        sanitize_cpp_ident_fragment(tv, var_id, sizeof(var_id));
                                        emit("case %s_%s:\n", enum_id, var_id);
                                    }
                                    else
                                        emit("case %s:\n", tv);
                                }
                            }
                            tok = next_pipe ? next_pipe + 1 : nullptr;
                        }
                    } else if (strcmp(trim(case_val), "_") == 0) {
                        emit_indent(c_indent + 1);
                        emit("default:\n");
                    } else {
                        char *cv = trim(case_val);
                        /* Handle EnumName.Variant notation */
                        char *dot = strchr(cv, '.');
                        if (dot) {
                            *dot = '\0';
                            const char *enum_name = cv;
                            const char *variant = dot + 1;
                            char enum_id[MAX_IDENT], var_id[MAX_IDENT];
                            sanitize_cpp_ident_fragment(enum_name, enum_id, sizeof(enum_id));
                            sanitize_cpp_ident_fragment(variant, var_id, sizeof(var_id));
                            emit_indent(c_indent + 1);
                            emit("case %s_%s:\n", enum_id, var_id);
                        } else {
                            const char *ev_enum = find_variant_enum(cv);
                            emit_indent(c_indent + 1);
                            if (ev_enum) {
                                char enum_id[MAX_IDENT], var_id[MAX_IDENT];
                                sanitize_cpp_ident_fragment(ev_enum, enum_id, sizeof(enum_id));
                                sanitize_cpp_ident_fragment(cv, var_id, sizeof(var_id));
                                emit("case %s_%s:\n", enum_id, var_id);
                            }
                            else
                                emit("case %s:\n", cv);
                        }
                    }
                    (*line_idx)++;
                    emit_indent(c_indent + 1);
                    emit("{\n");
                    translate_block(line_idx, ci, c_indent + 2);
                    emit_indent(c_indent + 2);
                    emit("break;\n");
                    emit_indent(c_indent + 1);
                    emit("}\n");
                } else {
                    (*line_idx)++;
                }
            }
            emit_indent(c_indent);
            emit("}\n");
            continue;
        }

        /* Skip use/export/import/from/mod */
        if (starts_with(trimmed, "use ") || starts_with(trimmed, "export ") ||
            starts_with(trimmed, "import ") || starts_with(trimmed, "from ") ||
            starts_with(trimmed, "pub mod ") || starts_with(trimmed, "mod ") || starts_with(trimmed, "pub ")) {
            (*line_idx)++;
            continue;
        }

        /* val declaration */
        if (starts_with(trimmed, "val ")) {
            const char *p = trimmed + 4;
            char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
            parse_var_decl(&p, name, stype);
            add_var(name, stype);

            if (stype[0] == '[' && *p == '[') {
                emit_indent(c_indent);
                if (type_is_struct_array(stype)) {
                    emit("%s %s = {};\n", simple_type_to_cpp(stype), name);
                } else {
                    emit("%s %s = spl_array_new();\n", simple_type_to_cpp(stype), name);
                }
                emit_array_literal_pushes(name, p, c_indent);
            } else if (type_is_option(stype)) {
                const char *ct = simple_type_to_cpp(stype);
                const char *rhs = skip_spaces(p);
                emit_indent(c_indent);
                if (*rhs == '\0' || strcmp(rhs, "nil") == 0) {
                    emit("%s %s = {};\n", ct, name);
                } else {
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("%s %s = %s;\n", ct, name, expr_c);
                }
            } else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit_indent(c_indent);
                const char *ct = simple_type_to_cpp(stype);
                emit("%s %s = %s;\n", ct, name, expr_c);
            }
            (*line_idx)++;
            continue;
        }

        /* var declaration */
        if (starts_with(trimmed, "var ")) {
            const char *p = trimmed + 4;
            char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
            parse_var_decl(&p, name, stype);
            add_var(name, stype);

            if (stype[0] == '[' && *p == '[') {
                emit_indent(c_indent);
                if (type_is_struct_array(stype)) {
                    emit("%s %s = {};\n", simple_type_to_cpp(stype), name);
                } else {
                    emit("%s %s = spl_array_new();\n", simple_type_to_cpp(stype), name);
                }
                emit_array_literal_pushes(name, p, c_indent);
            } else if (stype[0] == '[') {
                emit_indent(c_indent);
                if (type_is_struct_array(stype)) {
                    emit("%s %s = {};\n", simple_type_to_cpp(stype), name);
                } else {
                    emit("%s %s = spl_array_new();\n", simple_type_to_cpp(stype), name);
                }
            } else if (type_is_option(stype)) {
                const char *ct = simple_type_to_cpp(stype);
                const char *rhs = skip_spaces(p);
                emit_indent(c_indent);
                if (*rhs == '\0' || strcmp(rhs, "nil") == 0) {
                    emit("%s %s = {};\n", ct, name);
                } else {
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("%s %s = %s;\n", ct, name, expr_c);
                }
            } else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit_indent(c_indent);
                emit("%s %s = %s;\n", simple_type_to_cpp(stype), name, expr_c);
            }
            (*line_idx)++;
            continue;
        }

        /* return */
        if (starts_with(trimmed, "return ")) {
            const char *ret_expr = skip_spaces(trimmed + 7);
            if (current_func && type_is_option(current_func->simple_ret) && strcmp(ret_expr, "nil") == 0) {
                emit_indent(c_indent);
                emit("return {};\n");
            } else {
                char expr_c[MAX_LINE];
                translate_expr(trimmed + 7, expr_c, sizeof(expr_c));
                emit_indent(c_indent);
                emit("return %s;\n", expr_c);
            }
            (*line_idx)++;
            continue;
        }
        if (strcmp(trimmed, "return") == 0) {
            emit_indent(c_indent);
            emit("return;\n");
            (*line_idx)++;
            continue;
        }

        /* break/continue/pass */
        if (strcmp(trimmed, "break") == 0) {
            emit_indent(c_indent); emit("break;\n"); (*line_idx)++; continue;
        }
        if (strcmp(trimmed, "continue") == 0) {
            emit_indent(c_indent); emit("continue;\n"); (*line_idx)++; continue;
        }
        if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0 ||
            strcmp(trimmed, "pass_do_nothing") == 0 || strcmp(trimmed, "pass_dn") == 0 ||
            strcmp(trimmed, "pass_todo") == 0) {
            emit_indent(c_indent); emit("/* pass */;\n"); (*line_idx)++; continue;
        }

        /* print */
        if (starts_with(trimmed, "print ")) {
            const char *arg = trimmed + 6;
            char arg_trimmed[MAX_LINE];
            strncpy(arg_trimmed, arg, sizeof(arg_trimmed)-1);
            arg_trimmed[sizeof(arg_trimmed)-1] = '\0';
            int atl = strlen(arg_trimmed);
            while (atl > 0 && arg_trimmed[atl-1] == ' ') arg_trimmed[--atl] = '\0';
            bool is_text_expr = expr_is_text(arg_trimmed);

            char expr_c[MAX_LINE];
            translate_expr(arg, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            if (is_text_expr) {
                emit("spl_println(%s);\n", expr_c);
            } else {
                emit("printf(\"%%lld\\n\", (long long)%s);\n", expr_c);
            }
            (*line_idx)++;
            continue;
        }

        /* Assignment: =, +=, -= */
        {
            int paren = 0;
            bool in_str = false;
            bool handled = false;
            for (int i = 0; trimmed[i]; i++) {
                if (trimmed[i] == '"' && !in_str) in_str = true;
                else if (trimmed[i] == '"' && in_str) in_str = false;
                if (in_str) continue;
                if (trimmed[i] == '(' || trimmed[i] == '[') paren++;
                if (trimmed[i] == ')' || trimmed[i] == ']') paren--;

                if (paren == 0 && !in_str) {
                    if (trimmed[i] == '+' && trimmed[i+1] == '=') {
                        char target[MAX_LINE], value[MAX_LINE];
                        strncpy(target, trimmed, i); target[i] = '\0';
                        strcpy(value, trimmed + i + 2);
                        char tc[MAX_LINE], vc[MAX_LINE];
                        translate_expr(trim(target), tc, sizeof(tc));
                        translate_expr(trim(value), vc, sizeof(vc));
                        emit_indent(c_indent);
                        emit("%s += %s;\n", tc, vc);
                        handled = true; break;
                    }
                    if (trimmed[i] == '-' && trimmed[i+1] == '=') {
                        char target[MAX_LINE], value[MAX_LINE];
                        strncpy(target, trimmed, i); target[i] = '\0';
                        strcpy(value, trimmed + i + 2);
                        char tc[MAX_LINE], vc[MAX_LINE];
                        translate_expr(trim(target), tc, sizeof(tc));
                        translate_expr(trim(value), vc, sizeof(vc));
                        emit_indent(c_indent);
                        emit("%s -= %s;\n", tc, vc);
                        handled = true; break;
                    }
                    if (trimmed[i] == '=' && trimmed[i+1] != '=' && i > 0 &&
                        trimmed[i-1] != '!' && trimmed[i-1] != '<' && trimmed[i-1] != '>' && trimmed[i-1] != '=') {
                        char target[MAX_LINE], value[MAX_LINE];
                        strncpy(target, trimmed, i); target[i] = '\0';
                        strcpy(value, trimmed + i + 1);
                        /* Array element assignment */
                        char *lhs2 = trim(target);
                        char *bracket2 = strchr(lhs2, '[');
                        if (bracket2) {
                            char aname[MAX_IDENT]; int ai2 = 0;
                            const char *lp2 = lhs2;
                            while (lp2 < bracket2) aname[ai2++] = *lp2++;
                            aname[ai2] = '\0';
                            if (var_is_array(trim(aname))) {
                                char ids[MAX_LINE] = ""; int ix = 0;
                                const char *bp2 = bracket2 + 1;
                                while (*bp2 && *bp2 != ']') ids[ix++] = *bp2++;
                                ids[ix] = '\0';
                                char ac[MAX_LINE], ic[MAX_LINE], vc[MAX_LINE];
                                translate_expr(trim(aname), ac, sizeof(ac));
                                translate_expr(trim(ids), ic, sizeof(ic));
                                translate_expr(trim(value), vc, sizeof(vc));
                                emit_indent(c_indent);
                                if (var_is_struct_array(trim(aname)))
                                    emit("%s[%s] = %s;\n", ac, ic, vc);
                                else if (var_is_nested_array(trim(aname)))
                                    emit("spl_array_set(%s, %s, spl_array_val(%s));\n", ac, ic, vc);
                                else if (var_is_text_array(trim(aname)))
                                    emit("spl_array_set(%s, %s, spl_str(%s));\n", ac, ic, vc);
                                else
                                    emit("spl_array_set(%s, %s, spl_int(%s));\n", ac, ic, vc);
                                handled = true; break;
                            }
                        }
                        /* Option nil assignment: x = nil where x is Option */
                        char *lhs_trimmed = trim(target);
                        if ((var_is_option(lhs_trimmed) || dot_expr_is_option(lhs_trimmed)) && strcmp(trim(value), "nil") == 0) {
                            char tc[MAX_LINE];
                            translate_expr(lhs_trimmed, tc, sizeof(tc));
                            emit_indent(c_indent);
                            emit("%s = {};\n", tc);
                            handled = true; break;
                        }
                        /* Struct array reset: pool = [] → pool.clear() */
                        if (var_is_struct_array(trim(target)) && strcmp(trim(value), "[]") == 0) {
                            char tc[MAX_LINE];
                            translate_expr(trim(target), tc, sizeof(tc));
                            emit_indent(c_indent);
                            emit("%s.clear();\n", tc);
                            handled = true; break;
                        }
                        /* General assignment */
                        char tc[MAX_LINE], vc[MAX_LINE];
                        translate_expr(trim(target), tc, sizeof(tc));
                        translate_expr(trim(value), vc, sizeof(vc));
                        emit_indent(c_indent);
                        emit("%s = %s;\n", tc, vc);
                        handled = true; break;
                    }
                }
            }
            if (handled) { (*line_idx)++; continue; }
        }

        /* Expression statement */
        {
            const char *expr_src = trimmed;
            int next_line_idx = *line_idx + 1;
            char merged_expr[MAX_ASM_TEXT];

            /* Handle multiline call/constructor expressions that were not pre-joined. */
            if (strchr(trimmed, '(') && !strchr(trimmed, ')')) {
                int depth = 0;
                bool in_str = false;
                for (const char *c = trimmed; *c; c++) {
                    if (*c == '"' && !in_str) { in_str = true; continue; }
                    if (*c == '"' && in_str) { in_str = false; continue; }
                    if (*c == '\\' && in_str) { if (*(c + 1)) c++; continue; }
                    if (in_str) continue;
                    if (*c == '(' || *c == '[') depth++;
                    else if (*c == ')' || *c == ']') depth--;
                }

                if (depth > 0) {
                    strncpy(merged_expr, trimmed, sizeof(merged_expr) - 1);
                    merged_expr[sizeof(merged_expr) - 1] = '\0';

                    int j = *line_idx + 1;
                    while (j < num_lines && depth > 0) {
                        const char *nl_raw = source_lines[j];
                        const char *nl = trim(nl_raw);
                        int nind = indent_level(nl_raw);
                        if (nl[0] == '\0' || nl[0] == '#') { j++; continue; }
                        if (nind <= base_indent) break;

                        int ml = strlen(merged_expr);
                        if (ml < (int)sizeof(merged_expr) - 2) {
                            merged_expr[ml] = ' ';
                            merged_expr[ml + 1] = '\0';
                            strncat(merged_expr, nl, sizeof(merged_expr) - strlen(merged_expr) - 1);
                        }

                        in_str = false;
                        for (const char *c = nl; *c; c++) {
                            if (*c == '"' && !in_str) { in_str = true; continue; }
                            if (*c == '"' && in_str) { in_str = false; continue; }
                            if (*c == '\\' && in_str) { if (*(c + 1)) c++; continue; }
                            if (in_str) continue;
                            if (*c == '(' || *c == '[') depth++;
                            else if (*c == ')' || *c == ']') depth--;
                        }
                        j++;
                    }

                    if (depth == 0) {
                        expr_src = merged_expr;
                        next_line_idx = j;
                    }
                }
            }

            char expr_c[MAX_LINE];
            translate_expr(expr_src, expr_c, sizeof(expr_c));

            /* Check if this is an implicit return (last expression in function body) */
            bool is_implicit_return = false;
            if (current_func && strcmp(current_func->ret_type, "void") != 0) {
                /* Only add implicit return at function body level (c_indent==1), not inside loops/if */
                if (c_indent == 1) {
                    /* Peek ahead, skipping blank lines and comments, to find next real code */
                    int next_idx = *line_idx + 1;
                    while (next_idx < num_lines) {
                        const char *nl = trim(source_lines[next_idx]);
                        if (nl[0] != '\0' && nl[0] != '#') break;
                        next_idx++;
                    }
                    if (next_idx >= num_lines) {
                        is_implicit_return = true;
                    } else {
                        int next_ind = indent_level(source_lines[next_idx]);
                        if (next_ind <= base_indent) {
                            is_implicit_return = true;
                        }
                    }
                }
                /* Don't add return for void function calls */
                if (is_implicit_return) {
                    char call_name[MAX_IDENT] = "";
                    int cni = 0;
                    const char *ec = expr_c;
                    while (*ec && *ec != '(' && *ec != ' ' && cni < MAX_IDENT - 1)
                        call_name[cni++] = *ec++;
                    call_name[cni] = '\0';
                    FuncInfo *called = find_func(call_name);
                    if (called && strcmp(called->ret_type, "void") == 0) {
                        is_implicit_return = false;
                    }
                    /* Also check common runtime void functions */
                    if (is_implicit_return && (
                        strncmp(expr_c, "spl_array_push(", 15) == 0 ||
                        strncmp(expr_c, "spl_array_set(", 14) == 0 ||
                        strncmp(expr_c, "spl_dict_set(", 13) == 0 ||
                        strncmp(expr_c, "spl_println(", 12) == 0 ||
                        strncmp(expr_c, "spl_print(", 10) == 0 ||
                        strncmp(expr_c, "spl_free(", 9) == 0)) {
                        is_implicit_return = false;
                    }
                }
            }

            emit_indent(c_indent);
            if (is_implicit_return) {
                emit("return %s;\n", expr_c);
            } else {
                emit("%s;\n", expr_c);
            }
            *line_idx = next_line_idx;
        }
    }
}

/* Single-statement translation (no line tracking) */
static void translate_statement(const char *trimmed, int c_indent) {
    if (starts_with(trimmed, "val ")) {
        const char *p = trimmed + 4;
        char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
        parse_var_decl(&p, name, stype);
        add_var(name, stype);
        if (stype[0] == '[' && *p == '[') {
            emit_indent(c_indent);
            emit("%s %s = spl_array_new();\n", simple_type_to_cpp(stype), name);
            emit_array_literal_pushes(name, p, c_indent);
        } else if (type_is_option(stype)) {
            const char *ct = simple_type_to_cpp(stype);
            const char *rhs = skip_spaces(p);
            emit_indent(c_indent);
            if (*rhs == '\0' || strcmp(rhs, "nil") == 0)
                emit("const %s %s = {};\n", ct, name);
            else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit("const %s %s = %s;\n", ct, name, expr_c);
            }
        } else {
            char expr_c[MAX_LINE];
            translate_expr(p, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            const char *ct = simple_type_to_cpp(stype);
            if (starts_with(ct, "const "))
                emit("%s %s = %s;\n", ct, name, expr_c);
            else
                emit("const %s %s = %s;\n", ct, name, expr_c);
        }
        return;
    }

    if (starts_with(trimmed, "var ")) {
        const char *p = trimmed + 4;
        char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
        parse_var_decl(&p, name, stype);
        add_var(name, stype);
        if (stype[0] == '[') {
            emit_indent(c_indent);
            emit("%s %s = spl_array_new();\n", simple_type_to_cpp(stype), name);
            if (*p == '[') emit_array_literal_pushes(name, p, c_indent);
        } else if (type_is_option(stype)) {
            const char *ct = simple_type_to_cpp(stype);
            const char *rhs = skip_spaces(p);
            emit_indent(c_indent);
            if (*rhs == '\0' || strcmp(rhs, "nil") == 0)
                emit("%s %s = {};\n", ct, name);
            else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit("%s %s = %s;\n", ct, name, expr_c);
            }
        } else {
            char expr_c[MAX_LINE];
            translate_expr(p, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            emit("%s %s = %s;\n", simple_type_to_cpp(stype), name, expr_c);
        }
        return;
    }

    if (starts_with(trimmed, "asm {") || strcmp(trimmed, "asm{") == 0) {
        char asm_text[MAX_ASM_TEXT];
        asm_text[0] = '\0';
        const char *open = strchr(trimmed, '{');
        const char *close = open ? strrchr(open + 1, '}') : nullptr;
        if (open && close && close > open) {
            char inside[MAX_LINE];
            int ilen = (int)(close - open - 1);
            if (ilen >= (int)sizeof(inside)) ilen = (int)sizeof(inside) - 1;
            if (ilen < 0) ilen = 0;
            strncpy(inside, open + 1, ilen);
            inside[ilen] = '\0';
            char line_text[MAX_LINE];
            normalize_asm_line(inside, line_text, sizeof(line_text));
            asm_append_line(asm_text, sizeof(asm_text), line_text);
        }
        emit_asm_stmt(asm_text, c_indent);
        return;
    }

    if (starts_with(trimmed, "asm ")) {
        const char *payload = skip_spaces(trimmed + 3);
        char asm_text[MAX_ASM_TEXT];
        normalize_asm_line(payload, asm_text, sizeof(asm_text));
        emit_asm_stmt(asm_text, c_indent);
        return;
    }

    if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0 ||
        strcmp(trimmed, "pass_do_nothing") == 0 || strcmp(trimmed, "pass_dn") == 0 ||
        strcmp(trimmed, "pass_todo") == 0) {
        emit_indent(c_indent); emit("/* pass */;\n"); return;
    }

    if (starts_with(trimmed, "print ")) {
        const char *arg = trimmed + 6;
        char arg_trimmed[MAX_LINE];
        strncpy(arg_trimmed, arg, sizeof(arg_trimmed)-1);
        arg_trimmed[sizeof(arg_trimmed)-1] = '\0';
        int atl = strlen(arg_trimmed);
        while (atl > 0 && arg_trimmed[atl-1] == ' ') arg_trimmed[--atl] = '\0';
        bool is_text_expr = expr_is_text(arg_trimmed);
        char expr_c[MAX_LINE];
        translate_expr(arg, expr_c, sizeof(expr_c));
        emit_indent(c_indent);
        if (is_text_expr) emit("spl_println(%s);\n", expr_c);
        else emit("printf(\"%%lld\\n\", (long long)%s);\n", expr_c);
        return;
    }

    /* Assignment */
    {
        int paren = 0; bool in_str = false;
        for (int i = 0; trimmed[i]; i++) {
            if (trimmed[i] == '"' && !in_str) in_str = true;
            else if (trimmed[i] == '"' && in_str) in_str = false;
            if (in_str) continue;
            if (trimmed[i] == '(' || trimmed[i] == '[') paren++;
            if (trimmed[i] == ')' || trimmed[i] == ']') paren--;
            if (paren == 0 && !in_str) {
                if (trimmed[i] == '+' && trimmed[i+1] == '=') {
                    char t[MAX_LINE], v[MAX_LINE]; strncpy(t, trimmed, i); t[i]='\0';
                    strcpy(v, trimmed+i+2);
                    char tc[MAX_LINE], vc[MAX_LINE];
                    translate_expr(trim(t), tc, sizeof(tc)); translate_expr(trim(v), vc, sizeof(vc));
                    emit_indent(c_indent); emit("%s += %s;\n", tc, vc); return;
                }
                if (trimmed[i] == '-' && trimmed[i+1] == '=') {
                    char t[MAX_LINE], v[MAX_LINE]; strncpy(t, trimmed, i); t[i]='\0';
                    strcpy(v, trimmed+i+2);
                    char tc[MAX_LINE], vc[MAX_LINE];
                    translate_expr(trim(t), tc, sizeof(tc)); translate_expr(trim(v), vc, sizeof(vc));
                    emit_indent(c_indent); emit("%s -= %s;\n", tc, vc); return;
                }
                if (trimmed[i] == '=' && trimmed[i+1] != '=' && i > 0 &&
                    trimmed[i-1] != '!' && trimmed[i-1] != '<' && trimmed[i-1] != '>' && trimmed[i-1] != '=') {
                    char t[MAX_LINE], v[MAX_LINE]; strncpy(t, trimmed, i); t[i]='\0';
                    strcpy(v, trimmed+i+1);
                    char *lhs = trim(t);
                    char *bracket = strchr(lhs, '[');
                    if (bracket) {
                        char arr_name[MAX_IDENT]; int ani = 0;
                        const char *lp = lhs;
                        while (lp < bracket) arr_name[ani++] = *lp++;
                        arr_name[ani] = '\0';
                        if (var_is_array(trim(arr_name))) {
                            char idx_s[MAX_LINE] = ""; int idxi = 0;
                            const char *bp = bracket + 1;
                            while (*bp && *bp != ']') idx_s[idxi++] = *bp++;
                            idx_s[idxi] = '\0';
                            char arr_c[MAX_LINE], idx_c[MAX_LINE], vc[MAX_LINE];
                            translate_expr(trim(arr_name), arr_c, sizeof(arr_c));
                            translate_expr(trim(idx_s), idx_c, sizeof(idx_c));
                            translate_expr(trim(v), vc, sizeof(vc));
                            emit_indent(c_indent);
                            if (var_is_nested_array(trim(arr_name)))
                                emit("spl_array_set(%s, %s, spl_array_val(%s));\n", arr_c, idx_c, vc);
                            else if (var_is_text_array(trim(arr_name)))
                                emit("spl_array_set(%s, %s, spl_str(%s));\n", arr_c, idx_c, vc);
                            else
                                emit("spl_array_set(%s, %s, spl_int(%s));\n", arr_c, idx_c, vc);
                            return;
                        }
                    }
                    /* Option nil assignment */
                    char *lhs2 = trim(t);
                    if ((var_is_option(lhs2) || dot_expr_is_option(lhs2)) && strcmp(trim(v), "nil") == 0) {
                        char tc[MAX_LINE];
                        translate_expr(lhs2, tc, sizeof(tc));
                        emit_indent(c_indent); emit("%s = {};\n", tc); return;
                    }
                    char tc[MAX_LINE], vc[MAX_LINE];
                    translate_expr(trim(t), tc, sizeof(tc)); translate_expr(trim(v), vc, sizeof(vc));
                    emit_indent(c_indent); emit("%s = %s;\n", tc, vc); return;
                }
            }
        }
    }

    /* Expression statement */
    { char expr_c[MAX_LINE]; translate_expr(trimmed, expr_c, sizeof(expr_c));
      emit_indent(c_indent); emit("%s;\n", expr_c); }
}

/* ===== Top-Level Processing ===== */

/* Parse function signature and register in func table.
 * Returns true if a function was registered. */
static bool register_func_sig(const char *t, bool is_method, const char *owner, bool is_mutable) {
    FuncInfo *fi = &funcs[num_funcs];
    memset(fi, 0, sizeof(*fi));
    fi->is_mutable = is_mutable;

    const char *start = t;
    if (starts_with(t, "fn ")) start = t + 3;
    else if (starts_with(t, "extern fn ")) { start = t + 10; fi->is_extern = true; }
    else if (starts_with(t, "me ")) { start = t + 3; fi->is_mutable = true; }
    else if (starts_with(t, "static fn ")) { start = t + 10; fi->is_static_method = true; }
    else return false;

    const char *p = start;
    int ni = 0;

    char decl_name[MAX_IDENT] = "";
    parse_decl_name(p, decl_name, sizeof(decl_name));
    if (decl_name[0] == '\0') return false;

    /* If method, prepend owner struct name */
    if (is_method && owner[0]) {
        snprintf(fi->name, MAX_IDENT, "%s__", owner);
        ni = strlen(fi->name);
        strcpy(fi->owner_struct, owner);
    }

    for (int i = 0; decl_name[i] && ni < MAX_IDENT - 1; i++) {
        fi->name[ni++] = decl_name[i];
    }
    fi->name[ni] = '\0';

    while (*p && *p != '(') p++;

    /* Parse params */
    if (*p == '(') p++;
    fi->param_count = 0;
    while (*p && *p != ')') {
        p = skip_spaces(p);
        if (*p == ')') break;
        int pni = 0;
        while (*p && *p != ':' && *p != ',' && *p != ')')
            fi->param_names[fi->param_count][pni++] = *p++;
        fi->param_names[fi->param_count][pni] = '\0';
        while (pni > 0 && fi->param_names[fi->param_count][pni-1] == ' ')
            fi->param_names[fi->param_count][--pni] = '\0';
        /* sanitize at emit time instead */

        if (*p == ':') {
            p++; p = skip_spaces(p);
            int pti = 0;
            if (*p == '[') {
                fi->param_stypes[fi->param_count][pti++] = *p++;
                while (*p && *p != ']') fi->param_stypes[fi->param_count][pti++] = *p++;
                if (*p == ']') fi->param_stypes[fi->param_count][pti++] = *p++;
            } else {
                int angle_depth = 0;
                int paren_depth = 0;
                int bracket_depth = 0;
                while (*p) {
                    if (angle_depth == 0 && paren_depth == 0 && bracket_depth == 0 &&
                        (*p == ',' || *p == ')')) {
                        break;
                    }
                    if (*p == '<') angle_depth++;
                    else if (*p == '>' && angle_depth > 0) angle_depth--;
                    else if (*p == '(') paren_depth++;
                    else if (*p == ')' && paren_depth > 0) paren_depth--;
                    else if (*p == '[') bracket_depth++;
                    else if (*p == ']' && bracket_depth > 0) bracket_depth--;
                    fi->param_stypes[fi->param_count][pti++] = *p++;
                }
            }
            fi->param_stypes[fi->param_count][pti] = '\0';
            while (pti > 0 && fi->param_stypes[fi->param_count][pti-1] == ' ')
                fi->param_stypes[fi->param_count][--pti] = '\0';
            strcpy(fi->param_types[fi->param_count], simple_type_to_cpp(fi->param_stypes[fi->param_count]));
        } else {
            strcpy(fi->param_stypes[fi->param_count], "i64");
            strcpy(fi->param_types[fi->param_count], "int64_t");
        }
        fi->param_count++;
        if (*p == ',') p++;
    }

    /* Non-static methods already get an implicit self parameter in emitted C++; drop explicit self params. */
    if (is_method && !fi->is_static_method && fi->param_count > 0) {
        int write = 0;
        for (int read = 0; read < fi->param_count; read++) {
            if (strcmp(trim(fi->param_names[read]), "self") == 0) continue;
            if (write != read) {
                strcpy(fi->param_names[write], fi->param_names[read]);
                strcpy(fi->param_types[write], fi->param_types[read]);
                strcpy(fi->param_stypes[write], fi->param_stypes[read]);
            }
            write++;
        }
        fi->param_count = write;
    }

    /* Parse return type */
    if (*p == ')') p++;
    p = skip_spaces(p);
    if (starts_with(p, "->")) {
        p += 2; p = skip_spaces(p);
        int rti = 0;
        while (*p && *p != ':' && *p != '\0') fi->simple_ret[rti++] = *p++;
        fi->simple_ret[rti] = '\0';
        while (rti > 0 && fi->simple_ret[rti-1] == ' ')
            fi->simple_ret[--rti] = '\0';
        strcpy(fi->ret_type, simple_type_to_cpp(fi->simple_ret));
    } else {
        strcpy(fi->simple_ret, "void");
        strcpy(fi->ret_type, "void");
    }

    /* Skip spl_ extern functions -- they conflict with runtime.h */
    if (fi->is_extern && starts_with(fi->name, "spl_")) {
        return false;
    }

    /* Rename 'main' to avoid conflict with C++ main */
    if (strcmp(fi->name, "main") == 0) {
        has_main_func = true;
        fprintf(stderr, "[seed_cpp] DEBUG: Found main() function, setting has_main_func=true\n");
        strcpy(fi->name, "spl_main");
    }

    /* Skip if a function with the same name is already registered */
    for (int k = 0; k < num_funcs; k++) {
        if (strcmp(funcs[k].name, fi->name) == 0) {
            if (strcmp(fi->name, "spl_main") == 0) {
                fprintf(stderr, "[seed_cpp] DEBUG: Skipping duplicate spl_main (already registered at func #%d)\n", k);
            }
            return false;
        }
    }

    num_funcs++;
    if (strcmp(fi->name, "spl_main") == 0) {
        fprintf(stderr, "[seed_cpp] DEBUG: Registered spl_main as function #%d\n", num_funcs - 1);
    }
    return true;
}

static void process_file(void) {
    /* ===== First pass: collect struct/enum/function signatures ===== */
    fprintf(stderr, "[seed_cpp] DEBUG: Starting first pass, num_lines=%d\n", num_lines);
    for (int i = 0; i < num_lines; i++) {
        const char *line = source_lines[i];
        int ind = indent_level(line);
        const char *t = trim(line);
        if (i >= 123 && i <= 140) {
            fprintf(stderr, "[seed_cpp] DEBUG: Line %d (0-idx), ind=%d, in_docstring=%s, raw: %.60s | trimmed: %.60s\n",
                    i, ind, (strstr(line, "\"\"\"") ? "YES" : "no"), line, t);
        }
        if (t[0] == '\0' || t[0] == '#') continue;

        /* Top-level struct or class */
        if (ind == 0 && (starts_with(t, "struct ") || starts_with(t, "class ")) && ends_with(t, ":")) {
            fprintf(stderr, "[seed_cpp] DEBUG: Found struct/class at line %d: %.50s\n", i, t);
            bool is_class = starts_with(t, "class ");
            char sname[MAX_IDENT] = "";
            const char *p = t + (is_class ? 6 : 7);
            parse_decl_name(p, sname, sizeof(sname));

            StructInfo *si = &structs[num_structs];
            memset(si, 0, sizeof(*si));
            strcpy(si->name, sname);

            /* Parse fields (and methods for class) under indented lines */
            int j = i + 1;
            while (j < num_lines) {
                const char *fl = source_lines[j];
                const char *ft = trim(fl);
                if (ft[0] == '\0') { j++; continue; } /* Skip blank lines before indent check */
                if (indent_level(fl) <= 0) break;
                if (ft[0] == '#') { j++; continue; }

                /* Skip inline methods (fn/me/static fn) in struct/class — they're handled as impl methods */
                if (starts_with(ft, "fn ") || starts_with(ft, "me ") || starts_with(ft, "static fn ")) {
                    /* Skip method body */
                    int method_ind = indent_level(fl);
                    j++;
                    while (j < num_lines) {
                        const char *bl = source_lines[j];
                        const char *bt = trim(bl);
                        if (bt[0] == '\0' || bt[0] == '#') { j++; continue; }
                        if (indent_level(bl) <= method_ind) break;
                        j++;
                    }
                    continue;
                }

                /* Skip enum data variant lines: Name(field: type) */
                {
                    bool is_data_variant = false;
                    for (const char *chk = ft; *chk && *chk != ':'; chk++) {
                        if (*chk == '(') { is_data_variant = true; break; }
                    }
                    if (is_data_variant) { j++; continue; }
                }

                /* Field: name: type */
                char fname[MAX_IDENT] = "", ftype[MAX_IDENT] = "";
                int fni = 0;
                const char *fp = ft;
                while (*fp && *fp != ':') fname[fni++] = *fp++;
                fname[fni] = '\0';
                /* Trim fname */
                fni = strlen(fname);
                while (fni > 0 && fname[fni-1] == ' ') fname[--fni] = '\0';

                if (*fp == ':') {
                    fp++; fp = skip_spaces(fp);
                    int fti = 0;
                    while (*fp && *fp != '\0' && *fp != '#' && *fp != '=')
                        ftype[fti++] = *fp++;
                    ftype[fti] = '\0';
                    fti = strlen(ftype);
                    while (fti > 0 && ftype[fti-1] == ' ') ftype[--fti] = '\0';
                    /* Option type '?' is preserved for proper Option struct generation */
                }

                if (fname[0] && ftype[0] && si->field_count < MAX_FIELDS) {
                    /* Validate field name: must be a valid C identifier (no quotes, spaces, etc.) */
                    bool valid_field = true;
                    for (int ci = 0; fname[ci]; ci++) {
                        if (!isalnum((unsigned char)fname[ci]) && fname[ci] != '_') {
                            valid_field = false;
                            break;
                        }
                    }
                    if (valid_field) {
                        /* sanitize at emit time instead */
                        strcpy(si->field_names[si->field_count], fname);
                        strcpy(si->field_stypes[si->field_count], ftype);
                        si->field_count++;
                    }
                }
                j++;
            }
            num_structs++;
            fprintf(stderr, "[seed_cpp] DEBUG: Registered struct '%s' at line %d\n", sname, i);

            /* For class/struct: also register inline methods (as if impl ClassName:) */
            {
                j = i + 1;
                while (j < num_lines) {
                    const char *ml = source_lines[j];
                    const char *mt = trim(ml);
                    if (mt[0] == '\0' || mt[0] == '#') { j++; continue; }
                    if (indent_level(ml) <= 0) break;

                    if (starts_with(mt, "fn ") || starts_with(mt, "me ") || starts_with(mt, "static fn ")) {
                        bool is_mut = starts_with(mt, "me ");
                        register_func_sig(mt, true, si->name, is_mut);
                    }
                    j++;
                }
                /* Update outer loop counter to skip past struct body */
                fprintf(stderr, "[seed_cpp] DEBUG: Struct '%s' ended at line %d, updating i from %d to %d\n",
                        sname, j, i, j - 1);
                i = j - 1;  /* -1 because for loop will do i++ */
            }
        }

        /* Top-level enum */
        if (ind == 0 && starts_with(t, "enum ") && ends_with(t, ":")) {
            char ename[MAX_IDENT] = "";
            const char *p = t + 5;
            parse_decl_name(p, ename, sizeof(ename));

            /* Skip duplicate enum definitions (same enum in multiple files) */
            if (find_enum(ename)) {
                /* Already registered — skip variants */
                int j = i + 1;
                while (j < num_lines) {
                    const char *vl = source_lines[j];
                    const char *vt = trim(vl);
                    if (vt[0] == '\0') { j++; continue; }
                    if (indent_level(vl) <= 0) break;
                    j++;
                }
            } else {
                EnumInfo *ei = &enums[num_enums];
                memset(ei, 0, sizeof(*ei));
                strcpy(ei->name, ename);

                /* Parse variants (indented lines) */
                int j = i + 1;
                int enum_ind = indent_level(line);
                while (j < num_lines) {
                    const char *vl = source_lines[j];
                    const char *vt = trim(vl);
                    if (vt[0] == '\0') { j++; continue; } /* Skip blank lines before indent check */
                    int vind = indent_level(vl);
                    if (vind <= enum_ind) break;
                    if (vt[0] == '#') { j++; continue; }

                    /* Enum methods may follow variants. Stop collecting at first method. */
                    if (starts_with(vt, "fn ") || starts_with(vt, "me ") || starts_with(vt, "static fn ")) {
                        break;
                    }
                    if (vt[0] == '@') { j++; continue; }

                    /* Simple variant (no data): just the name */
                    char vname[MAX_IDENT] = "";
                    int vni = 0;
                    const char *vp = vt;
                    while (*vp && *vp != '(' && *vp != ' ' && *vp != '#' && *vp != ':' && *vp != ',')
                        vname[vni++] = *vp++;
                    vname[vni] = '\0';
                    bool dup_variant = false;
                    for (int vk = 0; vk < ei->variant_count; vk++) {
                        if (strcmp(ei->variants[vk], vname) == 0) {
                            dup_variant = true;
                            break;
                        }
                    }
                    /* Skip variant names starting with '"' (leaked docstrings) */
                    if (vname[0] && vname[0] != '"' && !dup_variant && ei->variant_count < MAX_VARIANTS) {
                        strcpy(ei->variants[ei->variant_count], vname);
                        ei->variant_count++;
                    }
                    j++;
                }
                num_enums++;
            }
        }

        /* Top-level function */
        if (ind == 0 && starts_with(t, "fn ") && ends_with(t, ":")) {
            // Debug: log which file we're in when processing functions
            static int last_logged_line = -1;
            if (i > last_logged_line + 1000 || strstr(t, "main") != NULL) {
                fprintf(stderr, "[seed_cpp] DEBUG: Processing fn at line %d: %.60s\n", i, t);
                last_logged_line = i;
            }
            register_func_sig(t, false, "", false);
        } else if (starts_with(t, "fn main() ")) {
            // Debug: Why isn't main() being detected?
            fprintf(stderr, "[seed_cpp] DEBUG: Found 'fn main()' but not registering! Line %d, ind=%d, ends_with_colon=%d, text: %.80s\n",
                    i, ind, ends_with(t, ":"), t);
        }

        /* Top-level extern fn */
        if (ind == 0 && starts_with(t, "extern fn ")) {
            register_func_sig(t, false, "", false);
        }

        /* Top-level val/var with explicit type annotation:
         * pre-register types (especially Option<T>) before type emission phases. */
        if (ind == 0 && (starts_with(t, "val ") || starts_with(t, "var "))) {
            const char *gp = t + 4;
            while (*gp && *gp != ':' && *gp != '=' && *gp != '#') gp++;
            if (*gp == ':') {
                gp++;
                gp = skip_spaces(gp);
                char gstype[MAX_IDENT] = "";
                int gti = 0;
                int angle_depth = 0;
                int bracket_depth = 0;
                int paren_depth = 0;
                while (*gp && gti < MAX_IDENT - 1) {
                    char c = *gp;
                    if (c == '<') angle_depth++;
                    else if (c == '>' && angle_depth > 0) angle_depth--;
                    else if (c == '[') bracket_depth++;
                    else if (c == ']' && bracket_depth > 0) bracket_depth--;
                    else if (c == '(') paren_depth++;
                    else if (c == ')' && paren_depth > 0) paren_depth--;

                    if (angle_depth == 0 && bracket_depth == 0 && paren_depth == 0 &&
                        (c == '=' || c == '#')) {
                        break;
                    }
                    gstype[gti++] = c;
                    gp++;
                }
                gstype[gti] = '\0';
                while (gti > 0 && gstype[gti - 1] == ' ') gstype[--gti] = '\0';
                if (gstype[0]) {
                    (void)simple_type_to_cpp(gstype);
                }
            }
        }

        /* trait block: skip entirely (traits have no runtime representation) */
        if (ind == 0 && starts_with(t, "trait ") && ends_with(t, ":")) {
            int j = i + 1;
            while (j < num_lines) {
                const char *tl = source_lines[j];
                const char *tt = trim(tl);
                if (tt[0] == '\0' || tt[0] == '#') { j++; continue; }
                if (indent_level(tl) <= 0) break;
                j++;
            }
            i = j - 1;
            continue;
        }

        /* impl block: collect methods */
        if (ind == 0 && starts_with(t, "impl ") && ends_with(t, ":")) {
            char impl_name[MAX_IDENT] = "";
            const char *p = t + 5;
            parse_impl_owner_name(p, impl_name, sizeof(impl_name));

            int j = i + 1;
            while (j < num_lines) {
                const char *ml = source_lines[j];
                const char *mt = trim(ml);
                /* Skip blank lines / comments inside impl block */
                if (mt[0] == '\0' || mt[0] == '#') { j++; continue; }
                /* Stop at next top-level declaration */
                if (indent_level(ml) <= 0) break;

                if (starts_with(mt, "fn ") || starts_with(mt, "me ") || starts_with(mt, "static fn ")) {
                    bool is_mut = starts_with(mt, "me ");
                    register_func_sig(mt, true, impl_name, is_mut);
                }
                j++;
            }
        }
    }

    fprintf(stderr, "[seed] Registered: %d structs, %d enums, %d funcs, %d lines\n",
            num_structs, num_enums, num_funcs, num_lines);

    /* Re-resolve function/parameter C++ types after full first pass.
     * This allows return/param types that appear before their struct declarations
     * to map correctly once all structs/enums are known. */
    for (int i = 0; i < num_funcs; i++) {
        const char *resolved_ret = simple_type_to_cpp(funcs[i].simple_ret);
        snprintf(funcs[i].ret_type, sizeof(funcs[i].ret_type), "%s", resolved_ret);
        for (int p = 0; p < funcs[i].param_count; p++) {
            const char *resolved_param = simple_type_to_cpp(funcs[i].param_stypes[p]);
            snprintf(funcs[i].param_types[p], sizeof(funcs[i].param_types[p]), "%s", resolved_param);
        }
    }

    /* ===== Emit C++ header ===== */
    emit("#include <cstdio>\n");
    emit("#include <cstdlib>\n");
    emit("#include <cstring>\n");
    emit("#include <cstdint>\n");
    emit("#include <cstdarg>\n");
    emit("#include <vector>\n\n");
    /* Include runtime.h BEFORE #defines to avoid breaking C headers */
    emit("extern \"C\" {\n");
    emit("#include \"runtime.h\"\n");
    emit("}\n\n");
    /* Rename C++ keywords used as Simple identifiers */
    emit("#define asm asm_spl\n");
    emit("#define assert spl_assert\n");
    emit("#define template template_spl\n");
    emit("#define register register_spl\n");
    emit("#define default default_spl\n");
    emit("#define class class_spl\n");
    emit("#define new new_spl\n");
    emit("#define delete delete_spl\n");
    emit("#define union union_spl\n");
    emit("#define namespace namespace_spl\n");
    emit("#define operator operator_spl\n");
    emit("#define private private_spl\n");
    emit("#define protected protected_spl\n");
    emit("#define public public_spl\n");
    emit("#define virtual virtual_spl\n");
    emit("#define throw throw_spl\n");
    emit("#define catch catch_spl\n");
    emit("#define try try_spl\n");
    emit("#define typename typename_spl\n\n");
    emit("static int has_field = 0;\n");
    emit("static int64_t _ = 0;\n\n");

    /* Type aliases for unmapped Simple types — only emit if not already a struct */
    const char *fallback_types[][2] = {
        {"Effect", "int64_t"}, {"Result", "int64_t"}, {"Option", "int64_t"},
        {"CompileResult", "int64_t"}, {"CoercionResult", "int64_t"},
        {"Symbol", "int64_t"}, {"Fn", "int64_t"}, {"Iterator", "int64_t"},
        {"Any", "int64_t"}, {"Trait", "int64_t"},
        {nullptr, nullptr}
    };
    for (int ti = 0; fallback_types[ti][0]; ti++) {
        /* Only skip typedef if there's a real struct; enums are emitted as int constants
           so they still need the typedef for the type name to resolve */
        if (!find_struct(fallback_types[ti][0])) {
            emit("typedef %s %s;\n", fallback_types[ti][1], fallback_types[ti][0]);
        }
    }
    emit("typedef int64_t fn;\n");
    emit("typedef int64_t type;\n");
    /* Not adding 'module' as typedef — it's used as a variable name too */
    emit("typedef const char* text;\n");
    emit("typedef int64_t i64;\n");
    emit("typedef int32_t i32;\n");
    emit("typedef double f64;\n");
    emit("typedef float f32;\n");
    emit("typedef uint8_t u8;\n");
    emit("typedef uint32_t u32;\n");
    /* Function pointer typedefs */
    emit("typedef int64_t (*FnPtr_i64)();\n");
    emit("typedef const char* (*FnPtr_text)();\n");
    emit("typedef void (*FnPtr_void)();\n");
    emit("typedef bool (*FnPtr_bool)();\n");
    emit("typedef int64_t (*FnPtr_Any)();\n");
    emit("typedef int64_t (*FnPtr_ConstValue)();\n");
    emit("typedef int64_t (*FnPtr_BlockValue)();\n");
    emit("typedef SplArray* (*FnPtr_array)();\n");
    emit("typedef int64_t (*FnPtr_HoverInfo)();\n");
    /* Note: Option_fn_ptr and Option_Symbol are now auto-generated by Option<T> registry */
    emit("typedef uint64_t u64;\n\n");
    /* NL is provided by shim_nl.spl as a Simple-level val, emitted as a global */
    emit("static const char* _NL = \"\\n\";\n");
    emit("static const char* NL = \"\\n\";\n\n");

    /* Some interface-only types may appear only as pointer receivers in reduced file sets. */
    emit("struct TypeMapper;\n\n");

    /* Stub declarations for functions NOT in runtime.h */
    emit("inline void log_debug(...) {}\n");
    emit("inline void log_trace(...) {}\n");
    emit("inline void log_info(...) {}\n");
    emit("inline void log_warn(...) {}\n");
    emit("inline void log_error(...) {}\n");
    emit("inline void spl_assert(bool cond) {}\n");
    emit("inline SplArray* data_push(SplArray* arr, int64_t val) { spl_array_push(arr, spl_int(val)); return arr; }\n");
    emit("inline int64_t spl_char_at(const char* s, int64_t i) { return (uint8_t)s[i]; }\n");
    emit("inline int64_t spl_abs(int64_t x) { return x < 0 ? -x : x; }\n");
    emit("inline int64_t spl_min(int64_t a, int64_t b) { return a < b ? a : b; }\n");
    emit("inline int64_t spl_max(int64_t a, int64_t b) { return a > b ? a : b; }\n");
    emit("inline const char* spl_str_lower(const char* s) { return s; }\n");
    emit("inline const char* spl_str_upper(const char* s) { return s; }\n");
    emit("inline const char* spl_substr(const char* s, int64_t start, int64_t len) { return \"\"; }\n\n");

    /* ===== Emit enum definitions ===== */
    for (int i = 0; i < num_enums; i++) {
        EnumInfo *ei = &enums[i];
        char enum_id[MAX_IDENT];
        sanitize_cpp_ident_fragment(ei->name, enum_id, sizeof(enum_id));
        emit("/* enum %s */\n", ei->name);
        if (!find_struct(ei->name)) {
            emit("typedef int64_t %s;\n", enum_id);
        }
        for (int j = 0; j < ei->variant_count; j++) {
            char var_id[MAX_IDENT];
            sanitize_cpp_ident_fragment(ei->variants[j], var_id, sizeof(var_id));
            emit("static const int64_t %s_%s = %d;\n", enum_id, var_id, j);
        }
        emit("\n");
    }

    /* ===== Trigger Option type registration from ALL sources ===== */
    /* From function signatures */
    for (int i = 0; i < num_funcs; i++) {
        if (type_is_option(funcs[i].simple_ret))
            simple_type_to_cpp(funcs[i].simple_ret);
        for (int j = 0; j < funcs[i].param_count; j++) {
            if (type_is_option(funcs[i].param_stypes[j]))
                simple_type_to_cpp(funcs[i].param_stypes[j]);
        }
    }
    /* From struct fields */
    for (int i = 0; i < num_structs; i++) {
        for (int j = 0; j < structs[i].field_count; j++) {
            if (type_is_option(structs[i].field_stypes[j]))
                simple_type_to_cpp(structs[i].field_stypes[j]);
        }
    }

    /* ===== Emit Option + struct definitions in correct order ===== */

    /* Phase 0: Pre-scan all struct fields to register Option/Result types */
    /* This ensures forward declarations include ALL Option types before any struct uses them */
    for (int i = 0; i < num_structs; i++) {
        StructInfo *si = &structs[i];
        for (int j = 0; j < si->field_count; j++) {
            /* Calling simple_type_to_cpp() registers the type if it's Option<T> or Result<T,E> */
            (void)simple_type_to_cpp(si->field_stypes[j]);
        }
    }

    /* Phase A: Forward-declare all structs and Option structs (deduplicated) */
    {
        static const char *emitted_structs[MAX_STRUCTS];
        int num_emitted = 0;
        for (int i = 0; i < num_structs; i++) {
            bool dup = false;
            for (int k = 0; k < num_emitted; k++) {
                if (strcmp(emitted_structs[k], structs[i].name) == 0) { dup = true; break; }
            }
            if (!dup) {
                emit("struct %s;\n", structs[i].name);
                emitted_structs[num_emitted++] = structs[i].name;
            }
        }
    }
    for (int i = 0; i < num_option_types; i++) {
        emit("struct %s;\n", option_types[i].option_name);
    }
    for (int i = 0; i < num_result_types; i++) {
        emit("struct %s;\n", result_types[i].result_name);
    }
    if (num_structs > 0 || num_option_types > 0 || num_result_types > 0) emit("\n");

    /* Phase B: Emit primitive Option structs (base type is NOT a user struct or Result) */
    for (int i = 0; i < num_option_types; i++) {
        OptionTypeInfo *oi = &option_types[i];
        fprintf(stderr, "Phase B: Option<%s> (cpp_base=%s)\n", oi->simple_base, oi->cpp_base);
        if (find_struct(oi->simple_base)) {
            fprintf(stderr, "  -> Skipping (struct-based)\n");
            continue; /* skip struct-based Options */
        }
        /* Skip Result-based Options (they need int64_t) */
        bool is_result_based = strncmp(oi->simple_base, "Result<", 7) == 0;
        if (is_result_based) {
            fprintf(stderr, "  -> Skipping Result-based Option (starts with Result<)\n");
            continue;
        }
        /* Skip tuple-based Options (they need int64_t) */
        bool is_tuple_based = oi->simple_base[0] == '(';
        if (is_tuple_based) {
            fprintf(stderr, "  -> Skipping tuple-based Option (starts with '(')\n");
            continue;
        }
        emit("/* Option<%s> */\n", oi->simple_base);
        emit("struct %s {\n", oi->option_name);
        emit("    bool has_value;\n");
        emit("    %s value;\n", oi->cpp_base);
        emit("    %s() : has_value(false), value{} {}\n", oi->option_name);
        emit("    %s(%s v) : has_value(true), value(v) {}\n", oi->option_name, oi->cpp_base);
        emit("    %s(SplValue) : has_value(false), value{} {}\n", oi->option_name);
        emit("};\n\n");
    }

    /* Phase D: Emit struct-based, Result-based, and tuple-based Option structs */
    /* Moved BEFORE Phase C so that structs can use these Option types */
    /* Use int64_t for struct/Result/tuple values (pointers) to avoid circular dependencies */
    for (int i = 0; i < num_option_types; i++) {
        OptionTypeInfo *oi = &option_types[i];
        fprintf(stderr, "Phase D: Option<%s>\n", oi->simple_base);
        bool is_struct_based = find_struct(oi->simple_base) != NULL;
        bool is_result_based = strncmp(oi->simple_base, "Result<", 7) == 0;
        bool is_tuple_based = oi->simple_base[0] == '(';

        if (is_result_based) {
            fprintf(stderr, "  -> Result-based! Will use int64_t\n");
        }
        if (is_struct_based) {
            fprintf(stderr, "  -> Struct-based, using int64_t\n");
        }
        if (is_tuple_based) {
            fprintf(stderr, "  -> Tuple-based, using int64_t\n");
        }

        if (!is_struct_based && !is_result_based && !is_tuple_based) {
            fprintf(stderr, "  -> Primitive, skipping\n");
            continue; /* skip primitive Options */
        }
        emit("/* Option<%s> */\n", oi->simple_base);
        emit("struct %s {\n", oi->option_name);
        emit("    bool has_value;\n");
        emit("    int64_t value;  /* struct/Result/tuple pointer as int64_t */\n");
        emit("    %s() : has_value(false), value(0) {}\n", oi->option_name);
        emit("    %s(int64_t v) : has_value(true), value(v) {}\n", oi->option_name);
        emit("    %s(SplValue) : has_value(false), value(0) {}\n", oi->option_name);
        emit("};\n\n");
    }

    /* Phase C: Emit user struct definitions (deduplicated — keep first definition) */
    {
        static const char *emitted_structs[MAX_STRUCTS];
        int num_emitted = 0;
        for (int i = 0; i < num_structs; i++) {
            StructInfo *si = &structs[i];
            bool dup = false;
            for (int k = 0; k < num_emitted; k++) {
                if (strcmp(emitted_structs[k], si->name) == 0) { dup = true; break; }
            }
            if (!dup) {
                emit("struct %s {\n", si->name);
                for (int j = 0; j < si->field_count; j++) {
                    const char *ctype = simple_type_to_cpp(si->field_stypes[j]);
                    /* Sanitize field name at emit time to avoid C++ keyword conflicts */
                    char safe_fname[MAX_IDENT];
                    strcpy(safe_fname, si->field_names[j]);
                    sanitize_cpp_name(safe_fname);
                    /* Use pointer for struct-typed fields to avoid incomplete type errors */
                    if (find_struct(si->field_stypes[j])) {
                        emit("    %s* %s;\n", ctype, safe_fname);
                    } else {
                        emit("    %s %s;\n", ctype, safe_fname);
                    }
                }
                emit("};\n\n");
                emitted_structs[num_emitted++] = si->name;
            }
        }
    }

    /* Phase E: Emit Result<T, E> structs */
    for (int i = 0; i < num_result_types; i++) {
        ResultTypeInfo *ri = &result_types[i];
        emit("/* Result<%s, %s> */\n", ri->ok_type, ri->err_type);
        emit("struct %s {\n", ri->result_name);
        emit("    bool is_ok;\n");
        emit("    %s ok_value;\n", ri->cpp_ok);
        emit("    %s err_value;\n", ri->cpp_err);
        emit("    %s() : is_ok(false), ok_value{}, err_value{} {}\n", ri->result_name);
        emit("    static %s Ok(%s v) { %s r; r.is_ok = true; r.ok_value = v; return r; }\n",
             ri->result_name, ri->cpp_ok, ri->result_name);
        emit("    static %s Err(%s e) { %s r; r.is_ok = false; r.err_value = e; return r; }\n",
             ri->result_name, ri->cpp_err, ri->result_name);
        emit("};\n\n");
    }

    /* ===== Emit extern declarations ===== */
    for (int i = 0; i < num_funcs; i++) {
        if (funcs[i].is_extern) {
            /* Skip rt_ externs - they're already declared in runtime.h */
            if (starts_with(funcs[i].name, "rt_")) continue;
            emit("extern \"C\" %s %s(", funcs[i].ret_type, funcs[i].name);
            for (int j = 0; j < funcs[i].param_count; j++) {
                if (j > 0) emit(", ");
                /* Sanitize param names at emit time */
                char safe_pname[MAX_IDENT];
                strcpy(safe_pname, funcs[i].param_names[j]);
                sanitize_cpp_name(safe_pname);
                emit("%s %s", funcs[i].param_types[j], safe_pname);
            }
            emit(");\n");
        }
    }
    emit("\n");

    /* ===== Emit forward declarations for all non-extern functions ===== */
    for (int i = 0; i < num_funcs; i++) {
        if (!funcs[i].is_extern) {
            /* Skip functions with garbled parameter names */
            bool garbled_params = false;
            for (int j = 0; j < funcs[i].param_count; j++) {
                const char *pn = funcs[i].param_names[j];
                if (pn[0] == '\0' || pn[0] == ']' || pn[0] == ')' || pn[0] == '[' ||
                    pn[0] == '{' || pn[0] == '}' || pn[0] == '(' || pn[0] == '.') {
                    garbled_params = true;
                    break;
                }
            }
            if (garbled_params) continue;
            emit("%s %s(", funcs[i].ret_type, funcs[i].name);
            /* Non-static methods get a 'self' parameter first */
            bool has_self = (funcs[i].owner_struct[0] != '\0' && !funcs[i].is_static_method);
            if (has_self) {
                if (funcs[i].is_mutable)
                    emit("%s* self", funcs[i].owner_struct);
                else
                    emit("const %s* self", funcs[i].owner_struct);
                if (funcs[i].param_count > 0) emit(", ");
            }
            for (int j = 0; j < funcs[i].param_count; j++) {
                if (j > 0) emit(", ");
                char safe_pname[MAX_IDENT];
                strcpy(safe_pname, funcs[i].param_names[j]);
                sanitize_cpp_name(safe_pname);
                emit("%s %s", funcs[i].param_types[j], safe_pname);
            }
            emit(");\n");
        }
    }
    emit("\n");

    /* ===== Emit module-level variables (deduplicated) ===== */
    static char emitted_vars[MAX_FUNCS][MAX_IDENT];
    int num_emitted_vars = 0;
    for (int i = 0; i < num_lines; i++) {
        const char *line = source_lines[i];
        int ind = indent_level(line);
        const char *t = trim(line);

        if (ind != 0) continue;
        if (t[0] == '\0' || t[0] == '#') continue;

        if (starts_with(t, "val ") || starts_with(t, "var ")) {
            const char *p = t + 4;
            char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
            parse_var_decl(&p, name, stype);
            add_var(name, stype);

            /* Skip if already emitted */
            bool var_dup = false;
            for (int k = 0; k < num_emitted_vars; k++) {
                if (strcmp(emitted_vars[k], name) == 0) { var_dup = true; break; }
            }
            if (var_dup) continue;
            if (num_emitted_vars < MAX_FUNCS)
                strcpy(emitted_vars[num_emitted_vars++], name);

            /* Check if variable name conflicts with a function name */
            if (find_func(name)) {
                /* Rename variable to avoid clash with function of same name */
                int nl = strlen(name);
                memmove(name + 2, name, nl + 1);
                name[0] = 'v'; name[1] = '_';
            }
            sanitize_cpp_name(name);

            const char *ctype = simple_type_to_cpp(stype);

            if (stype[0] == '[') {
                emit("static %s %s;\n", ctype, name);
            } else if (type_is_option(stype)) {
                emit("static %s %s = {};\n", ctype, name);
            } else if (type_is_struct(stype)) {
                emit("static %s %s = {};\n", ctype, name);
            } else if (is_constant_expr(p)) {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit("static %s %s = %s;\n", ctype, name, expr_c);
            } else {
                if (strcmp(ctype, "const char*") == 0)
                    emit("static %s %s = \"\";\n", ctype, name);
                else if (strcmp(ctype, "bool") == 0)
                    emit("static %s %s = false;\n", ctype, name);
                else
                    emit("static %s %s = 0;\n", ctype, name);
            }
        }
    }
    emit("\n");

    /* Save global var count so function scopes can reset to it */
    int global_vars_count = num_vars;

    /* ===== Emit function definitions ===== */
    for (int i = 0; i < num_lines; i++) {
        const char *line = source_lines[i];
        int ind = indent_level(line);
        const char *t = trim(line);

        if (ind != 0) continue;

        /* Top-level fn */
        if (starts_with(t, "fn ") && ends_with(t, ":")) {
            char fname[MAX_IDENT] = "";
            const char *p = t + 3;
            parse_decl_name(p, fname, sizeof(fname));

            /* If function is "main", look for "spl_main" (renamed in first pass) */
            const char *lookup_name = (strcmp(fname, "main") == 0) ? "spl_main" : fname;
            FuncInfo *fi = find_func(lookup_name);
            if (!fi) { continue; }
            if (fi->emitted) { continue; }  /* Skip duplicate definitions */
            fi->emitted = true;

            /* Check for garbled parameter names in definitions too */
            bool garbled_def = false;
            for (int j = 0; j < fi->param_count; j++) {
                const char *pn = fi->param_names[j];
                if (pn[0] == '\0' || pn[0] == ']' || pn[0] == ')' || pn[0] == '[' ||
                    pn[0] == '{' || pn[0] == '}' || pn[0] == '(' || pn[0] == '.') {
                    garbled_def = true;
                    break;
                }
            }
            if (garbled_def) { continue; }

            for (int j = 0; j < fi->param_count; j++) {
                add_var(fi->param_names[j], fi->param_stypes[j]);
            }

            emit("%s %s(", fi->ret_type, fi->name);
            for (int j = 0; j < fi->param_count; j++) {
                if (j > 0) emit(", ");
                char safe_pname[MAX_IDENT];
                strcpy(safe_pname, fi->param_names[j]);
                sanitize_cpp_name(safe_pname);
                emit("%s %s", fi->param_types[j], safe_pname);
            }
            emit(") {\n");

            /* Implicit return for non-void functions */
            if (strcmp(fi->ret_type, "void") != 0) {
                int body_end = i + 1;
                while (body_end < num_lines) {
                    const char *bl = source_lines[body_end];
                    int bi = indent_level(bl);
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { body_end++; continue; }
                    if (bi <= 0) break;
                    body_end++;
                }
                int last_body = -1;
                for (int k = body_end - 1; k > i; k--) {
                    const char *bl = source_lines[k];
                    int bi = indent_level(bl);
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') continue;
                    if (bi == 1) { last_body = k; break; }
                }
                if (last_body > 0) {
                    const char *lt = trim(source_lines[last_body]);
                    bool needs_return = true;
                    if (starts_with(lt, "return ") || strcmp(lt, "return") == 0) needs_return = false;
                    if (starts_with(lt, "if ") || starts_with(lt, "while ") ||
                        starts_with(lt, "for ") || starts_with(lt, "match ")) needs_return = false;
                    if (starts_with(lt, "elif ") || strcmp(lt, "else:") == 0) needs_return = false;
                    if (starts_with(lt, "val ") || starts_with(lt, "var ")) needs_return = false;
                    if (starts_with(lt, "break") || starts_with(lt, "continue")) needs_return = false;
                    if (starts_with(lt, "print ")) needs_return = false;
                    if (strcmp(lt, ")") == 0 || strcmp(lt, "]") == 0 || strcmp(lt, "}") == 0) needs_return = false;
                    if (needs_return) {
                        for (int ci = 0; lt[ci]; ci++) {
                            if (lt[ci] == '(' || lt[ci] == '[' || lt[ci] == '"') break;
                            if (lt[ci] == '=' && lt[ci+1] != '=' && ci > 0 &&
                                lt[ci-1] != '!' && lt[ci-1] != '<' && lt[ci-1] != '>' && lt[ci-1] != '=') {
                                needs_return = false;
                                break;
                            }
                        }
                    }
                    if (needs_return) {
                        char new_line[MAX_LINE];
                        int spaces = 0;
                        const char *orig = source_lines[last_body];
                        while (orig[spaces] == ' ') spaces++;
                        snprintf(new_line, MAX_LINE, "%.*sreturn %s", spaces, orig, lt);
                        free(source_lines[last_body]);
                        source_lines[last_body] = strdup(new_line);
                    }
                }
            }

            int body_idx = i + 1;
            current_func = fi;
            num_vars = global_vars_count;  /* Reset var table for each function scope */
            /* Register function params as variables */
            for (int pk = 0; pk < fi->param_count; pk++) {
                add_var(fi->param_names[pk], fi->param_stypes[pk]);
            }
            int saved_pos = out_pos;
            translate_block(&body_idx, 0, 1);
            if (output_has_problems(saved_pos)) {
                fprintf(stderr, "[seed_cpp] DEBUG: Function %s body has problems, emitting stub\n", fi->name);
                out_pos = saved_pos;
                output[out_pos] = '\0';
                emit_stub_return(fi->ret_type);
            } else if (strcmp(fi->name, "spl_main") == 0) {
                fprintf(stderr, "[seed_cpp] DEBUG: Function spl_main body OK, %d bytes generated\n", out_pos - saved_pos);
            }
            current_func = nullptr;
            i = body_idx - 1;
            emit("}\n\n");
        }

        /* trait block: skip in emission */
        if (starts_with(t, "trait ") && ends_with(t, ":")) {
            int j = i + 1;
            while (j < num_lines) {
                const char *tl = source_lines[j];
                const char *tt = trim(tl);
                if (tt[0] == '\0' || tt[0] == '#') { j++; continue; }
                if (indent_level(tl) <= 0) break;
                j++;
            }
            i = j - 1;
            continue;
        }

        /* impl/class/struct block: emit methods */
        if ((starts_with(t, "impl ") || starts_with(t, "class ") || starts_with(t, "struct ")) && ends_with(t, ":")) {
            bool is_class_block = starts_with(t, "class ");
            bool is_struct_block = starts_with(t, "struct ");
            char impl_name[MAX_IDENT] = "";
            const char *p = t + (is_class_block ? 6 : is_struct_block ? 7 : 5);
            parse_impl_owner_name(p, impl_name, sizeof(impl_name));

            int j = i + 1;
            while (j < num_lines) {
                const char *ml = source_lines[j];
                const char *mt = trim(ml);
                if (mt[0] == '\0' || mt[0] == '#') { j++; continue; }
                if (indent_level(ml) <= 0) break;

                bool is_fn = starts_with(mt, "fn ");
                bool is_me = starts_with(mt, "me ");
                bool is_static = starts_with(mt, "static fn ");

                if (is_fn || is_me || is_static) {
                    /* Find method name */
                    const char *mstart = mt;
                    if (is_fn) mstart = mt + 3;
                    else if (is_me) mstart = mt + 3;
                    else if (is_static) mstart = mt + 10;

                    char mname[MAX_IDENT] = "";
                    parse_decl_name(mstart, mname, sizeof(mname));

                    /* Find registered function */
                    char mangled[MAX_IDENT * 2];
                    snprintf(mangled, sizeof(mangled), "%s__%s", impl_name, mname);
                    FuncInfo *fi = find_func(mangled);
                    if (!fi) { j++; continue; }
                    if (fi->emitted) { j++; continue; }  /* Skip duplicate method definitions */
                    fi->emitted = true;

                    /* Check for garbled parameter names in method definitions */
                    bool garbled_mdef = false;
                    for (int k = 0; k < fi->param_count; k++) {
                        const char *pn = fi->param_names[k];
                        if (pn[0] == '\0' || pn[0] == ']' || pn[0] == ')' || pn[0] == '[' ||
                            pn[0] == '{' || pn[0] == '}' || pn[0] == '(' || pn[0] == '.') {
                            garbled_mdef = true;
                            break;
                        }
                    }
                    if (garbled_mdef) { j++; continue; }

                    /* Register params */
                    for (int k = 0; k < fi->param_count; k++) {
                        add_var(fi->param_names[k], fi->param_stypes[k]);
                    }

                    /* Emit method definition */
                    emit("%s %s(", fi->ret_type, fi->name);
                    if (!is_static) {
                        if (fi->is_mutable)
                            emit("%s* self", impl_name);
                        else
                            emit("const %s* self", impl_name);
                        if (fi->param_count > 0) emit(", ");
                    }
                    for (int k = 0; k < fi->param_count; k++) {
                        if (k > 0) emit(", ");
                        char safe_pname[MAX_IDENT];
                        strcpy(safe_pname, fi->param_names[k]);
                        sanitize_cpp_name(safe_pname);
                        emit("%s %s", fi->param_types[k], safe_pname);
                    }
                    emit(") {\n");

                    /* Find method body end */
                    int method_ind = indent_level(ml);
                    int body_start = j + 1;

                    /* Implicit return for non-void methods */
                    if (strcmp(fi->ret_type, "void") != 0) {
                        int body_end = body_start;
                        while (body_end < num_lines) {
                            const char *bl = source_lines[body_end];
                            const char *bt = trim(bl);
                            if (bt[0] == '\0' || bt[0] == '#') { body_end++; continue; }
                            if (indent_level(bl) <= method_ind) break;
                            body_end++;
                        }
                        int last_body = -1;
                        for (int k = body_end - 1; k >= body_start; k--) {
                            const char *bl = source_lines[k];
                            const char *bt = trim(bl);
                            if (bt[0] == '\0' || bt[0] == '#') continue;
                            if (indent_level(bl) == method_ind + 1) { last_body = k; break; }
                        }
                        if (last_body >= 0) {
                            const char *lt = trim(source_lines[last_body]);
                            bool needs_return = true;
                            if (starts_with(lt, "return ") || strcmp(lt, "return") == 0) needs_return = false;
                            if (starts_with(lt, "if ") || starts_with(lt, "while ") ||
                                starts_with(lt, "for ") || starts_with(lt, "match ")) needs_return = false;
                            if (starts_with(lt, "val ") || starts_with(lt, "var ")) needs_return = false;
                            if (starts_with(lt, "break") || starts_with(lt, "continue")) needs_return = false;
                            if (starts_with(lt, "print ")) needs_return = false;
                            if (strcmp(lt, ")") == 0 || strcmp(lt, "]") == 0 || strcmp(lt, "}") == 0) needs_return = false;
                            if (needs_return) {
                                for (int ci = 0; lt[ci]; ci++) {
                                    if (lt[ci] == '(' || lt[ci] == '[' || lt[ci] == '"') break;
                                    if (lt[ci] == '=' && lt[ci+1] != '=' && ci > 0 &&
                                        lt[ci-1] != '!' && lt[ci-1] != '<' && lt[ci-1] != '>' && lt[ci-1] != '=') {
                                        needs_return = false; break;
                                    }
                                }
                            }
                            if (needs_return) {
                                char new_line[MAX_LINE];
                                int spaces = 0;
                                const char *orig = source_lines[last_body];
                                while (orig[spaces] == ' ') spaces++;
                                snprintf(new_line, MAX_LINE, "%.*sreturn %s", spaces, orig, lt);
                                free(source_lines[last_body]);
                                source_lines[last_body] = strdup(new_line);
                            }
                        }
                    }

                    /* Translate method body */
                    current_func = fi;
                    num_vars = global_vars_count;  /* Reset var table for each method scope */
                    /* Register method params as variables */
                    for (int pk = 0; pk < fi->param_count; pk++) {
                        add_var(fi->param_names[pk], fi->param_stypes[pk]);
                    }
                    strncpy(current_impl_struct, impl_name, MAX_IDENT - 1);
                    current_impl_struct[MAX_IDENT - 1] = '\0';
                    int saved_pos2 = out_pos;
                    translate_block(&body_start, method_ind, 1);
                    if (output_has_problems(saved_pos2)) {
                        out_pos = saved_pos2;
                        output[out_pos] = '\0';
                        emit_stub_return(fi->ret_type);
                    }
                    current_impl_struct[0] = '\0';
                    current_func = nullptr;
                    j = body_start;
                    emit("}\n\n");
                } else {
                    j++;
                }
            }
            i = j - 1;
        }
    }

    /* Count emitted functions */
    {
        int emitted = 0;
        for (int i = 0; i < num_funcs; i++) {
            if (funcs[i].emitted) emitted++;
        }
        fprintf(stderr, "[seed] Emitted: %d / %d functions\n", emitted, num_funcs);
    }

    /* ===== Emit __module_init ===== */
    emit("static void __module_init(void) {\n");
    num_vars = global_vars_count;  /* Reset to globals only */
    {
        int init_idx = 0;
        while (init_idx < num_lines) {
            const char *line = source_lines[init_idx];
            int ind = indent_level(line);
            const char *t = trim(line);

            if (ind != 0) { init_idx++; continue; }
            if (t[0] == '\0' || t[0] == '#') { init_idx++; continue; }

            /* Skip declarations + their bodies */
            if (starts_with(t, "fn ") || starts_with(t, "extern fn ")) {
                init_idx++;
                while (init_idx < num_lines) {
                    const char *bl = source_lines[init_idx];
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                    if (indent_level(bl) == 0) break;
                    init_idx++;
                }
                continue;
            }
            if ((starts_with(t, "struct ") || starts_with(t, "enum ") || starts_with(t, "impl ") || starts_with(t, "class ")) &&
                ends_with(t, ":")) {
                init_idx++;
                while (init_idx < num_lines) {
                    const char *sl = source_lines[init_idx];
                    const char *st = trim(sl);
                    /* Skip blank/comment lines inside block */
                    if (st[0] == '\0' || st[0] == '#') { init_idx++; continue; }
                    if (indent_level(sl) == 0) break;
                    init_idx++;
                }
                continue;
            }
            if (starts_with(t, "use ") || starts_with(t, "export ") || starts_with(t, "import ") ||
                starts_with(t, "from ") ||
                starts_with(t, "pub mod ") || starts_with(t, "mod ") || starts_with(t, "pub ")) {
                init_idx++; continue;
            }
            /* Skip type aliases, traits, abstract classes */
            if (starts_with(t, "type ") || starts_with(t, "abstract ") || starts_with(t, "@")) {
                init_idx++;
                /* Skip any indented body */
                while (init_idx < num_lines) {
                    const char *bl = source_lines[init_idx];
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                    if (indent_level(bl) == 0) break;
                    init_idx++;
                }
                continue;
            }
            /* Skip trait blocks */
            if (starts_with(t, "trait ") && ends_with(t, ":")) {
                init_idx++;
                while (init_idx < num_lines) {
                    const char *bl = source_lines[init_idx];
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                    if (indent_level(bl) == 0) break;
                    init_idx++;
                }
                continue;
            }
            /* Skip me (mutating) method declarations at module level */
            if (starts_with(t, "me ") || starts_with(t, "static fn ")) {
                init_idx++;
                while (init_idx < num_lines) {
                    const char *bl = source_lines[init_idx];
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                    if (indent_level(bl) == 0) break;
                    init_idx++;
                }
                continue;
            }

            /* val/var: init arrays and non-constants */
            if (starts_with(t, "val ") || starts_with(t, "var ")) {
                const char *p = t + 4;
                char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
                parse_var_decl(&p, name, stype);

                if (stype[0] == '[') {
                    if (type_is_struct_array(stype)) {
                        /* struct arrays use std::vector, already initialized */
                    } else {
                        emit("    %s = spl_array_new();\n", name);
                    }
                    if (*p == '[' && *(p+1) != ']') {
                        int arr_sp = out_pos;
                        emit_array_literal_pushes(name, p, 1);
                        /* Check for spl_int wrapping type names or struct-typed variables */
                        const char *arr_gen = output + arr_sp;
                        bool bad_arr = false;
                        const char *sc = arr_gen;
                        while (!bad_arr && (sc = strstr(sc, "spl_int(")) != NULL) {
                            sc += 8;
                            char arg[MAX_IDENT] = "";
                            int ai = 0;
                            while (*sc && *sc != ')' && ai < MAX_IDENT-1) arg[ai++] = *sc++;
                            arg[ai] = '\0';
                            /* Check if arg is a struct name or type alias */
                            if (find_struct(arg) || strcmp(arg, "text") == 0 ||
                                strcmp(arg, "i64") == 0 || strcmp(arg, "i32") == 0 ||
                                strcmp(arg, "f64") == 0 || strcmp(arg, "f32") == 0 ||
                                strcmp(arg, "u8") == 0 || strcmp(arg, "u32") == 0 ||
                                strcmp(arg, "u64") == 0) {
                                bad_arr = true;
                            }
                            /* Check if arg is a variable of struct type */
                            for (int vi = 0; !bad_arr && vi < num_vars; vi++) {
                                if (strcmp(vars[vi].name, arg) == 0 && find_struct(vars[vi].stype)) {
                                    bad_arr = true;
                                }
                            }
                        }
                        if (bad_arr) {
                            out_pos = arr_sp;
                            output[out_pos] = '\0';
                        }
                    }
                } else if (type_is_option(stype) && *p != '\0' && strcmp(skip_spaces(p), "nil") != 0) {
                    /* Option with non-nil init */
                    int sp = out_pos;
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("    %s = %s;\n", name, expr_c);
                    if (output_has_problems(sp) || strlen(expr_c) > 200) {
                        out_pos = sp; output[out_pos] = '\0';
                    }
                } else if (type_is_struct(stype) && *p != '\0') {
                    /* Struct with constructor init — skip garbled */
                    int sp = out_pos;
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("    %s = %s;\n", name, expr_c);
                    if (output_has_problems(sp) || strlen(expr_c) > 200) {
                        out_pos = sp; output[out_pos] = '\0';
                    }
                } else if (!is_constant_expr(p)) {
                    int sp = out_pos;
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("    %s = %s;\n", name, expr_c);
                    if (output_has_problems(sp) || strlen(expr_c) > 200) {
                        out_pos = sp; output[out_pos] = '\0';
                    }
                }
                init_idx++;
                continue;
            }

            if (strcmp(t, "asm:") == 0) {
                int asm_base_indent = ind;
                char asm_text[MAX_ASM_TEXT];
                asm_text[0] = '\0';
                init_idx++;
                while (init_idx < num_lines) {
                    const char *aline = source_lines[init_idx];
                    const char *atrim = trim(aline);
                    int aind = indent_level(aline);
                    if (atrim[0] == '\0' || atrim[0] == '#') { init_idx++; continue; }
                    if (aind <= asm_base_indent) break;
                    char line_text[MAX_LINE];
                    normalize_asm_line(atrim, line_text, sizeof(line_text));
                    asm_append_line(asm_text, sizeof(asm_text), line_text);
                    init_idx++;
                }
                emit_asm_stmt(asm_text, 1);
                continue;
            }

            if (starts_with(t, "asm {") || strcmp(t, "asm{") == 0) {
                char asm_text[MAX_ASM_TEXT];
                asm_text[0] = '\0';
                const char *open = strchr(t, '{');
                const char *close = open ? strrchr(open + 1, '}') : nullptr;
                if (open && close && close > open) {
                    char inside[MAX_LINE];
                    int ilen = (int)(close - open - 1);
                    if (ilen >= (int)sizeof(inside)) ilen = (int)sizeof(inside) - 1;
                    if (ilen < 0) ilen = 0;
                    strncpy(inside, open + 1, ilen);
                    inside[ilen] = '\0';
                    char line_text[MAX_LINE];
                    normalize_asm_line(inside, line_text, sizeof(line_text));
                    asm_append_line(asm_text, sizeof(asm_text), line_text);
                    init_idx++;
                } else {
                    init_idx++;
                    while (init_idx < num_lines) {
                        const char *aline = source_lines[init_idx];
                        const char *atrim = trim(aline);
                        if (atrim[0] == '\0' || atrim[0] == '#') { init_idx++; continue; }
                        if (strcmp(atrim, "}") == 0) { init_idx++; break; }
                        char line_text[MAX_LINE];
                        normalize_asm_line(atrim, line_text, sizeof(line_text));
                        asm_append_line(asm_text, sizeof(asm_text), line_text);
                        init_idx++;
                    }
                }
                emit_asm_stmt(asm_text, 1);
                continue;
            }

            if (starts_with(t, "asm ")) {
                const char *payload = skip_spaces(t + 3);
                char asm_text[MAX_ASM_TEXT];
                normalize_asm_line(payload, asm_text, sizeof(asm_text));
                emit_asm_stmt(asm_text, 1);
                init_idx++;
                continue;
            }

            /* Module-level control flow — handle inline (NOT translate_block with base=-1,
               because that would consume ALL remaining lines since indent is always >= 0) */
            if (starts_with(t, "if ") && ends_with(t, ":")) {
                int saved_if_pos = out_pos;
                char cond[MAX_LINE], cond_c[MAX_LINE];
                extract_condition(t, 3, cond, sizeof(cond));
                translate_expr(cond, cond_c, sizeof(cond_c));
                emit("    if (%s) {\n", cond_c);
                init_idx++;
                translate_block(&init_idx, 0, 2);
                emit("    }");
                /* Handle elif/else chains */
                while (init_idx < num_lines) {
                    const char *nl = source_lines[init_idx];
                    const char *nt = trim(nl);
                    if (nt[0] == '\0' || nt[0] == '#') { init_idx++; continue; }
                    if (indent_level(nl) != 0) break;
                    if (starts_with(nt, "elif ") && ends_with(nt, ":")) {
                        char econd[MAX_LINE], econd_c[MAX_LINE];
                        extract_condition(nt, 5, econd, sizeof(econd));
                        translate_expr(econd, econd_c, sizeof(econd_c));
                        emit(" else if (%s) {\n", econd_c);
                        init_idx++;
                        translate_block(&init_idx, 0, 2);
                        emit("    }");
                    } else if (strcmp(nt, "else:") == 0) {
                        emit(" else {\n");
                        init_idx++;
                        translate_block(&init_idx, 0, 2);
                        emit("    }");
                    } else {
                        break;
                    }
                }
                emit("\n");
                /* Rewind if garbled */
                if (output_has_problems(saved_if_pos)) {
                    out_pos = saved_if_pos;
                    output[out_pos] = '\0';
                }
                continue;
            }
            if (starts_with(t, "while ") && ends_with(t, ":")) {
                int saved_while_pos = out_pos;
                char cond[MAX_LINE], cond_c[MAX_LINE];
                extract_condition(t, 6, cond, sizeof(cond));
                translate_expr(cond, cond_c, sizeof(cond_c));
                emit("    while (%s) {\n", cond_c);
                init_idx++;
                translate_block(&init_idx, 0, 2);
                emit("    }\n");
                if (output_has_problems(saved_while_pos)) {
                    out_pos = saved_while_pos;
                    output[out_pos] = '\0';
                }
                continue;
            }
            if (starts_with(t, "for ") && ends_with(t, ":")) {
                int saved_for_pos = out_pos;
                /* Let translate_block handle the for-loop parsing */
                int save_idx = init_idx;
                translate_block(&init_idx, -1, 1);
                /* translate_block with base=-1 would consume everything,
                   so we manually stop after one block: check if init_idx
                   moved past the for body */
                /* Actually, re-do: handle for inline */
                /* Restore and handle manually */
                init_idx = save_idx;
                /* Emit the for loop — skip the header, body handled by translate_block */
                /* We need translate_block for the for-loop syntax parsing,
                   but limit it to one statement. Use base_indent=0 approach:
                   increment past the for line, then process body. */
                {
                    /* Parse for header: for VAR in EXPR: */
                    const char *p = t + 4;
                    char var_name[MAX_IDENT] = "";
                    int vi = 0;
                    while (*p && *p != ' ') var_name[vi++] = *p++;
                    var_name[vi] = '\0';
                    p = skip_spaces(p);
                    if (starts_with(p, "in ")) p += 3;
                    char iter_expr[MAX_LINE];
                    int ie = 0;
                    while (*p && *p != ':') iter_expr[ie++] = *p++;
                    iter_expr[ie] = '\0';
                    while (ie > 0 && iter_expr[ie-1] == ' ') iter_expr[--ie] = '\0';

                    add_var(var_name, "i64");

                    /* Check for range() pattern */
                    char *tr_iter = trim(iter_expr);
                    if (starts_with(tr_iter, "range(")) {
                        char *args = tr_iter + 6;
                        char *end_paren = strrchr(args, ')');
                        if (end_paren) *end_paren = '\0';
                        char *comma = strchr(args, ',');
                        if (comma) {
                            *comma = '\0';
                            char start_c[MAX_LINE], end_c[MAX_LINE];
                            translate_expr(trim(args), start_c, sizeof(start_c));
                            translate_expr(trim(comma + 1), end_c, sizeof(end_c));
                            emit("    for (int64_t %s = %s; %s < %s; %s++) {\n",
                                 var_name, start_c, var_name, end_c, var_name);
                        } else {
                            char end_c[MAX_LINE];
                            translate_expr(trim(args), end_c, sizeof(end_c));
                            emit("    for (int64_t %s = 0; %s < %s; %s++) {\n",
                                 var_name, var_name, end_c, var_name);
                        }
                    } else {
                        const char *iter_stype = find_var_type(tr_iter);
                        if (iter_stype && strcmp(iter_stype, "text") == 0) {
                            char iter_c[MAX_LINE];
                            translate_expr(tr_iter, iter_c, sizeof(iter_c));
                            add_var(var_name, "text");
                            emit("    for (int64_t __%s_i = 0; __%s_i < spl_str_len(%s); __%s_i++) {\n",
                                 var_name, var_name, iter_c, var_name);
                            emit("        const char* %s = spl_str_index_char(%s, __%s_i);\n",
                                 var_name, iter_c, var_name);
                        } else {
                        /* Array iteration */
                        char arr_c[MAX_LINE];
                        translate_expr(tr_iter, arr_c, sizeof(arr_c));
                        emit("    for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                             var_name, var_name, arr_c, var_name);
                        emit("        int64_t %s = spl_array_get(%s, __%s_i).as_int;\n",
                             var_name, arr_c, var_name);
                        }
                    }
                    init_idx++;
                    translate_block(&init_idx, 0, 2);
                    emit("    }\n");
                }
                /* Rewind if garbled */
                if (output_has_problems(saved_for_pos)) {
                    out_pos = saved_for_pos;
                    output[out_pos] = '\0';
                }
                continue;
            }
            if (starts_with(t, "match ") && ends_with(t, ":")) {
                /* Match blocks are rare at module level; use simple skip for now */
                init_idx++;
                while (init_idx < num_lines) {
                    const char *bl = source_lines[init_idx];
                    const char *bt = trim(bl);
                    if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                    if (indent_level(bl) == 0) break;
                    init_idx++;
                }
                continue;
            }

            /* Whitelist approach: only translate known-safe patterns in module init.
               Everything else gets skipped to avoid garbled output. */
            {
                bool is_safe = false;
                /* Function calls: identifier followed by ( — must be very simple */
                if (strchr(t, '(') && !strchr(t, ':') && !strstr(t, "case ") &&
                    !strstr(t, "match ") && !strchr(t, '{') && !strchr(t, '"') &&
                    !strchr(t, '.') && strlen(t) < 100) {
                    is_safe = true;
                }
                /* Simple assignment: identifier = simple_expr */
                if (!is_safe) {
                    const char *eq = strchr(t, '=');
                    if (eq && eq > t && *(eq-1) != '!' && *(eq-1) != '<' && *(eq-1) != '>' &&
                        *(eq+1) != '=' && !strchr(t, ':') && !strstr(t, "case ") &&
                        !strchr(eq + 1, '{') && !strchr(eq + 1, '>') && !strchr(eq + 1, '"') &&
                        !strchr(eq + 1, '.') && strlen(t) < 100) {
                        is_safe = true;
                    }
                }
                /* print statements */
                if (starts_with(t, "print ") || starts_with(t, "spl_print")) is_safe = true;
                /* return statements */
                if (starts_with(t, "return ") || strcmp(t, "return") == 0) is_safe = true;
                /* break/continue */
                if (strcmp(t, "break") == 0 || strcmp(t, "continue") == 0) is_safe = true;

                if (!is_safe) {
                    init_idx++;
                    /* Skip any indented body that follows */
                    while (init_idx < num_lines) {
                        const char *bl = source_lines[init_idx];
                        const char *bt = trim(bl);
                        if (bt[0] == '\0' || bt[0] == '#') { init_idx++; continue; }
                        if (indent_level(bl) == 0) break;
                        init_idx++;
                    }
                    continue;
                }
            }
            {
                int saved_init_pos = out_pos;
                translate_statement(t, 1);
                /* Check if the translated output looks broken or too long */
                int gen_len = out_pos - saved_init_pos;
                bool bad_output = false;
                if (output_has_problems(saved_init_pos)) bad_output = true;
                if (gen_len > 300) bad_output = true;
                /* Check for garbled identifiers - type names used as values */
                const char *gen_start = output + saved_init_pos;
                if (strstr(gen_start, "spl_int(i64)") || strstr(gen_start, "spl_int(i32)") ||
                    strstr(gen_start, "= i64>") || strstr(gen_start, "= Bitfield>") ||
                    strstr(gen_start, "spl_int(spl_array") ||
                    strstr(gen_start, "spl_int(local_") ||
                    strstr(gen_start, "spl_int(MirLocal") ||
                    strstr(gen_start, "= spl_array_new();\n")) bad_output = true;
                if (bad_output) {
                    out_pos = saved_init_pos;
                    output[out_pos] = '\0';
                }
            }
            init_idx++;
        }
    }
    emit("}\n\n");

    /* ===== Emit main ===== */
    emit("int main(int argc, char** argv) {\n");
    emit("    spl_init_args(argc, argv);\n");
    emit("    __module_init();\n");
    if (has_main_func) {
        /* Call Simple main function and return its result */
        emit("    return (int)spl_main();\n");
    } else {
        /* No main function - just return 0 */
        emit("    return 0;\n");
    }
    emit("}\n");
}

/* ===== Main ===== */
int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s input1.spl [input2.spl ...] [> output.cpp]\n", argv[0]);
        return 1;
    }

    /* Allocate output buffer dynamically to avoid .bss section overflow */
    output = (char*)calloc(MAX_OUTPUT, 1);
    if (!output) {
        fprintf(stderr, "ERROR: Failed to allocate %zu MB output buffer\n", MAX_OUTPUT / (1024*1024));
        return 1;
    }

    fprintf(stderr, "[seed_cpp] Processing %d files...\n", argc - 1);

    /* Load all input files into a single source buffer */
    for (int i = 1; i < argc; i++) {
        fprintf(stderr, "[seed_cpp] Loading file %d/%d: %s\n", i, argc - 1, argv[i]);
        load_file(argv[i]);
        fprintf(stderr, "[seed_cpp] Loaded %s (%d total lines)\n", argv[i], num_lines);
        /* Add empty line between files for safety */
        if (i < argc - 1 && num_lines < MAX_LINES) {
            source_lines[num_lines++] = strdup("");
        }
    }

    fprintf(stderr, "[seed_cpp] All files loaded (%d lines total). Starting processing...\n", num_lines);
    fprintf(stderr, "[seed_cpp] Applying conditional compilation (@when/@cfg/@elif/@else/@end)...\n");
    preprocess_conditional_directives();
    process_file();
    fprintf(stderr, "[seed_cpp] Processing complete. Output size: %d bytes\n", out_pos);

    fwrite(output, 1, out_pos, stdout);
    free(output);

    return 0;
}
