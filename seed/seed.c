/*
 * Bootstrap Seed Compiler — Simple → C Transpiler
 *
 * A minimal, self-contained C program that reads Simple source code and
 * emits equivalent C code. This is the "seed" that bootstraps the full
 * Simple compiler written in Simple.
 *
 * Bootstrap chain:
 *   1. cc (clang/gcc) compiles seed.c → seed binary
 *   2. seed compiles bootstrap compiler (Simple) → C code
 *   3. cc compiles C code + runtime.c → native bootstrap compiler
 *   4. Native bootstrap compiler compiles itself → fixed point
 *
 * Supported Simple subset:
 *   - val/var declarations with type annotations
 *   - fn declarations with typed params and return type
 *   - extern fn declarations
 *   - struct definitions
 *   - if/elif/else
 *   - for i in 0..N (range loops)
 *   - while loops
 *   - match/case (integer patterns)
 *   - return, break, continue
 *   - Expressions: arithmetic, comparison, logical, calls, indexing,
 *     field access, method calls (.push, .len, .pop, .contains)
 *   - Array literals, string literals, string interpolation
 *   - Comments (#)
 *   - use/export (skipped)
 *
 * Usage:
 *   cc -o build/seed seed/seed.c
 *   build/seed input.spl > output.c
 *   cc -o output output.c seed/runtime.c
 */

#if !defined(_WIN32)
#define _POSIX_C_SOURCE 200809L
#endif
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>

#ifdef _WIN32
#define strdup _strdup
#endif

/* ===== Configuration ===== */
#define MAX_LINE 4096
#define MAX_LINES 100000
#define MAX_IDENT 256
#define MAX_OUTPUT (1024 * 1024 * 16)  /* 16 MB output buffer */
#define MAX_INDENT_STACK 256
#define MAX_PARAMS 64
#define MAX_FUNCS 4096

/* ===== Output Buffer ===== */
static char output[MAX_OUTPUT];
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

static void load_file(const char *path) {
    FILE *f = fopen(path, "r");
    if (!f) { fprintf(stderr, "Cannot open: %s\n", path); exit(1); }
    char buf[MAX_LINE];
    while (fgets(buf, sizeof(buf), f) && num_lines < MAX_LINES) {
        /* Remove trailing newline */
        int len = strlen(buf);
        if (len > 0 && buf[len-1] == '\n') buf[len-1] = '\0';
        source_lines[num_lines++] = strdup(buf);
    }
    fclose(f);
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

/* trim uses multiple static buffers to avoid reentrant conflicts */
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

/* ===== Type Conversion ===== */
static const char *simple_type_to_c(const char *stype) {
    if (strcmp(stype, "i64") == 0) return "int64_t";
    if (strcmp(stype, "f64") == 0) return "double";
    if (strcmp(stype, "text") == 0) return "const char*";
    if (strcmp(stype, "bool") == 0) return "int";
    if (strcmp(stype, "void") == 0) return "void";
    if (strcmp(stype, "[i64]") == 0) return "SplArray*";
    if (strcmp(stype, "[f64]") == 0) return "SplArray*";
    if (strcmp(stype, "[text]") == 0) return "SplArray*";
    if (strcmp(stype, "[bool]") == 0) return "SplArray*";
    if (strcmp(stype, "[[i64]]") == 0) return "SplArray*";
    if (strcmp(stype, "[[text]]") == 0) return "SplArray*";
    if (strcmp(stype, "[i64]") == 0) return "SplArray*";
    /* Default: assume struct pointer or int */
    return "int64_t";
}

/* ===== Function Registry ===== */
typedef struct {
    char name[MAX_IDENT];
    char ret_type[MAX_IDENT];  /* C return type */
    char simple_ret[MAX_IDENT]; /* Simple return type */
    int param_count;
    char param_names[MAX_PARAMS][MAX_IDENT];
    char param_types[MAX_PARAMS][MAX_IDENT];   /* C types */
    char param_stypes[MAX_PARAMS][MAX_IDENT];  /* Simple types */
    bool is_extern;
} FuncInfo;

static FuncInfo funcs[MAX_FUNCS];
static int num_funcs = 0;

static FuncInfo *find_func(const char *name) {
    for (int i = 0; i < num_funcs; i++) {
        if (strcmp(funcs[i].name, name) == 0) return &funcs[i];
    }
    return NULL;
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

static void add_var(const char *name, const char *stype) {
    if (num_vars < MAX_VARS) {
        strncpy(vars[num_vars].name, name, MAX_IDENT-1);
        strncpy(vars[num_vars].stype, stype, MAX_IDENT-1);
        vars[num_vars].scope_depth = current_scope;
        num_vars++;
    }
}

static const char *find_var_type(const char *name) {
    /* Search from most recent to oldest */
    for (int i = num_vars - 1; i >= 0; i--) {
        if (strcmp(vars[i].name, name) == 0) return vars[i].stype;
    }
    return NULL;
}

static bool var_is_array(const char *name) {
    const char *t = find_var_type(name);
    return t && t[0] == '[';
}

static bool var_is_text(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "text") == 0;
}

/* Check if variable is an array of text: [text] */
static bool var_is_text_array(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "[text]") == 0;
}

/* Check if variable is a nested array: [[text]], [[i64]], etc */
static bool var_is_nested_array(const char *name) {
    const char *t = find_var_type(name);
    return t && t[0] == '[' && t[1] == '[';
}

/* Check if variable is a bool type */
static bool var_is_bool(const char *name) {
    const char *t = find_var_type(name);
    return t && strcmp(t, "bool") == 0;
}

/* ===== Helpers ===== */

/* Check if expression is a compile-time constant (safe for C static initializer) */
static bool is_constant_expr(const char *e) {
    e = skip_spaces(e);
    if (*e == '\0') return true;
    /* Number literal */
    if (isdigit(*e) || (*e == '-' && isdigit(e[1]))) return true;
    /* String literal */
    if (*e == '"') return true;
    /* Bool/nil */
    if (strcmp(e, "true") == 0 || strcmp(e, "false") == 0 || strcmp(e, "nil") == 0) return true;
    return false;
}

/* ===== Expression Translation ===== */

/* Forward declarations */
static void translate_expr(const char *expr, char *out, int outsz);
static void translate_block(int *line_idx, int base_indent, int c_indent);
static void translate_statement(const char *trimmed, int c_indent);

/* Translate a Simple expression to C */
static void translate_expr(const char *expr, char *out, int outsz) {
    const char *e = skip_spaces(expr);

    /* Empty */
    if (*e == '\0') { snprintf(out, outsz, "0"); return; }

    /* String literal */
    if (*e == '"') {
        /* Check for interpolation: must have {expr} with expr non-empty */
        bool has_interp = false;
        for (const char *p = e + 1; *p && *p != '"'; p++) {
            if (*p == '\\') { p++; continue; }
            if (*p == '{') {
                /* Check that there's a matching } before the end of the string */
                const char *q = p + 1;
                int depth = 1;
                while (*q && depth > 0) {
                    if (*q == '{') depth++;
                    else if (*q == '}') { depth--; if (depth == 0) break; }
                    else if (*q == '"') break; /* hit end of string */
                    q++;
                }
                if (*q == '}' && (q - p) > 1) { has_interp = true; break; }
            }
        }
        if (!has_interp) {
            snprintf(out, outsz, "%s", e);
        } else {
            /* String interpolation: "hello {name}" → spl_sprintf("hello %s", name) */
            /* For simplicity, convert to a series of spl_str_concat calls */
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
                    /* Close current string part */
                    str_buf[str_pos++] = '"';
                    str_buf[str_pos] = '\0';
                    if (str_pos > 2) { /* Not empty string */
                        if (first) {
                            snprintf(buf, sizeof(buf), "%s", str_buf);
                            first = false;
                        } else {
                            snprintf(part, sizeof(part), "spl_str_concat(%s, ", buf);
                            snprintf(buf, sizeof(buf), "%s%s)", part, str_buf);
                        }
                    }

                    /* Extract expression inside {} */
                    p++; /* skip { */
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

                    /* Translate the inner expression */
                    char inner_c[MAX_LINE];
                    translate_expr(expr_buf, inner_c, sizeof(inner_c));

                    /* Convert to string if needed: check if already text */
                    char as_str[MAX_LINE];
                    char *trimmed_expr = trim(expr_buf);
                    if (var_is_text(trimmed_expr) || trimmed_expr[0] == '"') {
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

                    /* Reset string buffer */
                    str_pos = 0;
                    str_buf[str_pos++] = '"';
                    continue;
                }
                str_buf[str_pos++] = *p++;
            }
            if (*p == '"') p++;

            /* Close final string part */
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

    /* Integer literal */
    if (isdigit(*e) || (*e == '-' && isdigit(e[1]))) {
        snprintf(out, outsz, "%s", e);
        return;
    }

    /* Bool literals */
    if (strcmp(e, "true") == 0) { snprintf(out, outsz, "1"); return; }
    if (strcmp(e, "false") == 0) { snprintf(out, outsz, "0"); return; }
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
        /* Find matching close paren */
        int depth = 1;
        const char *p = e + 1;
        while (*p && depth > 0) {
            if (*p == '(') depth++;
            else if (*p == ')') depth--;
            p++;
        }
        /* Check if () is the entire expression */
        const char *after = skip_spaces(p);
        if (*after == '\0') {
            /* Extract inner */
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
        /* For now, emit as spl_array_new() with pushes */
        /* This is a simplification; we'll handle it during statement translation */
        snprintf(out, outsz, "spl_array_new()");
        return;
    }

    /* Binary operators: find the lowest precedence operator not inside parens/brackets */
    {
        int paren = 0;
        int best_pos = -1;
        int best_prec = 999;
        const char *p = e;

        /* Scan for binary operators */
        while (*p) {
            if (*p == '(' || *p == '[') { paren++; p++; continue; }
            if (*p == ')' || *p == ']') { paren--; p++; continue; }
            if (*p == '"') { p++; while (*p && *p != '"') { if (*p == '\\') p++; p++; } if (*p) p++; continue; }

            if (paren == 0) {
                int pos = p - e;
                int prec = 999;
                const char *op = NULL;
                /* Check multi-char operators first */
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
            /* Split at the operator */
            char left_str[MAX_LINE], right_str[MAX_LINE];
            strncpy(left_str, e, best_pos);
            left_str[best_pos] = '\0';

            /* Find the operator and its length */
            const char *op_start = e + best_pos;
            const char *op_str = NULL;
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
            else if (starts_with(op_start, " * ")) { op_str = "*"; skip = 3; }
            else if (starts_with(op_start, " / ")) { op_str = "/"; skip = 3; }
            else if (starts_with(op_start, " % ")) { op_str = "%"; skip = 3; }

            strncpy(right_str, e + best_pos + skip, MAX_LINE-1);
            right_str[MAX_LINE-1] = '\0';

            char left_c[MAX_LINE], right_c[MAX_LINE];
            translate_expr(trim(left_str), left_c, sizeof(left_c));
            translate_expr(trim(right_str), right_c, sizeof(right_c));

            if (strcmp(op_str, "+") == 0) {
                /* Check if either side is text/string for concatenation */
                char *lt = trim(left_str), *rt = trim(right_str);
                bool left_is_str = (lt[0] == '"' || var_is_text(lt));
                bool right_is_str = (rt[0] == '"' || var_is_text(rt));
                if (left_is_str || right_is_str) {
                    snprintf(out, outsz, "spl_str_concat(%s, %s)", left_c, right_c);
                    return;
                }
            }

            /* Nil comparison: x == nil / x != nil */
            if (strcmp(op_str, "==") == 0 || strcmp(op_str, "!=") == 0) {
                char *lt = trim(left_str), *rt = trim(right_str);
                bool nil_on_right = (strcmp(rt, "nil") == 0);
                bool nil_on_left = (strcmp(lt, "nil") == 0);
                if (nil_on_right || nil_on_left) {
                    const char *val_side = nil_on_right ? left_c : right_c;
                    const char *var_name = nil_on_right ? lt : rt;
                    const char *cmp = strcmp(op_str, "==") == 0 ? "==" : "!=";
                    if (var_is_text(var_name)) {
                        snprintf(out, outsz, "(%s %s NULL)", val_side, cmp);
                    } else {
                        snprintf(out, outsz, "(%s %s -1)", val_side, cmp);
                    }
                    return;
                }
            }

            /* String equality/inequality */
            if (strcmp(op_str, "==") == 0 || strcmp(op_str, "!=") == 0) {
                char *lt = trim(left_str), *rt = trim(right_str);
                bool left_is_str = (lt[0] == '"' || var_is_text(lt));
                bool right_is_str = (rt[0] == '"' || var_is_text(rt));
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
                snprintf(out, outsz, "((%s) ? (%s) : (%s))", left_c, left_c, right_c);
                return;
            }

            snprintf(out, outsz, "(%s %s %s)", left_c, op_str, right_c);
            return;
        }
    }

    /* Method calls: obj.method(args) */
    {
        /* Find the last '.' not inside parens/brackets */
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

            /* Common methods */
            if (starts_with(rest, "len()")) {
                if (var_is_text(trim(obj))) {
                    snprintf(out, outsz, "spl_str_len(%s)", obj_c);
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
                /* Check element type for correct wrapping */
                if (var_is_nested_array(trim(obj))) {
                    snprintf(out, outsz, "spl_array_push(%s, spl_array_val(%s))", obj_c, arg_c);
                } else if (var_is_text_array(trim(obj))) {
                    snprintf(out, outsz, "spl_array_push(%s, spl_str(%s))", obj_c, arg_c);
                } else {
                    snprintf(out, outsz, "spl_array_push(%s, spl_int(%s))", obj_c, arg_c);
                }
                return;
            }
            if (starts_with(rest, "pop()")) {
                snprintf(out, outsz, "spl_array_pop(%s).as_int", obj_c);
                return;
            }
            if (starts_with(rest, "contains(")) {
                char arg[MAX_LINE];
                const char *a = rest + 9;
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') {
                    strncpy(arg, a, len - 1);
                    arg[len-1] = '\0';
                }
                char arg_c[MAX_LINE];
                translate_expr(trim(arg), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "spl_str_contains(%s, %s)", obj_c, arg_c);
                return;
            }

            /* String methods: starts_with, ends_with, index_of, trim, replace */
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
            if (starts_with(rest, "replace(")) {
                /* Extract two args: old, new */
                const char *a = rest + 8;
                char args_buf[MAX_LINE];
                int len = strlen(a);
                if (len > 0 && a[len-1] == ')') { strncpy(args_buf, a, len-1); args_buf[len-1] = '\0'; }
                else { strncpy(args_buf, a, MAX_LINE-1); args_buf[MAX_LINE-1] = '\0'; }
                /* Split on comma outside parens */
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

            /* General method call: obj.method(args) → method(obj, args) or obj->method */
            if (strchr(rest, '(')) {
                /* It's a method call */
                char method[MAX_IDENT];
                int mi = 0;
                const char *r = rest;
                while (*r && *r != '(') method[mi++] = *r++;
                method[mi] = '\0';

                /* Extract args (skip strings) */
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
                    translate_expr(trim(args_str), args_c, sizeof(args_c));
                    snprintf(out, outsz, "%s_%s(%s, %s)", obj_c, method, obj_c, args_c);
                } else {
                    snprintf(out, outsz, "%s_%s(%s)", obj_c, method, obj_c);
                }
                return;
            }

            /* Field access: obj.field */
            snprintf(out, outsz, "%s.%s", obj_c, rest);
            return;
        }
    }

    /* Function call: func(args) */
    {
        const char *paren = strchr(e, '(');
        if (paren && !strchr(e, '.')) {
            char func_name[MAX_IDENT];
            int fi = 0;
            const char *p = e;
            while (p < paren && fi < MAX_IDENT - 1) func_name[fi++] = *p++;
            func_name[fi] = '\0';

            /* Extract args (skip strings to avoid paren confusion) */
            p = paren + 1;
            char args[MAX_LINE] = "";
            int depth = 1, ai = 0;
            while (*p && depth > 0) {
                if (*p == '"') {
                    /* Skip string literal entirely */
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

            /* Special built-in: int() */
            if (strcmp(func_name, "int") == 0) {
                char arg_c[MAX_LINE];
                translate_expr(trim(args), arg_c, sizeof(arg_c));
                snprintf(out, outsz, "atoll(%s)", arg_c);
                return;
            }

            /* Translate each argument */
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

    /* Array indexing: arr[i] */
    {
        const char *bracket = strchr(e, '[');
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

            /* Check for slice: arr[start:end] */
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

            if (var_is_nested_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_array", arr_c, idx_c);
            } else if (var_is_text_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_str", arr_c, idx_c);
            } else if (var_is_array(trim(arr_name))) {
                snprintf(out, outsz, "spl_array_get(%s, %s).as_int", arr_c, idx_c);
            } else if (var_is_text(trim(arr_name))) {
                /* String indexing: s[i] → spl_str_index_char(s, i) */
                snprintf(out, outsz, "spl_str_index_char(%s, %s)", arr_c, idx_c);
            } else {
                snprintf(out, outsz, "%s[%s]", arr_c, idx_c);
            }
            return;
        }
    }

    /* Simple identifier */
    if (isalpha(*e) || *e == '_') {
        snprintf(out, outsz, "%s", e);
        return;
    }

    /* Fallback */
    snprintf(out, outsz, "/* TODO: %s */0", e);
}

/* ===== Statement Translation ===== */

/* Parse a val/var name and optional type annotation, advancing p past '=' */
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
        } else {
            while (*p && *p != '=' && *p != ' ') stype[ti++] = *p++;
        }
        stype[ti] = '\0';
        /* Trim trailing spaces */
        ti = strlen(stype);
        while (ti > 0 && stype[ti-1] == ' ') stype[--ti] = '\0';
        p = skip_spaces(p);
    }
    if (*p == '=') { p++; p = skip_spaces(p); }

    /* Type inference from RHS when no annotation */
    if (strcmp(stype, "i64") == 0 && *p != '\0') {
        const char *rhs = skip_spaces(p);
        if (*rhs == '"') {
            strcpy(stype, "text");
        } else if (*rhs == '[') {
            /* Could be array literal */
            strcpy(stype, "[i64]");
        } else if (starts_with(rhs, "spl_array_new") ||
                   starts_with(rhs, "true") || starts_with(rhs, "false")) {
            if (starts_with(rhs, "true") || starts_with(rhs, "false"))
                strcpy(stype, "bool");
        } else if (strcmp(rhs, "nil") == 0) {
            /* nil: keep as i64, could be any type */
        } else if (strstr(rhs, ".as_array")) {
            /* Array value extracted from SplArray */
            strcpy(stype, "[i64]");  /* close enough: SplArray* */
        } else if (strstr(rhs, ".as_str")) {
            strcpy(stype, "text");
        } else {
            /* Check if RHS is a known text-returning function or text variable */
            /* Look for function calls that return text */
            char func[MAX_IDENT] = "";
            int fi = 0;
            const char *fp = rhs;
            while (*fp && *fp != '(' && *fp != '.' && *fp != ' ' && fi < MAX_IDENT-1)
                func[fi++] = *fp++;
            func[fi] = '\0';
            if (var_is_text(func)) {
                strcpy(stype, "text");
            }
            /* Check for method calls on text vars */
            const char *dot = strchr(rhs, '.');
            if (dot) {
                char obj_name[MAX_IDENT] = "";
                int oi = 0;
                const char *op = rhs;
                while (op < dot && oi < MAX_IDENT-1) obj_name[oi++] = *op++;
                obj_name[oi] = '\0';
                const char *method = dot + 1;
                if (var_is_text(obj_name)) {
                    /* Text methods that return text */
                    if (starts_with(method, "trim(") || starts_with(method, "replace(") ||
                        starts_with(method, "slice("))
                        strcpy(stype, "text");
                    /* Text methods that return bool */
                    else if (starts_with(method, "starts_with(") || starts_with(method, "ends_with(") ||
                             starts_with(method, "contains("))
                        strcpy(stype, "bool");
                }
                if (var_is_array(obj_name) || var_is_text_array(obj_name) ||
                    var_is_nested_array(obj_name)) {
                    /* .len() returns i64 */
                    if (starts_with(method, "len(")) strcpy(stype, "i64");
                }
            }
            /* Check for known text-returning functions */
            FuncInfo *fn = find_func(func);
            if (fn) {
                if (strcmp(fn->simple_ret, "text") == 0) strcpy(stype, "text");
                else if (strcmp(fn->simple_ret, "bool") == 0) strcpy(stype, "bool");
                else if (fn->simple_ret[0] == '[') strcpy(stype, fn->simple_ret);
            }
        }
    }

    *pp = p;
}

/* Extract condition from "if <cond>:" — removes trailing colon */
static void extract_condition(const char *line, int skip, char *cond, int condsz) {
    const char *p = line + skip;
    int len = strlen(p);
    /* Remove trailing : */
    if (len > 0 && p[len-1] == ':') len--;
    if (len >= condsz) len = condsz - 1;
    strncpy(cond, p, len);
    cond[len] = '\0';
    /* Trim */
    len = strlen(cond);
    while (len > 0 && (cond[len-1] == ' ' || cond[len-1] == '\t')) cond[--len] = '\0';
}

/* Parse array literal elements: [1, 2, 3] → emit pushes */
static void emit_array_literal_pushes(const char *arr_name, const char *rhs, int c_indent) {
    /* rhs starts with '[', find matching ']' */
    if (rhs[0] != '[') return;
    const char *p = rhs + 1;
    char elem[MAX_LINE];
    int ei = 0;
    int depth = 0;

    while (*p && !(*p == ']' && depth == 0)) {
        if (*p == '[') depth++;
        else if (*p == ']') depth--;
        else if (*p == ',' && depth == 0) {
            elem[ei] = '\0';
            if (ei > 0) {
                char ec[MAX_LINE];
                translate_expr(trim(elem), ec, sizeof(ec));
                emit_indent(c_indent);
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
            emit("spl_array_push(%s, spl_int(%s));\n", arr_name, ec);
        }
    }
}

/* translate_block: process indented lines starting at *line_idx.
 * Processes lines with indent > base_indent. c_indent is the C indentation level. */
static void translate_block(int *line_idx, int base_indent, int c_indent) {
    while (*line_idx < num_lines) {
        const char *line = source_lines[*line_idx];
        int ind = indent_level(line);
        const char *trimmed = trim(line);

        /* Skip blank lines and comments */
        if (trimmed[0] == '\0' || trimmed[0] == '#') { (*line_idx)++; continue; }

        /* End of block: indent returned to or below base */
        if (ind <= base_indent) break;

        /* --- Block-opening statements --- */

        /* Single-line if: "if cond: stmt" (colon not at end) */
        if (starts_with(trimmed, "if ") && !ends_with(trimmed, ":")) {
            /* Find the colon that separates condition from body */
            const char *colon_pos = NULL;
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
                /* Trim */
                int cl = strlen(cond);
                while (cl > 0 && cond[cl-1] == ' ') cond[--cl] = '\0';

                char cond_c[MAX_LINE];
                translate_expr(cond, cond_c, sizeof(cond_c));

                const char *body = skip_spaces(colon_pos + 1);
                emit_indent(c_indent);
                emit("if (%s) ", cond_c);

                /* Translate the body statement inline */
                /* Wrap in {} for safety */
                emit("{ ");
                /* Quick inline statement translation */
                if (starts_with(body, "return ")) {
                    char expr_c[MAX_LINE];
                    translate_expr(body + 7, expr_c, sizeof(expr_c));
                    emit("return %s;", expr_c);
                } else if (strcmp(body, "return") == 0) {
                    emit("return;");
                } else if (strcmp(body, "break") == 0) {
                    emit("break;");
                } else if (strcmp(body, "continue") == 0) {
                    emit("continue;");
                } else {
                    /* General expression or assignment */
                    translate_statement(body, 0);
                }
                emit(" }\n");
                (*line_idx)++;
                continue;
            }
        }

        /* if cond: (block-opening, colon at end) */
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

            /* Check for elif/else chains */
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

        /* for i in start..end: OR for i in range(n): */
        if (starts_with(trimmed, "for ") && ends_with(trimmed, ":")) {
            char body[MAX_LINE];
            extract_condition(trimmed, 4, body, sizeof(body));
            /* Parse: var_name in start..end */
            char var_name[MAX_IDENT] = "";
            int vi = 0;
            const char *p = body;
            while (*p && *p != ' ') var_name[vi++] = *p++;
            var_name[vi] = '\0';
            p = skip_spaces(p);
            if (starts_with(p, "in ")) p += 3;
            p = skip_spaces(p);

            add_var(var_name, "i64");

            /* Check for range patterns */
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
                /* Check for two-arg range(start, end) */
                char *comma = NULL;
                int depth = 0;
                for (int ci = 0; range_arg[ci]; ci++) {
                    if (range_arg[ci] == '(' || range_arg[ci] == '[') depth++;
                    else if (range_arg[ci] == ')' || range_arg[ci] == ']') depth--;
                    else if (range_arg[ci] == ',' && depth == 0) { comma = &range_arg[ci]; break; }
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
            } else {
                /* for item in array: → iterate array */
                char arr_c[MAX_LINE];
                translate_expr(trim((char*)p), arr_c, sizeof(arr_c));
                emit_indent(c_indent);
                emit("for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                     var_name, var_name, arr_c, var_name);
                emit_indent(c_indent + 1);
                emit("int64_t %s = spl_array_get(%s, __%s_i).as_int;\n",
                     var_name, arr_c, var_name);
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

            /* Process case blocks */
            while (*line_idx < num_lines) {
                const char *cline = source_lines[*line_idx];
                const char *ct = trim(cline);
                int ci = indent_level(cline);
                if (ct[0] == '\0' || ct[0] == '#') { (*line_idx)++; continue; }
                if (ci <= ind) break;

                if (starts_with(ct, "case ") && ends_with(ct, ":")) {
                    char case_val[MAX_LINE];
                    extract_condition(ct, 5, case_val, sizeof(case_val));
                    /* Handle pipe-separated values: case 1 | 2 | 3: */
                    char *pipe = strchr(case_val, '|');
                    if (pipe) {
                        /* Multiple case values */
                        char *tok = case_val;
                        while (tok) {
                            char *next_pipe = strchr(tok, '|');
                            if (next_pipe) *next_pipe = '\0';
                            char *tv = trim(tok);
                            if (strcmp(tv, "_") == 0) {
                                emit_indent(c_indent + 1);
                                emit("default:\n");
                            } else {
                                emit_indent(c_indent + 1);
                                emit("case %s:\n", tv);
                            }
                            tok = next_pipe ? next_pipe + 1 : NULL;
                        }
                    } else if (strcmp(trim(case_val), "_") == 0) {
                        emit_indent(c_indent + 1);
                        emit("default:\n");
                    } else {
                        emit_indent(c_indent + 1);
                        emit("case %s:\n", trim(case_val));
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

        /* --- Simple statements (no sub-block) --- */

        /* Skip use/export/import */
        if (starts_with(trimmed, "use ") || starts_with(trimmed, "export ") ||
            starts_with(trimmed, "import ")) {
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
                emit("%s %s = spl_array_new();\n", simple_type_to_c(stype), name);
                emit_array_literal_pushes(name, p, c_indent);
            } else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit_indent(c_indent);
                const char *ct = simple_type_to_c(stype);
                if (starts_with(ct, "const "))
                    emit("%s %s = %s;\n", ct, name, expr_c);
                else
                    emit("const %s %s = %s;\n", ct, name, expr_c);
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
                emit("%s %s = spl_array_new();\n", simple_type_to_c(stype), name);
                emit_array_literal_pushes(name, p, c_indent);
            } else if (stype[0] == '[') {
                /* Empty array or no initializer */
                emit_indent(c_indent);
                emit("%s %s = spl_array_new();\n", simple_type_to_c(stype), name);
            } else {
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit_indent(c_indent);
                emit("%s %s = %s;\n", simple_type_to_c(stype), name, expr_c);
            }
            (*line_idx)++;
            continue;
        }

        /* return */
        if (starts_with(trimmed, "return ")) {
            char expr_c[MAX_LINE];
            translate_expr(trimmed + 7, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            emit("return %s;\n", expr_c);
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
        if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
            emit_indent(c_indent); emit("/* pass */;\n"); (*line_idx)++; continue;
        }
        if (strcmp(trimmed, "pass_todo") == 0) {
            emit_indent(c_indent); emit("/* TODO */;\n"); (*line_idx)++; continue;
        }
        if (starts_with(trimmed, "pass_todo(")) {
            emit_indent(c_indent); emit("/* TODO: <message> */;\n"); (*line_idx)++; continue;
        }
        if (strcmp(trimmed, "pass_do_nothing") == 0) {
            emit_indent(c_indent); emit("/* intentional no-op */;\n"); (*line_idx)++; continue;
        }
        if (starts_with(trimmed, "pass_do_nothing(")) {
            emit_indent(c_indent); emit("/* no-op: <message> */;\n"); (*line_idx)++; continue;
        }
        if (strcmp(trimmed, "pass_dn") == 0) {
            emit_indent(c_indent); emit("/* intentional no-op */;\n"); (*line_idx)++; continue;
        }
        if (starts_with(trimmed, "pass_dn(")) {
            emit_indent(c_indent); emit("/* no-op: <message> */;\n"); (*line_idx)++; continue;
        }
        if (starts_with(trimmed, "pass(")) {
            emit_indent(c_indent); emit("/* pass: <message> */;\n"); (*line_idx)++; continue;
        }

        /* print */
        if (starts_with(trimmed, "print ")) {
            const char *arg = trimmed + 6;
            /* Check if arg is a text expression before translating (trim uses static buf) */
            char arg_trimmed[MAX_LINE];
            strncpy(arg_trimmed, arg, sizeof(arg_trimmed)-1);
            arg_trimmed[sizeof(arg_trimmed)-1] = '\0';
            /* Trim spaces */
            int atl = strlen(arg_trimmed);
            while (atl > 0 && arg_trimmed[atl-1] == ' ') arg_trimmed[--atl] = '\0';
            bool is_text_expr = (*arg == '"' || var_is_text(arg_trimmed));

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

        /* Assignment: check for =, +=, -= */
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
                        /* Check for array element assignment: arr[idx] = val */
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
                                if (var_is_nested_array(trim(aname)))
                                    emit("spl_array_set(%s, %s, spl_array_val(%s));\n", ac, ic, vc);
                                else if (var_is_text_array(trim(aname)))
                                    emit("spl_array_set(%s, %s, spl_str(%s));\n", ac, ic, vc);
                                else
                                    emit("spl_array_set(%s, %s, spl_int(%s));\n", ac, ic, vc);
                                handled = true; break;
                            }
                        }
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

        /* Expression statement (function call, method call, etc.) */
        {
            char expr_c[MAX_LINE];
            translate_expr(trimmed, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            emit("%s;\n", expr_c);
        }
        (*line_idx)++;
    }
}

/* Compatibility: translate a single statement without line tracking */
static void translate_statement(const char *trimmed, int c_indent) {
    /* Skip use/export/import */
    if (starts_with(trimmed, "use ") || starts_with(trimmed, "export ") ||
        starts_with(trimmed, "import ")) return;

    /* val declaration */
    if (starts_with(trimmed, "val ")) {
        const char *p = trimmed + 4;
        char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
        parse_var_decl(&p, name, stype);
        add_var(name, stype);
        if (stype[0] == '[' && *p == '[') {
            emit_indent(c_indent);
            emit("%s %s = spl_array_new();\n", simple_type_to_c(stype), name);
            emit_array_literal_pushes(name, p, c_indent);
        } else {
            char expr_c[MAX_LINE];
            translate_expr(p, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            { const char *ct = simple_type_to_c(stype);
              if (starts_with(ct, "const "))
                  emit("%s %s = %s;\n", ct, name, expr_c);
              else
                  emit("const %s %s = %s;\n", ct, name, expr_c);
            }
        }
        return;
    }

    /* var declaration */
    if (starts_with(trimmed, "var ")) {
        const char *p = trimmed + 4;
        char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
        parse_var_decl(&p, name, stype);
        add_var(name, stype);
        if (stype[0] == '[') {
            emit_indent(c_indent);
            emit("%s %s = spl_array_new();\n", simple_type_to_c(stype), name);
            if (*p == '[') emit_array_literal_pushes(name, p, c_indent);
        } else {
            char expr_c[MAX_LINE];
            translate_expr(p, expr_c, sizeof(expr_c));
            emit_indent(c_indent);
            emit("%s %s = %s;\n", simple_type_to_c(stype), name, expr_c);
        }
        return;
    }

    /* return */
    if (starts_with(trimmed, "return ")) {
        char expr_c[MAX_LINE]; translate_expr(trimmed + 7, expr_c, sizeof(expr_c));
        emit_indent(c_indent); emit("return %s;\n", expr_c); return;
    }
    if (strcmp(trimmed, "return") == 0) { emit_indent(c_indent); emit("return;\n"); return; }

    /* break/continue/pass */
    if (strcmp(trimmed, "break") == 0) { emit_indent(c_indent); emit("break;\n"); return; }
    if (strcmp(trimmed, "continue") == 0) { emit_indent(c_indent); emit("continue;\n"); return; }
    if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
        emit_indent(c_indent); emit("/* pass */;\n"); return;
    }
    if (strcmp(trimmed, "pass_todo") == 0) {
        emit_indent(c_indent); emit("/* TODO */;\n"); return;
    }
    if (starts_with(trimmed, "pass_todo(")) {
        emit_indent(c_indent); emit("/* TODO: <message> */;\n"); return;
    }
    if (strcmp(trimmed, "pass_do_nothing") == 0) {
        emit_indent(c_indent); emit("/* intentional no-op */;\n"); return;
    }
    if (starts_with(trimmed, "pass_do_nothing(")) {
        emit_indent(c_indent); emit("/* no-op: <message> */;\n"); return;
    }
    if (strcmp(trimmed, "pass_dn") == 0) {
        emit_indent(c_indent); emit("/* intentional no-op */;\n"); return;
    }
    if (starts_with(trimmed, "pass_dn(")) {
        emit_indent(c_indent); emit("/* no-op: <message> */;\n"); return;
    }
    if (starts_with(trimmed, "pass(")) {
        emit_indent(c_indent); emit("/* pass: <message> */;\n"); return;
    }

    /* print */
    if (starts_with(trimmed, "print ")) {
        const char *arg = trimmed + 6;
        char arg_trimmed[MAX_LINE];
        strncpy(arg_trimmed, arg, sizeof(arg_trimmed)-1);
        arg_trimmed[sizeof(arg_trimmed)-1] = '\0';
        int atl = strlen(arg_trimmed);
        while (atl > 0 && arg_trimmed[atl-1] == ' ') arg_trimmed[--atl] = '\0';
        bool is_text_expr = (*arg == '"' || var_is_text(arg_trimmed));
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
                    /* Check for array element assignment: arr[idx] = val */
                    char *lhs = trim(t);
                    char *bracket = strchr(lhs, '[');
                    if (bracket) {
                        char arr_name[MAX_IDENT];
                        int ani = 0;
                        const char *lp = lhs;
                        while (lp < bracket) arr_name[ani++] = *lp++;
                        arr_name[ani] = '\0';
                        if (var_is_array(trim(arr_name))) {
                            /* Extract index */
                            char idx_s[MAX_LINE] = "";
                            int idxi = 0;
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

static void process_file(void) {
    /* First pass: collect function signatures */
    for (int i = 0; i < num_lines; i++) {
        const char *line = source_lines[i];
        const char *t = trim(line);

        if (starts_with(t, "fn ") && ends_with(t, ":")) {
            /* Parse: fn name(param: type, ...) -> rettype: */
            FuncInfo *fi = &funcs[num_funcs];
            memset(fi, 0, sizeof(*fi));

            const char *p = t + 3;
            int ni = 0;
            while (*p && *p != '(') fi->name[ni++] = *p++;
            fi->name[ni] = '\0';

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
                /* Trim trailing spaces from param name */
                while (pni > 0 && fi->param_names[fi->param_count][pni-1] == ' ')
                    fi->param_names[fi->param_count][--pni] = '\0';

                if (*p == ':') {
                    p++;
                    p = skip_spaces(p);
                    int pti = 0;
                    if (*p == '[') {
                        fi->param_stypes[fi->param_count][pti++] = *p++;
                        while (*p && *p != ']') fi->param_stypes[fi->param_count][pti++] = *p++;
                        if (*p == ']') fi->param_stypes[fi->param_count][pti++] = *p++;
                    } else {
                        while (*p && *p != ',' && *p != ')')
                            fi->param_stypes[fi->param_count][pti++] = *p++;
                    }
                    fi->param_stypes[fi->param_count][pti] = '\0';
                    /* Trim */
                    while (pti > 0 && fi->param_stypes[fi->param_count][pti-1] == ' ')
                        fi->param_stypes[fi->param_count][--pti] = '\0';
                    strcpy(fi->param_types[fi->param_count], simple_type_to_c(fi->param_stypes[fi->param_count]));
                } else {
                    strcpy(fi->param_stypes[fi->param_count], "i64");
                    strcpy(fi->param_types[fi->param_count], "int64_t");
                }
                fi->param_count++;
                if (*p == ',') p++;
            }

            /* Parse return type */
            if (*p == ')') p++;
            p = skip_spaces(p);
            if (starts_with(p, "->")) {
                p += 2;
                p = skip_spaces(p);
                int rti = 0;
                while (*p && *p != ':') fi->simple_ret[rti++] = *p++;
                fi->simple_ret[rti] = '\0';
                while (rti > 0 && fi->simple_ret[rti-1] == ' ')
                    fi->simple_ret[--rti] = '\0';
                strcpy(fi->ret_type, simple_type_to_c(fi->simple_ret));
            } else {
                strcpy(fi->simple_ret, "void");
                strcpy(fi->ret_type, "void");
            }

            num_funcs++;
        }

        if (starts_with(t, "extern fn ")) {
            FuncInfo *fi = &funcs[num_funcs];
            memset(fi, 0, sizeof(*fi));
            fi->is_extern = true;

            const char *p = t + 10;
            int ni = 0;
            while (*p && *p != '(') fi->name[ni++] = *p++;
            fi->name[ni] = '\0';

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

                if (*p == ':') {
                    p++; p = skip_spaces(p);
                    int pti = 0;
                    if (*p == '[') {
                        fi->param_stypes[fi->param_count][pti++] = *p++;
                        while (*p && *p != ']') fi->param_stypes[fi->param_count][pti++] = *p++;
                        if (*p == ']') fi->param_stypes[fi->param_count][pti++] = *p++;
                    } else {
                        while (*p && *p != ',' && *p != ')')
                            fi->param_stypes[fi->param_count][pti++] = *p++;
                    }
                    fi->param_stypes[fi->param_count][pti] = '\0';
                    while (pti > 0 && fi->param_stypes[fi->param_count][pti-1] == ' ')
                        fi->param_stypes[fi->param_count][--pti] = '\0';
                    strcpy(fi->param_types[fi->param_count], simple_type_to_c(fi->param_stypes[fi->param_count]));
                } else {
                    strcpy(fi->param_stypes[fi->param_count], "i64");
                    strcpy(fi->param_types[fi->param_count], "int64_t");
                }
                fi->param_count++;
                if (*p == ',') p++;
            }

            if (*p == ')') p++;
            p = skip_spaces(p);
            if (starts_with(p, "->")) {
                p += 2; p = skip_spaces(p);
                int rti = 0;
                while (*p && *p != ' ' && *p != '\0') fi->simple_ret[rti++] = *p++;
                fi->simple_ret[rti] = '\0';
                strcpy(fi->ret_type, simple_type_to_c(fi->simple_ret));
            } else {
                strcpy(fi->simple_ret, "void");
                strcpy(fi->ret_type, "void");
            }

            num_funcs++;
        }
    }

    /* Emit header */
    emit("#if !defined(_WIN32)\n");
    emit("#define _POSIX_C_SOURCE 200809L\n");
    emit("#endif\n");
    emit("#include <stdio.h>\n");
    emit("#include <stdlib.h>\n");
    emit("#include <string.h>\n");
    emit("#include <stdint.h>\n");
    emit("#include <stdarg.h>\n");
    emit("#include \"runtime.h\"\n\n");

    /* Emit extern declarations */
    for (int i = 0; i < num_funcs; i++) {
        if (funcs[i].is_extern) {
            emit("extern %s %s(", funcs[i].ret_type, funcs[i].name);
            for (int j = 0; j < funcs[i].param_count; j++) {
                if (j > 0) emit(", ");
                emit("%s %s", funcs[i].param_types[j], funcs[i].param_names[j]);
            }
            emit(");\n");
        }
    }
    emit("\n");

    /* Emit forward declarations for non-extern functions */
    for (int i = 0; i < num_funcs; i++) {
        if (!funcs[i].is_extern) {
            emit("%s %s(", funcs[i].ret_type, funcs[i].name);
            for (int j = 0; j < funcs[i].param_count; j++) {
                if (j > 0) emit(", ");
                emit("%s %s", funcs[i].param_types[j], funcs[i].param_names[j]);
            }
            emit(");\n");
        }
    }
    emit("\n");

    /* Emit module-level variables */
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

            const char *ctype = simple_type_to_c(stype);

            if (stype[0] == '[') {
                /* Array: just declare, init in __module_init */
                emit("static %s %s;\n", ctype, name);
            } else if (is_constant_expr(p)) {
                /* Constant: static initialize */
                char expr_c[MAX_LINE];
                translate_expr(p, expr_c, sizeof(expr_c));
                emit("static %s %s = %s;\n", ctype, name, expr_c);
            } else {
                /* Non-constant: declare with default, init in __module_init */
                if (strcmp(ctype, "const char*") == 0)
                    emit("static %s %s = \"\";\n", ctype, name);
                else
                    emit("static %s %s = 0;\n", ctype, name);
            }
        }
    }
    emit("\n");

    /* Emit function definitions */
    for (int i = 0; i < num_lines; i++) {
        const char *line = source_lines[i];
        int ind = indent_level(line);
        const char *t = trim(line);

        if (ind != 0) continue;
        if (!starts_with(t, "fn ") || !ends_with(t, ":")) continue;

        /* Find function info */
        char fname[MAX_IDENT] = "";
        const char *p = t + 3;
        int ni = 0;
        while (*p && *p != '(') fname[ni++] = *p++;
        fname[ni] = '\0';

        FuncInfo *fi = find_func(fname);
        if (!fi) continue;

        /* Add params to var registry */
        for (int j = 0; j < fi->param_count; j++) {
            add_var(fi->param_names[j], fi->param_stypes[j]);
        }

        /* Emit function header */
        emit("%s %s(", fi->ret_type, fi->name);
        for (int j = 0; j < fi->param_count; j++) {
            if (j > 0) emit(", ");
            emit("%s %s", fi->param_types[j], fi->param_names[j]);
        }
        emit(") {\n");

        /* Handle implicit return: if function has non-void return type,
         * find the last non-blank/non-comment line at body indent level
         * and prepend "return" if it's a bare expression. */
        if (strcmp(fi->ret_type, "void") != 0) {
            /* Find end of function body */
            int body_end = i + 1;
            while (body_end < num_lines) {
                const char *bl = source_lines[body_end];
                int bi = indent_level(bl);
                const char *bt = trim(bl);
                if (bt[0] == '\0' || bt[0] == '#') { body_end++; continue; }
                if (bi <= 0) break;
                body_end++;
            }
            /* Find last meaningful line at indent level 1 */
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
                /* Check if it's a bare expression (not return/if/while/for/match/val/var/assignment/break) */
                bool needs_return = true;
                if (starts_with(lt, "return ") || strcmp(lt, "return") == 0) needs_return = false;
                if (starts_with(lt, "if ") || starts_with(lt, "while ") ||
                    starts_with(lt, "for ") || starts_with(lt, "match ")) needs_return = false;
                if (starts_with(lt, "elif ") || strcmp(lt, "else:") == 0) needs_return = false;
                if (starts_with(lt, "val ") || starts_with(lt, "var ")) needs_return = false;
                if (starts_with(lt, "break") || starts_with(lt, "continue")) needs_return = false;
                if (starts_with(lt, "print ") || starts_with(lt, "println ")) needs_return = false;
                if (starts_with(lt, "case ")) needs_return = false;
                /* Check for assignment (has = not inside == != <= >=) */
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
                    /* Prepend "return " to this line */
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

        /* Process body using translate_block */
        int body_idx = i + 1;
        translate_block(&body_idx, 0, 1);
        /* Skip past function body lines */
        i = body_idx - 1;

        emit("}\n\n");
    }

    /* Emit initialization function for module-level arrays and code */
    emit("static void __module_init(void) {\n");
    {
        /* Build a virtual source that has only module-level init code.
         * We use translate_block to handle control flow properly.
         * But first, collect init-relevant line indices. */
        int init_idx = 0;
        while (init_idx < num_lines) {
            const char *line = source_lines[init_idx];
            int ind = indent_level(line);
            const char *t = trim(line);

            if (ind != 0) { init_idx++; continue; }
            if (t[0] == '\0' || t[0] == '#') { init_idx++; continue; }

            /* Skip function/extern/struct/enum declarations + their bodies */
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
            if ((starts_with(t, "struct ") || starts_with(t, "enum ")) && ends_with(t, ":")) {
                init_idx++;
                while (init_idx < num_lines) {
                    if (indent_level(source_lines[init_idx]) == 0) break;
                    init_idx++;
                }
                continue;
            }
            if (starts_with(t, "use ") || starts_with(t, "export ") || starts_with(t, "import ")) {
                init_idx++; continue;
            }

            /* val/var: init arrays and non-constants */
            if (starts_with(t, "val ") || starts_with(t, "var ")) {
                const char *p = t + 4;
                char name[MAX_IDENT] = "", stype[MAX_IDENT] = "";
                parse_var_decl(&p, name, stype);

                if (stype[0] == '[') {
                    emit("    %s = spl_array_new();\n", name);
                    if (*p == '[' && *(p+1) != ']') {
                        emit_array_literal_pushes(name, p, 1);
                    }
                } else if (!is_constant_expr(p)) {
                    char expr_c[MAX_LINE];
                    translate_expr(p, expr_c, sizeof(expr_c));
                    emit("    %s = %s;\n", name, expr_c);
                }
                init_idx++;
                continue;
            }

            /* Module-level control flow or expression: use translate_block
             * if it's a block-opening statement */
            if ((starts_with(t, "if ") || starts_with(t, "while ") ||
                 starts_with(t, "for ") || starts_with(t, "match ")) &&
                ends_with(t, ":")) {
                /* translate_block handles this line + its body */
                translate_block(&init_idx, -1, 1);
                continue;
            }

            /* Simple expression/statement */
            translate_statement(t, 1);
            init_idx++;
        }
    }
    emit("}\n\n");

    /* Emit main */
    emit("int main(int argc, char** argv) {\n");
    emit("    spl_init_args(argc, argv);\n");
    emit("    __module_init();\n");
    emit("    return 0;\n");
    emit("}\n");
}

/* ===== Main ===== */
int main(int argc, char *argv[]) {
    if (argc < 2) {
        fprintf(stderr, "Usage: %s input.spl [> output.c]\n", argv[0]);
        return 1;
    }

    load_file(argv[1]);
    process_file();

    /* Write output */
    fwrite(output, 1, out_pos, stdout);

    return 0;
}
