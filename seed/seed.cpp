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
 *   c++ -std=c++20 -o output output.cpp seed/runtime.c -Iseed
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

#ifdef _WIN32
#define strdup _strdup
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
        strip_inline_comment(buf);
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
#define MAX_OPTION_TYPES 128
typedef struct {
    char simple_base[MAX_IDENT];  /* Base Simple type: "text", "i64", "MyStruct" */
    char cpp_base[MAX_IDENT];     /* Base C++ type: "const char*", "int64_t", etc. */
    char option_name[MAX_IDENT];  /* C++ struct name: "Option_text", etc. */
} OptionTypeInfo;

static OptionTypeInfo option_types[MAX_OPTION_TYPES];
static int num_option_types = 0;

/* ===== Result Type Registry ===== */
/* Tracks which Result<T, E> types are needed, generates C++ structs */
#define MAX_RESULT_TYPES 128
typedef struct {
    char ok_type[MAX_IDENT];    /* Success type T */
    char err_type[MAX_IDENT];   /* Error type E */
    char cpp_ok[MAX_IDENT];     /* C++ ok type */
    char cpp_err[MAX_IDENT];    /* C++ err type */
    char result_name[MAX_IDENT]; /* C++ struct name: "Result_T_E" */
} ResultTypeInfo;

static ResultTypeInfo result_types[MAX_RESULT_TYPES];
static int num_result_types = 0;

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
        if (!found && num_option_types < MAX_OPTION_TYPES) {
            OptionTypeInfo *oi = &option_types[num_option_types];
            strcpy(oi->simple_base, base);
            /* Recursive call for base type */
            strcpy(oi->cpp_base, simple_type_to_cpp(base));
            if (base[0] == '[')
                snprintf(oi->option_name, MAX_IDENT, "Option_array");
            else
                snprintf(oi->option_name, MAX_IDENT, "Option_%s", base);
            num_option_types++;
        }
        /* Return option struct name */
        static char option_buf[MAX_IDENT];
        if (base[0] == '[')
            snprintf(option_buf, sizeof(option_buf), "Option_array");
        else
            snprintf(option_buf, sizeof(option_buf), "Option_%s", base);
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
            if (!found && num_option_types < MAX_OPTION_TYPES) {
                OptionTypeInfo *oi = &option_types[num_option_types];
                strcpy(oi->simple_base, param);
                /* Recursive call for base type */
                strcpy(oi->cpp_base, simple_type_to_cpp(param));
                if (param[0] == '[')
                    snprintf(oi->option_name, MAX_IDENT, "Option_array");
                else
                    snprintf(oi->option_name, MAX_IDENT, "Option_%s", param);
                num_option_types++;
            }
            /* Return option struct name */
            static char option_buf[MAX_IDENT];
            if (param[0] == '[')
                snprintf(option_buf, sizeof(option_buf), "Option_array");
            else
                snprintf(option_buf, sizeof(option_buf), "Option_%s", param);
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
            if (!found && num_result_types < MAX_RESULT_TYPES) {
                ResultTypeInfo *ri = &result_types[num_result_types];
                strcpy(ri->ok_type, ok_type);
                strcpy(ri->err_type, err_type);
                strcpy(ri->cpp_ok, simple_type_to_cpp(ok_type));
                strcpy(ri->cpp_err, simple_type_to_cpp(err_type));
                snprintf(ri->result_name, MAX_IDENT, "Result_%s_%s", ok_type, err_type);
                num_result_types++;
            }
            /* Return result struct name */
            static char result_buf[MAX_IDENT];
            snprintf(result_buf, sizeof(result_buf), "Result_%s_%s", ok_type, err_type);
            return result_buf;
        }
    }
    /* Common generic types that Simple uses but aren't structs */
    if (strcmp(stype, "Result") == 0) return "int64_t"; /* bare Result without type params */
    if (strcmp(stype, "Option") == 0) return "int64_t"; /* bare Option without type param */
    if (strncmp(stype, "Effect<", 7) == 0 || strcmp(stype, "Effect") == 0) return "int64_t";
    if (strcmp(stype, "Any") == 0) return "int64_t";
    if (strncmp(stype, "Iterator<", 9) == 0) return "int64_t";
    if (strncmp(stype, "Fn<", 3) == 0 || strncmp(stype, "fn(", 3) == 0) return "int64_t";
    /* Default */
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
        /* Raw Simple syntax leaked into C++ */
        if (i == 0 || start[i-1] == '\n' || start[i-1] == ' ' || start[i-1] == '(') {
            if (strncmp(start + i, "val ", 4) == 0) problems++;
            if (strncmp(start + i, "var ", 4) == 0 && strncmp(start + i, "var_", 4) != 0) problems++;
            if (strncmp(start + i, "fn ", 3) == 0) problems++;
            if (strncmp(start + i, "elif ", 5) == 0) problems++;
            if (strncmp(start + i, "elif:", 5) == 0) problems++;
            if (strncmp(start + i, "impl ", 5) == 0) problems++;
            if (strncmp(start + i, "trait ", 6) == 0) problems++;
            if (strncmp(start + i, "match ", 6) == 0 && strncmp(start + i, "match(", 6) != 0) problems++;
        }
    }
    if (line_len > max_line_len) max_line_len = line_len;

    /* Garbled output produces extremely long lines */
    if (max_line_len > 300) return true;
    /* Unbalanced braces indicate broken output */
    if (brace_depth != 0) return true;
    /* If too many problems, the body is garbled */
    if (nested_funcs > 0) return true;
    if (todos > 0) return true;
    if (problems > 0) return true;
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
                if (*q == '}' && (q - p) > 1) { has_interp = true; break; }
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
                    if (var_is_text(trimmed_expr) || trimmed_expr[0] == '"' || expr_is_text(trimmed_expr)) {
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

            strncpy(right_str, e + best_pos + skip, MAX_LINE-1);
            right_str[MAX_LINE-1] = '\0';

            char left_c[MAX_LINE], right_c[MAX_LINE];
            translate_expr(trim(left_str), left_c, sizeof(left_c));
            translate_expr(trim(right_str), right_c, sizeof(right_c));

            if (strcmp(op_str, "+") == 0) {
                char *lt = trim(left_str), *rt = trim(right_str);
                bool left_is_str = expr_is_text(lt);
                bool right_is_str = expr_is_text(rt);
                if (left_is_str || right_is_str) {
                    snprintf(out, outsz, "spl_str_concat(%s, %s)", left_c, right_c);
                    return;
                }
            }

            /* Nil comparison */
            if (strcmp(op_str, "==") == 0 || strcmp(op_str, "!=") == 0) {
                char *lt = trim(left_str), *rt = trim(right_str);
                bool nil_on_right = (strcmp(rt, "nil") == 0);
                bool nil_on_left = (strcmp(lt, "nil") == 0);
                if (nil_on_right || nil_on_left) {
                    const char *val_side = nil_on_right ? left_c : right_c;
                    const char *var_name = nil_on_right ? lt : rt;
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
                char *lt = trim(left_str), *rt = trim(right_str);
                bool left_is_str = expr_is_text(lt);
                bool right_is_str = expr_is_text(rt);
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
                char *lt = trim(left_str);
                if (expr_is_option(lt)) {
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
                        translate_expr(trim(val_buf), val_c, sizeof(val_c));

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
                snprintf(out, outsz, "%s_%s", enum_name, func_name);
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
            snprintf(out, outsz, "%s_%s", ename, e);
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
                    else if (starts_with(method, "starts_with(") || starts_with(method, "ends_with(") ||
                             starts_with(method, "contains("))
                        strcpy(stype, "bool");
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
        if (strcmp(stype, "i64") == 0 && expr_is_text(rhs)) {
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
            } else if (!find_var_type(trim((char*)p)) && !strchr(p, '.') && !strchr(p, '(')) {
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
                if (arr_stype && type_is_struct_array(arr_stype)) {
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
                                    emit_indent(c_indent + 1);
                                    emit("case %s_%s:\n", enum_name, variant);
                                } else {
                                    /* Check if it's an enum variant */
                                    const char *ev_enum = find_variant_enum(tv);
                                    emit_indent(c_indent + 1);
                                    if (ev_enum)
                                        emit("case %s_%s:\n", ev_enum, tv);
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
                            emit_indent(c_indent + 1);
                            emit("case %s_%s:\n", enum_name, variant);
                        } else {
                            const char *ev_enum = find_variant_enum(cv);
                            emit_indent(c_indent + 1);
                            if (ev_enum)
                                emit("case %s_%s:\n", ev_enum, cv);
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
        if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
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
            char expr_c[MAX_LINE];
            translate_expr(trimmed, expr_c, sizeof(expr_c));

            /* Check if this is an implicit return (last expression in function body) */
            bool is_implicit_return = false;
            if (current_func && strcmp(current_func->ret_type, "void") != 0) {
                /* Peek ahead to see if next line exits the block */
                int next_idx = *line_idx + 1;
                if (next_idx >= num_lines) {
                    /* End of file - this is last line */
                    is_implicit_return = true;
                } else {
                    const char *next_line = source_lines[next_idx];
                    const char *next_trimmed = trim(next_line);
                    int next_ind = indent_level(next_line);
                    /* If next line is less indented or is closing syntax, this is last expr */
                    if (next_ind <= base_indent || next_trimmed[0] == '\0' || next_trimmed[0] == '#') {
                        is_implicit_return = true;
                    }
                }
            }

            emit_indent(c_indent);
            if (is_implicit_return) {
                emit("return %s;\n", expr_c);
            } else {
                emit("%s;\n", expr_c);
            }
        }
        (*line_idx)++;
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

    if (strcmp(trimmed, "pass") == 0 || strcmp(trimmed, "()") == 0) {
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

    /* If method, prepend owner struct name */
    if (is_method && owner[0]) {
        snprintf(fi->name, MAX_IDENT, "%s__", owner);
        ni = strlen(fi->name);
        strcpy(fi->owner_struct, owner);
    }

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
                while (*p && (angle_depth > 0 || (*p != ',' && *p != ')'))) {
                    if (*p == '<') angle_depth++;
                    if (*p == '>') angle_depth--;
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
        if (i >= 365 && i <= 375) {
            fprintf(stderr, "[seed_cpp] DEBUG: Line %d, ind=%d, raw: %.60s | trimmed: %.60s\n", i, ind, line, t);
        }
        if (t[0] == '\0' || t[0] == '#') continue;

        /* Top-level struct or class */
        if (ind == 0 && (starts_with(t, "struct ") || starts_with(t, "class ")) && ends_with(t, ":")) {
            bool is_class = starts_with(t, "class ");
            char sname[MAX_IDENT] = "";
            const char *p = t + (is_class ? 6 : 7);
            int ni = 0;
            while (*p && *p != ':' && *p != '(' && *p != ' ') sname[ni++] = *p++;
            sname[ni] = '\0';

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
            }
        }

        /* Top-level enum */
        if (ind == 0 && starts_with(t, "enum ") && ends_with(t, ":")) {
            char ename[MAX_IDENT] = "";
            const char *p = t + 5;
            int ni = 0;
            while (*p && *p != ':' && *p != ' ') ename[ni++] = *p++;
            ename[ni] = '\0';

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
                while (j < num_lines) {
                    const char *vl = source_lines[j];
                    const char *vt = trim(vl);
                    if (vt[0] == '\0') { j++; continue; } /* Skip blank lines before indent check */
                    if (indent_level(vl) <= 0) break;
                    if (vt[0] == '#') { j++; continue; }
                    /* Simple variant (no data): just the name */
                    char vname[MAX_IDENT] = "";
                    int vni = 0;
                    const char *vp = vt;
                    while (*vp && *vp != '(' && *vp != ' ' && *vp != '#' && *vp != ':')
                        vname[vni++] = *vp++;
                    vname[vni] = '\0';
                    /* Skip variant names starting with '"' (leaked docstrings) */
                    if (vname[0] && vname[0] != '"' && ei->variant_count < MAX_VARIANTS) {
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
            int ni = 0;
            while (*p && *p != ':' && *p != '(' && *p != ' ') impl_name[ni++] = *p++;
            impl_name[ni] = '\0';

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
    emit("typedef uint64_t u64;\n\n");
    emit("/* Common constants from stdlib */\n");
    emit("static const char* NL = \"\\n\";\n\n");

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
        emit("/* enum %s */\n", ei->name);
        for (int j = 0; j < ei->variant_count; j++) {
            emit("static const int64_t %s_%s = %d;\n", ei->name, ei->variants[j], j);
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

    /* Phase B: Emit primitive Option structs (base type is NOT a user struct) */
    for (int i = 0; i < num_option_types; i++) {
        OptionTypeInfo *oi = &option_types[i];
        if (find_struct(oi->simple_base)) continue; /* skip struct-based Options */
        emit("/* Option<%s> */\n", oi->simple_base);
        emit("struct %s {\n", oi->option_name);
        emit("    bool has_value;\n");
        emit("    %s value;\n", oi->cpp_base);
        emit("    %s() : has_value(false), value{} {}\n", oi->option_name);
        emit("    %s(%s v) : has_value(true), value(v) {}\n", oi->option_name, oi->cpp_base);
        emit("    %s(SplValue) : has_value(false), value{} {}\n", oi->option_name);
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

    /* Phase D: Emit struct-based Option structs (base type IS a user struct) */
    for (int i = 0; i < num_option_types; i++) {
        OptionTypeInfo *oi = &option_types[i];
        if (!find_struct(oi->simple_base)) continue; /* skip primitive Options */
        emit("/* Option<%s> */\n", oi->simple_base);
        emit("struct %s {\n", oi->option_name);
        emit("    bool has_value;\n");
        emit("    %s value;\n", oi->cpp_base);
        emit("    %s() : has_value(false), value{} {}\n", oi->option_name);
        emit("    %s(%s v) : has_value(true), value(v) {}\n", oi->option_name, oi->cpp_base);
        emit("    %s(SplValue) : has_value(false), value{} {}\n", oi->option_name);
        emit("};\n\n");
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
            int ni = 0;
            while (*p && *p != '(') fname[ni++] = *p++;
            fname[ni] = '\0';

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
            int ni = 0;
            while (*p && *p != ':' && *p != '(' && *p != ' ') impl_name[ni++] = *p++;
            impl_name[ni] = '\0';

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
                    int mni = 0;
                    const char *mp = mstart;
                    while (*mp && *mp != '(') mname[mni++] = *mp++;
                    mname[mni] = '\0';

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
                        /* Array iteration */
                        char arr_c[MAX_LINE];
                        translate_expr(tr_iter, arr_c, sizeof(arr_c));
                        emit("    for (int64_t __%s_i = 0; __%s_i < spl_array_len(%s); __%s_i++) {\n",
                             var_name, var_name, arr_c, var_name);
                        emit("        int64_t %s = spl_array_get(%s, __%s_i).as_int;\n",
                             var_name, arr_c, var_name);
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
    process_file();
    fprintf(stderr, "[seed_cpp] Processing complete. Output size: %d bytes\n", out_pos);

    fwrite(output, 1, out_pos, stdout);
    free(output);

    return 0;
}
