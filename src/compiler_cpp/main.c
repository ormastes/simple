/*
 * Simple Language Bootstrap CLI
 *
 * Minimal bootstrap binary providing:
 *   - Version/help display
 *   - Simple→C translation (delegates to codegen)
 *   - Compile-and-run for .spl files (via codegen + C compiler)
 *
 * This is NOT the full Simple CLI. The full CLI is written in Simple
 * and interpreted by the pre-built binary (bin/simple). This bootstrap
 * exists to enable building Simple from scratch on a new platform.
 *
 * Build:
 *   cmake -B build -G Ninja -DCMAKE_C_COMPILER=clang -S src/compiler_cpp
 *   ninja -C build -j7
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/stat.h>

#include "runtime.h"

#define BOOTSTRAP_VERSION "0.5.0-bootstrap"

static void print_help(void) {
    puts("Simple Language Bootstrap CLI v" BOOTSTRAP_VERSION);
    puts("");
    puts("Usage:");
    puts("  simple --help              Show this help");
    puts("  simple --version           Show version");
    puts("  simple gen-c <src> <out>   Translate Simple source to C");
    puts("  simple compile <src>       Compile Simple source to executable");
    puts("  simple <file.spl>          Run Simple source file (compile-and-run)");
    puts("");
    puts("This is the bootstrap binary. For the full Simple CLI,");
    puts("use the pre-built binary at bin/simple.");
    puts("");
    puts("Bootstrap flow:");
    puts("  1. simple gen-c src/app/compile/real_compiler.spl out.c");
    puts("  2. clang -o simple_codegen out.c -std=gnu11");
    puts("  3. Use simple_codegen to translate more files");
}

static void print_version(void) {
    printf("Simple v%s\n", BOOTSTRAP_VERSION);
}

/* Find the codegen binary (simple_codegen) relative to this binary */
static const char* find_codegen(const char* self_path) {
    /* Try same directory as this binary */
    static char buf[4096];
    const char* last_slash = strrchr(self_path, '/');
    if (last_slash) {
        size_t dir_len = (size_t)(last_slash - self_path);
        memcpy(buf, self_path, dir_len);
        strcpy(buf + dir_len, "/simple_codegen");
        if (access(buf, X_OK) == 0) return buf;
    }
    /* Try ./simple_codegen */
    if (access("./simple_codegen", X_OK) == 0) return "./simple_codegen";
    /* Try build/simple_codegen */
    if (access("build/simple_codegen", X_OK) == 0) return "build/simple_codegen";
    return NULL;
}

/* Generate C from Simple source using the codegen tool */
/* Codegen expects: argv[0]=binary argv[1]=_ argv[2]=source argv[3]=output */
static int gen_c(const char* codegen_path, const char* src, const char* out) {
    char cmd[8192];
    snprintf(cmd, sizeof(cmd), "%s _ %s %s", codegen_path, src, out);
    return system(cmd);
}

/* Compile a C file to executable */
static int compile_c(const char* c_file, const char* out_file) {
    char cmd[8192];
    /* Try clang first, fall back to gcc */
    snprintf(cmd, sizeof(cmd),
        "clang -std=gnu11 -O2 -o %s %s -lm -lpthread -ldl 2>/dev/null || "
        "gcc -std=gnu11 -O2 -o %s %s -lm -lpthread -ldl",
        out_file, c_file, out_file, c_file);
    return system(cmd);
}

/* Compile-and-run: translate .spl to C, compile, execute */
static int compile_and_run(const char* codegen_path, const char* spl_file,
                           int argc, char** argv) {
    char c_file[4096];
    char exe_file[4096];
    char cmd[8192];

    /* Create temp files */
    snprintf(c_file, sizeof(c_file), "/tmp/simple_bootstrap_%d.c", getpid());
    snprintf(exe_file, sizeof(exe_file), "/tmp/simple_bootstrap_%d", getpid());

    /* Step 1: Generate C */
    printf("[bootstrap] Translating %s to C...\n", spl_file);
    int rc = gen_c(codegen_path, spl_file, c_file);
    if (rc != 0) {
        fprintf(stderr, "Error: codegen failed for %s\n", spl_file);
        return 1;
    }

    /* Step 2: Compile C */
    printf("[bootstrap] Compiling C code...\n");
    rc = compile_c(c_file, exe_file);
    if (rc != 0) {
        fprintf(stderr, "Error: C compilation failed\n");
        unlink(c_file);
        return 1;
    }

    /* Step 3: Run executable */
    size_t offset = 0;
    offset += (size_t)snprintf(cmd + offset, sizeof(cmd) - offset, "%s", exe_file);
    for (int i = 2; i < argc && offset < sizeof(cmd) - 256; i++) {
        offset += (size_t)snprintf(cmd + offset, sizeof(cmd) - offset, " %s", argv[i]);
    }
    rc = system(cmd);

    /* Cleanup */
    unlink(c_file);
    unlink(exe_file);

    return WEXITSTATUS(rc);
}

int main(int argc, char** argv) {
    spl_init_args(argc, argv);

    if (argc < 2) {
        print_help();
        return 0;
    }

    const char* cmd = argv[1];

    /* --help / -h */
    if (strcmp(cmd, "--help") == 0 || strcmp(cmd, "-h") == 0) {
        print_help();
        return 0;
    }

    /* --version / -v */
    if (strcmp(cmd, "--version") == 0 || strcmp(cmd, "-v") == 0) {
        print_version();
        return 0;
    }

    /* gen-c <source.spl> <output.c> — translate Simple to C */
    if (strcmp(cmd, "gen-c") == 0) {
        if (argc < 4) {
            fprintf(stderr, "Usage: simple gen-c <source.spl> <output.c>\n");
            return 1;
        }
        const char* codegen = find_codegen(argv[0]);
        if (!codegen) {
            fprintf(stderr, "Error: cannot find simple_codegen binary\n");
            return 1;
        }
        return gen_c(codegen, argv[2], argv[3]) == 0 ? 0 : 1;
    }

    /* compile <source.spl> [-o output] — compile to executable */
    if (strcmp(cmd, "compile") == 0) {
        if (argc < 3) {
            fprintf(stderr, "Usage: simple compile <source.spl> [-o output]\n");
            return 1;
        }
        const char* src = argv[2];
        const char* out = "a.out";
        for (int i = 3; i < argc - 1; i++) {
            if (strcmp(argv[i], "-o") == 0) {
                out = argv[i + 1];
                break;
            }
        }
        const char* codegen = find_codegen(argv[0]);
        if (!codegen) {
            fprintf(stderr, "Error: cannot find simple_codegen binary\n");
            return 1;
        }
        char c_file[4096];
        snprintf(c_file, sizeof(c_file), "/tmp/simple_compile_%d.c", getpid());
        int rc = gen_c(codegen, src, c_file);
        if (rc != 0) {
            fprintf(stderr, "Error: codegen failed for %s\n", src);
            return 1;
        }
        rc = compile_c(c_file, out);
        unlink(c_file);
        if (rc != 0) {
            fprintf(stderr, "Error: C compilation failed\n");
            return 1;
        }
        printf("Compiled: %s -> %s\n", src, out);
        return 0;
    }

    /* <file.spl> — compile-and-run */
    if (strstr(cmd, ".spl") != NULL) {
        if (access(cmd, R_OK) != 0) {
            fprintf(stderr, "Error: file not found: %s\n", cmd);
            return 1;
        }
        const char* codegen = find_codegen(argv[0]);
        if (!codegen) {
            fprintf(stderr, "Error: cannot find simple_codegen binary\n");
            return 1;
        }
        return compile_and_run(codegen, cmd, argc, argv);
    }

    fprintf(stderr, "Error: unknown command '%s'\n", cmd);
    fprintf(stderr, "Run 'simple --help' for usage information.\n");
    return 1;
}
