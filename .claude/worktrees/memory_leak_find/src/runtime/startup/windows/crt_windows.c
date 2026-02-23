/*
 * Simple Seed — Windows CRT (shared x86/x86_64)
 *
 * Windows does not pass argc/argv to the entry point.
 * We parse them from GetCommandLineA / CommandLineToArgvW,
 * or use the MinGW __getmainargs helper.
 *
 * ExitProcess is imported from kernel32.dll.
 */

#include "../common/crt_common.h"

#ifdef _WIN32
#include <windows.h>
#else
/* Cross-compilation: declare Windows API symbols resolved at link time */
extern char  *GetCommandLineA(void);
extern void  *CommandLineToArgvW(const void *lpCmdLine, int *pNumArgs);
extern void  *GetModuleHandleA(const char *lpModuleName);
extern void   ExitProcess(unsigned int uExitCode);
#endif

/*
 * Minimal command-line parser for freestanding Windows.
 * Splits on spaces, handles simple double-quote grouping.
 * Not fully compatible with Windows quoting rules, but sufficient
 * for seed compiler usage.
 */
#define MAX_ARGS 256

static char *g_argv_storage[MAX_ARGS];
static int   g_argc = 0;

static void parse_cmdline(char *cmdline) {
    char *p = cmdline;
    g_argc = 0;

    while (*p && g_argc < MAX_ARGS - 1) {
        /* Skip whitespace */
        while (*p == ' ' || *p == '\t') p++;
        if (*p == '\0') break;

        if (*p == '"') {
            /* Quoted argument */
            p++;
            g_argv_storage[g_argc++] = p;
            while (*p && *p != '"') p++;
            if (*p == '"') *p++ = '\0';
        } else {
            /* Unquoted argument */
            g_argv_storage[g_argc++] = p;
            while (*p && *p != ' ' && *p != '\t') p++;
            if (*p) *p++ = '\0';
        }
    }
    g_argv_storage[g_argc] = (char *)0;
}

/*
 * Windows startup — called from ASM entry point.
 * Parses command line, then calls common __spl_start.
 */
void __spl_start_win(void) {
    char *cmdline = GetCommandLineA();
    parse_cmdline(cmdline);
    __spl_start(g_argc, g_argv_storage, (char **)0);
}

void __spl_exit(int status) {
    ExitProcess((unsigned int)status);
#ifdef __GNUC__
    __builtin_unreachable();
#else
    for (;;) {}
#endif
}
