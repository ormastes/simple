#ifndef SIMPLE_WINDOWS_COMMAND_LINE_PRIVATE_H
#define SIMPLE_WINDOWS_COMMAND_LINE_PRIVATE_H

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

static bool win_cmd_needs_quotes(const char* s) {
    if (!s || s[0] == '\0') return true;
    for (const char* p = s; *p; p++) {
        if (*p == ' ' || *p == '\t' || *p == '"') return true;
    }
    return false;
}

static bool win_cmd_append_char(char* out, size_t cap, size_t* pos, char ch) {
    if (*pos + 1 >= cap) return false;
    out[*pos] = ch;
    (*pos)++;
    out[*pos] = '\0';
    return true;
}

static bool win_cmd_append_str(char* out, size_t cap, size_t* pos, const char* s) {
    if (!s) return true;
    while (*s) {
        if (!win_cmd_append_char(out, cap, pos, *s)) return false;
        s++;
    }
    return true;
}

static bool win_cmd_append_arg(char* out, size_t cap, size_t* pos, const char* arg) {
    const char* s = arg ? arg : "";
    if (!win_cmd_needs_quotes(s)) {
        return win_cmd_append_str(out, cap, pos, s);
    }

    if (!win_cmd_append_char(out, cap, pos, '"')) return false;
    size_t backslashes = 0;
    for (const char* p = s; *p; p++) {
        if (*p == '\\') {
            backslashes++;
            continue;
        }
        if (*p == '"') {
            for (size_t i = 0; i < backslashes * 2 + 1; i++) {
                if (!win_cmd_append_char(out, cap, pos, '\\')) return false;
            }
            backslashes = 0;
            if (!win_cmd_append_char(out, cap, pos, '"')) return false;
            continue;
        }
        for (size_t i = 0; i < backslashes; i++) {
            if (!win_cmd_append_char(out, cap, pos, '\\')) return false;
        }
        backslashes = 0;
        if (!win_cmd_append_char(out, cap, pos, *p)) return false;
    }
    for (size_t i = 0; i < backslashes * 2; i++) {
        if (!win_cmd_append_char(out, cap, pos, '\\')) return false;
    }
    return win_cmd_append_char(out, cap, pos, '"');
}

/* cmd.exe does NOT parse its command line with CommandLineToArgvW rules: it
 * never honours a backslash-escaped quote. So the argv quoter above corrupts
 * every shell string that contains a `"` (the normal case as soon as a path has
 * a space) -- cmd then prints "The filename, directory name, or volume label
 * syntax is incorrect" and exits 1 without running anything. See
 * doc/08_tracking/bug/windows_cmd_shell_string_mangled_by_argv_quoting_2026-09-02.md
 *
 * The documented cmd.exe contract for handing it a verbatim shell string is
 * `/S`: with /S, cmd strips exactly the first and last quote after /C (or /K)
 * and preserves everything between them byte-for-byte. That is applied here,
 * once, at the single boundary every Windows spawn goes through, so no caller
 * has to know about it.
 *
 * Deliberately NARROW. It fires only for a payload that actually contains a
 * quote -- i.e. exactly the set of strings that are mangled today. A quote-free
 * payload with spaces (`cmd /c "C:\p ath\run.bat"`) works today via cmd's
 * two-quote heuristic, and /S would DISABLE that heuristic and break it, so
 * such payloads keep the legacy path. */
static bool win_cmd_is_cmd_exe(const char* cmd) {
    const char* base = cmd;
    for (const char* p = cmd; *p; p++) {
        if (*p == '\\' || *p == '/') base = p + 1;
    }
    static const char* const names[2] = {"cmd", "cmd.exe"};
    for (int k = 0; k < 2; k++) {
        const char* w = names[k];
        const char* b = base;
        while (*w && *b) {
            char cb = (*b >= 'A' && *b <= 'Z') ? (char)(*b - 'A' + 'a') : *b;
            if (cb != *w) break;
            w++;
            b++;
        }
        if (*w == '\0' && *b == '\0') return true;
    }
    return false;
}

static bool win_cmd_is_shell_switch(const char* a) {
    return a && (a[0] == '/' || a[0] == '-') &&
           (a[1] == 'c' || a[1] == 'C' || a[1] == 'k' || a[1] == 'K') && a[2] == '\0';
}

/* Verbatim /S passthrough is safe only for a single-line payload. A CR or LF
 * would truncate the command line at the child and silently drop (or, worse,
 * re-interpret) the remainder, so such a payload is REJECTED rather than
 * quoted -- fail closed at a shell boundary, never guess. */
static bool win_cmd_shell_payload_needs_verbatim(const char* s) {
    return s != NULL && strchr(s, '"') != NULL;
}

static bool win_cmd_shell_payload_single_line(const char* s) {
    return strchr(s, '\n') == NULL && strchr(s, '\r') == NULL;
}

static char* win_cmd_build_shell_line(const char* cmd, const char* sw, const char* payload) {
    size_t total = strlen(cmd) + strlen(sw) + strlen(payload) + 16;
    char* out = (char*)malloc(total);
    if (!out) return NULL;
    out[0] = '\0';
    size_t pos = 0;
    if (!win_cmd_append_arg(out, total, &pos, cmd) ||
        !win_cmd_append_str(out, total, &pos, " /S ") ||
        !win_cmd_append_str(out, total, &pos, sw) ||
        !win_cmd_append_str(out, total, &pos, " \"") ||
        !win_cmd_append_str(out, total, &pos, payload) ||
        !win_cmd_append_char(out, total, &pos, '"')) {
        free(out);
        return NULL;
    }
    return out;
}

static char* win_cmd_build_line(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd || arg_count < 0) return NULL;

    if (arg_count == 2 && args && win_cmd_is_cmd_exe(cmd) &&
        win_cmd_is_shell_switch(args[0]) &&
        win_cmd_shell_payload_needs_verbatim(args[1])) {
        /* Fail closed: a multi-line shell payload cannot be represented on a
         * Windows command line at all. Returning NULL surfaces as a spawn
         * failure; silently truncating it at the CR would run a PREFIX of what
         * the caller asked for, which at a shell boundary is the dangerous
         * outcome. */
        if (!win_cmd_shell_payload_single_line(args[1])) return NULL;
        return win_cmd_build_shell_line(cmd, args[0], args[1]);
    }

    size_t cmd_len = strlen(cmd);
    if (cmd_len > (SIZE_MAX - 4) / 2) return NULL;
    size_t total = (cmd_len * 2) + 4;
    for (int64_t i = 0; i < arg_count; i++) {
        const char* a = args ? args[i] : "";
        size_t arg_len = strlen(a ? a : "");
        if (arg_len > (SIZE_MAX - 4) / 2) return NULL;
        size_t addition = (arg_len * 2) + 4;
        if (total > SIZE_MAX - addition) return NULL;
        total += addition;
    }

    char* cmdline = (char*)malloc(total);
    if (!cmdline) return NULL;
    cmdline[0] = '\0';
    size_t pos = 0;

    if (!win_cmd_append_arg(cmdline, total, &pos, cmd)) {
        free(cmdline);
        return NULL;
    }
    for (int64_t i = 0; i < arg_count; i++) {
        if (!win_cmd_append_char(cmdline, total, &pos, ' ')) {
            free(cmdline);
            return NULL;
        }
        if (!win_cmd_append_arg(cmdline, total, &pos, args ? args[i] : "")) {
            free(cmdline);
            return NULL;
        }
    }
    return cmdline;
}

#endif
