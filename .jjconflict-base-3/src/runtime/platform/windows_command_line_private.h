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

static char* win_cmd_build_line(const char* cmd, const char** args, int64_t arg_count) {
    if (!cmd || arg_count < 0) return NULL;

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
