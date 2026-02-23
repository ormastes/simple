/* simple_helpers.h - Shared types and utilities for generated C code */
#ifndef SIMPLE_HELPERS_H
#define SIMPLE_HELPERS_H

#include <stdlib.h>
#include <string.h>
#include <stdio.h>

/* ── String helpers ── */
static int simple_starts_with(const char* s, const char* p) {
    if (!s || !p) return 0;
    return strncmp(s, p, strlen(p)) == 0;
}
static int simple_ends_with(const char* s, const char* x) {
    if (!s || !x) return 0;
    size_t sl = strlen(s), xl = strlen(x);
    return sl >= xl && strcmp(s + sl - xl, x) == 0;
}
static int simple_contains(const char* s, const char* n) {
    if (!s || !n) return 0;
    return strstr(s, n) != NULL;
}
static char* simple_str_concat(const char* a, const char* b) {
    size_t la = a ? strlen(a) : 0, lb = b ? strlen(b) : 0;
    char* r = (char*)malloc(la + lb + 1);
    if (a) memcpy(r, a, la);
    if (b) memcpy(r + la, b, lb);
    r[la + lb] = 0;
    return r;
}

/* ── Dynamic string array ── */
typedef struct { const char** items; long long len; long long cap; } SimpleStringArray;

static SimpleStringArray simple_new_string_array(void) {
    SimpleStringArray a;
    a.items = (const char**)malloc(16 * sizeof(const char*));
    a.len = 0;
    a.cap = 16;
    return a;
}
static void simple_string_push(SimpleStringArray* a, const char* s) {
    if (a->len >= a->cap) {
        a->cap *= 2;
        a->items = (const char**)realloc(a->items, a->cap * sizeof(const char*));
    }
    a->items[a->len++] = strdup(s ? s : "");
}
static void simple_string_array_free(SimpleStringArray* a) {
    if (a->items) {
        for (long long i = 0; i < a->len; i++)
            free((void*)a->items[i]);
        free(a->items);
        a->items = NULL;
        a->len = 0;
        a->cap = 0;
    }
}
static SimpleStringArray simple_string_array_slice(SimpleStringArray a, long long start) {
    SimpleStringArray r = simple_new_string_array();
    for (long long i = start; i < a.len; i++)
        simple_string_push(&r, a.items[i]);
    return r;
}

/* ── Dynamic int array ── */
typedef struct { long long* items; long long len; long long cap; } SimpleIntArray;

static SimpleIntArray simple_new_int_array(void) {
    SimpleIntArray a;
    a.items = (long long*)malloc(16 * sizeof(long long));
    a.len = 0;
    a.cap = 16;
    return a;
}
static void simple_int_push(SimpleIntArray* a, long long v) {
    if (a->len >= a->cap) {
        a->cap *= 2;
        a->items = (long long*)realloc(a->items, a->cap * sizeof(long long));
    }
    a->items[a->len++] = v;
}

/* ── Formatting helpers ── */
static char* simple_format_long(const char* b, long long v, const char* a) {
    char buf[256];
    snprintf(buf, 256, "%s%lld%s", b ? b : "", v, a ? a : "");
    return strdup(buf);
}
static char* simple_format_str(const char* b, const char* v, const char* a) {
    size_t t = strlen(b ? b : "") + strlen(v ? v : "") + strlen(a ? a : "") + 1;
    char* r = (char*)malloc(t);
    snprintf(r, t, "%s%s%s", b ? b : "", v ? v : "", a ? a : "");
    return r;
}
static char* simple_int_to_str(long long v) {
    char b[32];
    snprintf(b, 32, "%lld", v);
    return strdup(b);
}
static const char* simple_substr_from(const char* s, long long start) {
    if (!s) return "";
    long long l = (long long)strlen(s);
    if (start >= l) return "";
    return strdup(s + start);
}

#endif /* SIMPLE_HELPERS_H */
