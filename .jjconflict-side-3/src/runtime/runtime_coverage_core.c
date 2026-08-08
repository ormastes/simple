/* Minimal decision/condition coverage owner for the core-c-bootstrap bundle. */
#ifdef _WIN32
#include <windows.h>
#else
#include <pthread.h>
#endif
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    uint32_t decision_id;
    uint32_t condition_id;
    char *file;
    uint32_t line;
    uint32_t column;
    uint64_t true_count;
    uint64_t false_count;
} CoverageRow;

static CoverageRow *g_decisions;
static size_t g_decision_count;
static CoverageRow *g_conditions;
static size_t g_condition_count;

#ifdef _WIN32
static INIT_ONCE g_coverage_lock_once = INIT_ONCE_STATIC_INIT;
static CRITICAL_SECTION g_coverage_lock;
static BOOL CALLBACK coverage_init_lock(PINIT_ONCE once, PVOID parameter, PVOID *context) {
    (void)once; (void)parameter; (void)context;
    InitializeCriticalSection(&g_coverage_lock);
    return TRUE;
}
static void coverage_lock(void) {
    if (!InitOnceExecuteOnce(&g_coverage_lock_once, coverage_init_lock, NULL, NULL)) abort();
    EnterCriticalSection(&g_coverage_lock);
}
static void coverage_unlock(void) { LeaveCriticalSection(&g_coverage_lock); }
#else
static pthread_mutex_t g_coverage_lock = PTHREAD_MUTEX_INITIALIZER;
static void coverage_lock(void) { if (pthread_mutex_lock(&g_coverage_lock) != 0) abort(); }
static void coverage_unlock(void) { if (pthread_mutex_unlock(&g_coverage_lock) != 0) abort(); }
#endif

static bool coverage_add_size(size_t a, size_t b, size_t *result) {
    if (a > SIZE_MAX - b) return false;
    *result = a + b;
    return true;
}

static bool coverage_mul_size(size_t a, size_t b, size_t *result) {
    if (a && b > SIZE_MAX / a) return false;
    *result = a * b;
    return true;
}

static char *coverage_file_copy(const char *file) {
    const char *source = file ? file : "";
    size_t size;
    if (!coverage_add_size(strlen(source), 1, &size)) abort();
    char *copy = (char *)malloc(size);
    if (copy) memcpy(copy, source, size);
    return copy;
}

static size_t coverage_escaped_file_size(const char *file) {
    size_t size = 0;
    for (const unsigned char *p = (const unsigned char *)file; *p; ++p) {
        size_t width = (*p == '%' || *p == ',' || *p == '\r' || *p == '\n') ? 3u : 1u;
        if (!coverage_add_size(size, width, &size)) abort();
    }
    return size;
}

static size_t coverage_write_escaped_file(char *out, const char *file) {
    char *start = out;
    for (const unsigned char *p = (const unsigned char *)file; *p; ++p) {
        const char *escape = NULL;
        if (*p == '%') escape = "%25";
        else if (*p == ',') escape = "%2C";
        else if (*p == '\r' || *p == '\n') escape = "%0A";
        if (escape) { memcpy(out, escape, 3); out += 3; }
        else *out++ = (char)*p;
    }
    return (size_t)(out - start);
}

static void coverage_record(CoverageRow **rows, size_t *count, uint32_t decision_id,
                            uint32_t condition_id, bool result, const char *file,
                            uint32_t line, uint32_t column) {
    char *file_copy = coverage_file_copy(file);
    if (!file_copy) abort();
    coverage_lock();
    for (size_t i = 0; i < *count; ++i) {
        CoverageRow *row = &(*rows)[i];
        if (row->decision_id == decision_id && row->condition_id == condition_id &&
            row->line == line && row->column == column && strcmp(row->file, file_copy) == 0) {
            uint64_t *counter = result ? &row->true_count : &row->false_count;
            if (*counter != UINT64_MAX) ++*counter;
            coverage_unlock();
            free(file_copy);
            return;
        }
    }
    size_t next_count;
    size_t bytes;
    if (!coverage_add_size(*count, 1, &next_count) ||
        !coverage_mul_size(next_count, sizeof(**rows), &bytes)) {
        coverage_unlock(); free(file_copy); abort();
    }
    CoverageRow *grown = (CoverageRow *)realloc(*rows, bytes);
    if (!grown) { coverage_unlock(); free(file_copy); abort(); }
    *rows = grown;
    (*rows)[*count] = (CoverageRow){decision_id, condition_id, file_copy, line, column,
                                   result ? 1u : 0u, result ? 0u : 1u};
    *count = next_count;
    coverage_unlock();
}

bool rt_coverage_enabled(void) {
    const char *value = getenv("SIMPLE_COVERAGE");
    return value && strcmp(value, "1") == 0;
}

void rt_coverage_decision_probe(uint32_t decision_id, bool result, const char *file,
                                uint32_t line, uint32_t column) {
    if (rt_coverage_enabled()) coverage_record(&g_decisions, &g_decision_count, decision_id, 0, result, file, line, column);
}

void rt_coverage_condition_probe(uint32_t decision_id, uint32_t condition_id, bool result,
                                 const char *file, uint32_t line, uint32_t column) {
    if (rt_coverage_enabled()) coverage_record(&g_conditions, &g_condition_count, decision_id, condition_id, result, file, line, column);
}

static int coverage_row_compare(const void *left, const void *right) {
    const CoverageRow *a = *(const CoverageRow * const *)left;
    const CoverageRow *b = *(const CoverageRow * const *)right;
    if (a->decision_id != b->decision_id) return a->decision_id < b->decision_id ? -1 : 1;
    if (a->condition_id != b->condition_id) return a->condition_id < b->condition_id ? -1 : 1;
    int file_order = strcmp(a->file, b->file);
    if (file_order) return file_order;
    if (a->line != b->line) return a->line < b->line ? -1 : 1;
    if (a->column != b->column) return a->column < b->column ? -1 : 1;
    return 0;
}

static void coverage_require_capacity(size_t *capacity, size_t addition) {
    if (!coverage_add_size(*capacity, addition, capacity)) abort();
}

static void coverage_append(char *out, size_t capacity, size_t *offset, const char *text) {
    size_t length = strlen(text);
    if (*offset > capacity || length > capacity - *offset) abort();
    memcpy(out + *offset, text, length);
    *offset += length;
}

char *rt_coverage_dump_sdn(void) {
    static const char decision_header[] = "# Coverage Report\nversion: 1.0\n\ndecisions |id, file, line, column, true_count, false_count|\n";
    static const char condition_header[] = "\nconditions |decision_id, condition_id, file, line, column, true_count, false_count|\n";
    coverage_lock();
    size_t capacity = sizeof(decision_header) - 1;
    coverage_require_capacity(&capacity, sizeof(condition_header) - 1);
    for (size_t i = 0; i < g_decision_count; ++i) {
        coverage_require_capacity(&capacity, coverage_escaped_file_size(g_decisions[i].file));
        coverage_require_capacity(&capacity, 96);
    }
    for (size_t i = 0; i < g_condition_count; ++i) {
        coverage_require_capacity(&capacity, coverage_escaped_file_size(g_conditions[i].file));
        coverage_require_capacity(&capacity, 112);
    }
    coverage_require_capacity(&capacity, 1);
    size_t decision_bytes;
    size_t condition_bytes;
    if (!coverage_mul_size(g_decision_count, sizeof(CoverageRow *), &decision_bytes) ||
        !coverage_mul_size(g_condition_count, sizeof(CoverageRow *), &condition_bytes)) {
        coverage_unlock(); abort();
    }
    char *out = (char *)malloc(capacity);
    CoverageRow **decisions = decision_bytes ? (CoverageRow **)malloc(decision_bytes) : NULL;
    CoverageRow **conditions = condition_bytes ? (CoverageRow **)malloc(condition_bytes) : NULL;
    if (!out || (decision_bytes && !decisions) || (condition_bytes && !conditions)) {
        free(out); free(decisions); free(conditions); coverage_unlock(); abort();
    }
    for (size_t i = 0; i < g_decision_count; ++i) decisions[i] = &g_decisions[i];
    for (size_t i = 0; i < g_condition_count; ++i) conditions[i] = &g_conditions[i];
    if (g_decision_count > 1) qsort(decisions, g_decision_count, sizeof(*decisions), coverage_row_compare);
    if (g_condition_count > 1) qsort(conditions, g_condition_count, sizeof(*conditions), coverage_row_compare);
    size_t offset = 0;
    coverage_append(out, capacity, &offset, decision_header);
    for (size_t i = 0; i < g_decision_count; ++i) {
        const CoverageRow *row = decisions[i];
        int written = snprintf(out + offset, capacity - offset, "    %u, ", row->decision_id);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
        offset += coverage_write_escaped_file(out + offset, row->file);
        written = snprintf(out + offset, capacity - offset, ", %u, %u, %llu, %llu\n", row->line, row->column,
                           (unsigned long long)row->true_count, (unsigned long long)row->false_count);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
    }
    coverage_append(out, capacity, &offset, condition_header);
    for (size_t i = 0; i < g_condition_count; ++i) {
        const CoverageRow *row = conditions[i];
        int written = snprintf(out + offset, capacity - offset, "    %u, %u, ", row->decision_id, row->condition_id);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
        offset += coverage_write_escaped_file(out + offset, row->file);
        written = snprintf(out + offset, capacity - offset, ", %u, %u, %llu, %llu\n", row->line, row->column,
                           (unsigned long long)row->true_count, (unsigned long long)row->false_count);
        if (written < 0 || (size_t)written >= capacity - offset) abort();
        offset += (size_t)written;
    }
    out[offset] = '\0';
    free(decisions); free(conditions); coverage_unlock();
    return out;
}

void rt_coverage_free_sdn(char *report) { free(report); }

void rt_coverage_clear(void) {
    coverage_lock();
    for (size_t i = 0; i < g_decision_count; ++i) free(g_decisions[i].file);
    for (size_t i = 0; i < g_condition_count; ++i) free(g_conditions[i].file);
    free(g_decisions); free(g_conditions);
    g_decisions = NULL; g_conditions = NULL;
    g_decision_count = 0; g_condition_count = 0;
    coverage_unlock();
}
