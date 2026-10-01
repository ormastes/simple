/* Linux first-use SQLite bridge. Link this object instead of runtime_sqlite.c
 * or libsimple_sqlite_provider.so. The provider path and SHA-256 are required
 * at first use; no SQLite library is mapped by the executable loader. */
#if !defined(__linux__)
#error runtime_sqlite_demand.c currently requires Linux sealed snapshots
#endif

#include "runtime.h"
#include "runtime_sqlite_provider_abi_v1.h"
#include <dlfcn.h>
#include <sched.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

typedef int64_t RtValue;
enum { SQLITE_NIL = 3 };

typedef struct SqliteApi {
    RtValue (*open)(RtValue);
    RtValue (*open_memory)(void);
    RtValue (*close)(RtValue);
    RtValue (*execute)(RtValue, RtValue);
    RtValue (*execute_batch)(RtValue, RtValue);
    RtValue (*query)(RtValue, RtValue);
    RtValue (*query_next)(RtValue);
    void (*query_done)(RtValue);
    RtValue (*column_count)(RtValue);
    RtValue (*column_name)(RtValue, RtValue);
    RtValue (*column_text)(RtValue, RtValue);
    RtValue (*column_int)(RtValue, RtValue);
    double (*column_float)(RtValue, RtValue);
    RtValue (*column_type)(RtValue, RtValue);
    RtValue (*prepare)(RtValue, RtValue);
    RtValue (*bind_text)(RtValue, RtValue, RtValue);
    RtValue (*bind_int)(RtValue, RtValue, RtValue);
    RtValue (*bind_float)(RtValue, RtValue, double);
    RtValue (*bind_null)(RtValue, RtValue);
    RtValue (*reset)(RtValue);
    void (*finalize)(RtValue);
    RtValue (*begin)(RtValue);
    RtValue (*commit)(RtValue);
    RtValue (*rollback)(RtValue);
    RtValue (*last_insert_rowid)(RtValue);
    RtValue (*changes)(RtValue);
    RtValue (*error_message)(RtValue);
} SqliteApi;

/* 0 untouched, 1 loading, 2 ready, -1 permanently rejected. The provider
 * stays mapped while its connection and statement handles may be in use. */
static atomic_int sqlite_state = ATOMIC_VAR_INIT(0);
static SqliteApi sqlite_api;
static void *sqlite_handle;
static int sqlite_snapshot_fd = -1;

static int sqlite_digest_matches(const char *hex, const uint8_t digest[32]) {
    if (!hex || strlen(hex) != 64) return 0;
    for (int i = 0; i < 32; i++) {
        int hi = hex[i * 2], lo = hex[i * 2 + 1];
        hi = hi >= '0' && hi <= '9' ? hi - '0' :
            hi >= 'a' && hi <= 'f' ? hi - 'a' + 10 :
            hi >= 'A' && hi <= 'F' ? hi - 'A' + 10 : -1;
        lo = lo >= '0' && lo <= '9' ? lo - '0' :
            lo >= 'a' && lo <= 'f' ? lo - 'a' + 10 :
            lo >= 'A' && lo <= 'F' ? lo - 'A' + 10 : -1;
        if (hi < 0 || lo < 0 || digest[i] != (uint8_t)((hi << 4) | lo)) return 0;
    }
    return 1;
}

static int sqlite_load(void) {
    const char *path = getenv("SIMPLE_SQLITE_PROVIDER_PATH");
    const char *expected = getenv("SIMPLE_SQLITE_PROVIDER_SHA256");
    char snapshot_path[64];
    uint8_t digest[32];
    SqliteApi loaded = {0};
    void *handle = NULL;
    int fd = -1;
    if (!path || !path[0] || !expected || strlen(expected) != 64) return 0;
    /* The runtime snapshot copies a regular, no-follow file into a sealed
     * memfd. Hash and map that same immutable object. */
    fd = (int)spl_dynlib_snapshot_linux(rt_string_new(
        (const uint8_t *)path, (uint64_t)strlen(path)));
    if (fd < 0 || snprintf(snapshot_path, sizeof(snapshot_path),
            "/proc/self/fd/%d", fd) <= 0 ||
            !rt_sha256_file_raw_v1(snapshot_path, digest) ||
            !sqlite_digest_matches(expected, digest)) goto reject;
    handle = dlopen(snapshot_path, RTLD_NOW | RTLD_LOCAL);
    if (!handle) goto reject;
    int64_t (*abi)(void) = NULL;
    void *symbol = dlsym(handle, "spl_sqlite_provider_abi_version_v1");
    memcpy(&abi, &symbol, sizeof(abi));
    if (!abi || abi() != SIMPLE_SQLITE_PROVIDER_ABI_V1) goto reject;
    int64_t (*init)(const SimpleSqliteRuntimeApiV1 *) = NULL;
    symbol = dlsym(handle, "spl_sqlite_provider_init_v1");
    memcpy(&init, &symbol, sizeof(init));
    SimpleSqliteRuntimeApiV1 host_api = {
        .struct_size = sizeof(host_api),
        .abi_version = SIMPLE_SQLITE_PROVIDER_ABI_V1,
        .string_new = rt_string_new,
        .string_data = rt_string_data,
        .string_len = rt_string_len
    };
    if (!init || init(&host_api) != 1) goto reject;
#define LOAD(name) do { \
    symbol = dlsym(handle, "rt_sqlite_" #name); \
    if (!symbol) goto reject; \
    memcpy(&loaded.name, &symbol, sizeof(loaded.name)); \
} while (0)
    LOAD(open); LOAD(open_memory); LOAD(close); LOAD(execute);
    LOAD(execute_batch); LOAD(query); LOAD(query_next); LOAD(query_done);
    LOAD(column_count); LOAD(column_name); LOAD(column_text); LOAD(column_int);
    LOAD(column_float); LOAD(column_type); LOAD(prepare); LOAD(bind_text);
    LOAD(bind_int); LOAD(bind_float); LOAD(bind_null); LOAD(reset);
    LOAD(finalize); LOAD(begin); LOAD(commit); LOAD(rollback);
    LOAD(last_insert_rowid); LOAD(changes); LOAD(error_message);
#undef LOAD
    sqlite_api = loaded;
    sqlite_handle = handle;
    sqlite_snapshot_fd = fd;
    return 1;
reject:
    if (handle) dlclose(handle);
    if (fd >= 0) close(fd);
    return 0;
}

static int sqlite_ensure(void) {
    int expected = 0;
    if (atomic_compare_exchange_strong_explicit(&sqlite_state, &expected, 1,
            memory_order_acq_rel, memory_order_acquire)) {
        atomic_store_explicit(&sqlite_state, sqlite_load() ? 2 : -1,
            memory_order_release);
    }
    int state;
    while ((state = atomic_load_explicit(&sqlite_state,
            memory_order_acquire)) == 1) sched_yield();
    return state == 2;
}

int64_t spl_sqlite_demand_state(void) {
    return atomic_load_explicit(&sqlite_state, memory_order_acquire);
}

#define WRAP0(name, fallback) RtValue rt_sqlite_##name(void) { \
    return sqlite_ensure() ? sqlite_api.name() : (fallback); }
#define WRAP1(name, fallback) RtValue rt_sqlite_##name(RtValue a) { \
    return sqlite_ensure() ? sqlite_api.name(a) : (fallback); }
#define WRAP2(name, fallback) RtValue rt_sqlite_##name(RtValue a, RtValue b) { \
    return sqlite_ensure() ? sqlite_api.name(a, b) : (fallback); }
#define WRAP3(name, fallback) RtValue rt_sqlite_##name(RtValue a, RtValue b, RtValue c) { \
    return sqlite_ensure() ? sqlite_api.name(a, b, c) : (fallback); }
WRAP1(open, SQLITE_NIL)
WRAP0(open_memory, SQLITE_NIL)
WRAP1(close, 0)
WRAP2(execute, 0)
WRAP2(execute_batch, 0)
WRAP2(query, SQLITE_NIL)
WRAP1(query_next, 0)
void rt_sqlite_query_done(RtValue a) { if (sqlite_ensure()) sqlite_api.query_done(a); }
WRAP1(column_count, 0)
WRAP2(column_name, SQLITE_NIL)
WRAP2(column_text, SQLITE_NIL)
WRAP2(column_int, 0)
double rt_sqlite_column_float(RtValue a, RtValue b) {
    return sqlite_ensure() ? sqlite_api.column_float(a, b) : 0.0;
}
WRAP2(column_type, SQLITE_NIL)
WRAP2(prepare, SQLITE_NIL)
WRAP3(bind_text, 0)
WRAP3(bind_int, 0)
RtValue rt_sqlite_bind_float(RtValue a, RtValue b, double c) {
    return sqlite_ensure() ? sqlite_api.bind_float(a, b, c) : 0;
}
WRAP2(bind_null, 0)
WRAP1(reset, 0)
void rt_sqlite_finalize(RtValue a) { if (sqlite_ensure()) sqlite_api.finalize(a); }
WRAP1(begin, 0)
WRAP1(commit, 0)
WRAP1(rollback, 0)
WRAP1(last_insert_rowid, 0)
WRAP1(changes, 0)
WRAP1(error_message, SQLITE_NIL)
