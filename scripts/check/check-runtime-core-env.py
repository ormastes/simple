#!/usr/bin/env python3
"""Compile real core env consumers with effect-boundary fixtures on MSVC."""
import argparse
from pathlib import Path
import subprocess
ap = argparse.ArgumentParser()
ap.add_argument('--cc', required=True)
ap.add_argument('--output', required=True)
ap.add_argument('--negative-only', action='store_true')
a = ap.parse_args()
root = Path(__file__).resolve().parents[2]
out = Path(a.output).resolve()
out.mkdir(parents=True, exist_ok=True)
def extract(unit, signature):
    text = (root / 'src/runtime' / unit).read_text()
    start = text.index(signature)
    end = text.index('{', start) + 1
    depth = 1
    while depth:
        depth += (text[end] == '{') - (text[end] == '}')
        end += 1
    return text[start:end]
pre = r"""
#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
static int fail_snapshot;
static errno_t fixture_dupenv(char** out, size_t* n, const char* key) {
    if (fail_snapshot) { *out = NULL; *n = 0; return ENOMEM; }
    return _dupenv_s(out, n, key);
}
#define _dupenv_s fixture_dupenv
#include "runtime_env_owned.h"
#undef _dupenv_s
static int g_slice_audit_level = -1;
static int g_text_status, provider_calls;
#define SIMD_TEXT_PROVIDER_LOAD_FAILED 8
static void simd_text_provider_admit_values(const char* path, const char* pin) {
    assert(path && pin && !strcmp(path, "fixture.dll") && !strcmp(pin, "pinned"));
    assert(_putenv_s("SIMPLE_VECTOR_PROVIDER_PATH", "mutated") == 0);
    assert(_putenv_s("SIMPLE_VECTOR_PROVIDER_SHA256", "changed") == 0);
    assert(!strcmp(path, "fixture.dll") && !strcmp(pin, "pinned"));
    provider_calls++;
}
static char record[10000];
static int appended;
static int rt_mem_snapshot_append_flush_raw(int64_t fd, const char* p, int64_t n) {
    assert(fd == 1 && n < sizeof(record)); memcpy(record, p, (size_t)n);
    record[n] = 0; appended++; return 1;
}
static int rt_group_self_charge_snapshot(int64_t* c, int64_t* p) { (void)c; (void)p; return 0; }
static int64_t rt_getpid(void) { return 42; }
static int64_t rt_time_now_monotonic_ms(void) { return 100; }
static int64_t rt_heap_live_bytes(void) { return 0; }
static int64_t rt_heap_peak_bytes(void) { return 0; }
static int64_t rt_process_rss_kib(void) { return 0; }
static int64_t rt_process_hwm_kib(void) { return 0; }
"""
functions = '\n'.join(extract(unit, signature) for unit, signature in [
    ('runtime_coverage_core.c', 'bool rt_coverage_enabled(void)'),
    ('runtime_memory.c', 'static int rt_mem_harden_enabled(void)'),
    ('runtime_simd_utf8.c', 'int64_t rt_text_slice_audit_level(void)'),
    ('runtime_simd_utf8.c', 'static void simd_text_provider_admit(void)'),
    ('runtime_legacy_core.c', 'static int rt_mem_snapshot_token('),
    ('runtime_legacy_core.c', 'int rt_mem_snapshot_record('),
])
legacy = (root / 'src/runtime/runtime_legacy_core.c').read_text()
functions += legacy[legacy.index('/* BEGIN borrowed-env-compat'):legacy.index('/* END borrowed-env-compat */')]
main = r"""
static int snapshot_record(void) {
    return rt_mem_snapshot_record(1, 5, "event", 5, "phase", 5, 0, "path", 4,
        0,0,0,0,0,0,0,0,0,0,0);
}
int main(void) {
    assert(_putenv_s("SIMPLE_COVERAGE", "") == 0); assert(!rt_coverage_enabled());
    assert(_putenv_s("SIMPLE_COVERAGE", "1") == 0); assert(rt_coverage_enabled());
    assert(_putenv_s("SIMPLE_COVERAGE", "11") == 0); assert(!rt_coverage_enabled());
    assert(_putenv_s("SIMPLE_COVERAGE", " 1") == 0); assert(!rt_coverage_enabled());
    assert(_putenv_s("SIMPLE_MEM_HARDEN", "1") == 0); assert(rt_mem_harden_enabled());
    assert(_putenv_s("SIMPLE_MEM_HARDEN", "0") == 0); assert(rt_mem_harden_enabled());
    assert(_putenv_s("SIMPLE_UTF8_SLICE_AUDIT", "2") == 0); assert(rt_text_slice_audit_level() == 2);
    assert(_putenv_s("SIMPLE_UTF8_SLICE_AUDIT", "1") == 0); assert(rt_text_slice_audit_level() == 2);
    g_slice_audit_level = -1; assert(rt_text_slice_audit_level() == 1);
    g_slice_audit_level = -1;
    assert(_putenv_s("SIMPLE_UTF8_SLICE_AUDIT", "20") == 0); assert(rt_text_slice_audit_level() == 0);
    assert(_putenv_s("SIMPLE_VECTOR_PROVIDER_PATH", "fixture.dll") == 0);
    assert(_putenv_s("SIMPLE_VECTOR_PROVIDER_SHA256", "pinned") == 0);
    simd_text_provider_admit(); assert(provider_calls == 1);
    fail_snapshot = 1;
    simd_text_provider_admit(); assert(provider_calls == 1 && g_text_status == SIMD_TEXT_PROVIDER_LOAD_FAILED);
    assert(!snapshot_record() && !appended);
    fail_snapshot = 0;
    assert(_putenv_s("SIMPLE_EVIDENCE_RUN_ID", "a b=c%") == 0);
    assert(snapshot_record() && strstr(record, "run_id=a%20b%3Dc%25 seq=5"));
    assert(_putenv_s("SIMPLE_EVIDENCE_RUN_ID", "") == 0);
    assert(snapshot_record() && strstr(record, "run_id=none seq=5"));
    assert(_putenv_s("Simple_Borrow_Fixture", "first") == 0);
    assert(!strcmp(spl_env_get("sIMPLE_bORROW_fIXTURE"), "first"));
    const char* held = spl_env_get("Simple_Borrow_Fixture");
    assert(!strcmp(spl_env_get("PATH"), spl_env_get("Path")));
    assert(!strcmp(held, "first")); /* Other lookups don't replace borrowed storage. */
    assert(!strcmp(spl_env_get("Simple_Borrow_Fixtur"), ""));
    assert(!strcmp(spl_env_get("missing-fixture"), ""));
    assert(!strcmp(spl_env_get(NULL), "") && !strcmp(spl_env_get(""), ""));
    assert(_putenv_s("Simple_Borrow_Fixture", "second") == 0);
    assert(!strcmp(spl_env_get("Simple_Borrow_Fixture"), "second"));
    assert(_putenv_s("Simple_Borrow_Fixture", "") == 0);
    assert(!strcmp(spl_env_get("Simple_Borrow_Fixture"), ""));
    puts("production core environment consumers: PASS");
    return 0;
}
"""
f = out / 'core-env.c'
f.write_text(pre + functions + main)
exe = out / 'core-env.exe'
if not a.negative_only:
    subprocess.run([a.cc, '/nologo', '/WX', '/std:c11', '/I' + str(root / 'src/runtime'),
    str(f), '/Fo' + str(out/'core-env.obj'), '/Fe' + str(exe)], check=True)
    subprocess.run([str(exe)], check=True)

# Wide startup initializes only the wide CRT environment. The first public
# borrowed lookup must retain getenv's lazy creation of the narrow environment.
wide = out / 'core-env-wide.c'
wide.write_text(r"""
#include <assert.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
""" + legacy[legacy.index('/* BEGIN borrowed-env-compat'):legacy.index('/* END borrowed-env-compat */')] + r"""
int wmain(void) {
    char** entries = NULL;
    entries = *__p__environ(); assert(!entries);
    const char* value = spl_env_get("SIMPLE_BORROW_WIDE_FIXTURE");
    assert(!strcmp(value, "from-parent"));
    entries = *__p__environ(); assert(entries);
    int found = 0;
    for (char** entry = entries; *entry; ++entry) {
        const char* separator = strchr(*entry, '=');
        if (separator && !strcmp(separator + 1, "from-parent") && separator + 1 == value) found = 1;
    }
    assert(found); /* The public pointer is the CRT's storage, not a copy. */
    puts("borrowed environment wide startup and pointer identity: PASS");
    return 0;
}
""")
wide_exe = out / 'core-env-wide.exe'
if not a.negative_only:
    subprocess.run([a.cc, '/nologo', '/WX', '/std:c11', str(wide),
    '/Fo' + str(out/'core-env-wide.obj'), '/Fe' + str(wide_exe)], check=True)
import os
wide_env = dict(os.environ, SIMPLE_BORROW_WIDE_FIXTURE='from-parent')
if not a.negative_only:
    subprocess.run([str(wide_exe)], check=True, env=wide_env)

# A deprecated call immediately after the scoped compatibility section must
# still fail /WX: the public borrowed ABI exception cannot mask other calls.
negative = out / 'env-warning-negative.c'
negative.write_text('#include <stdlib.h>\n' + legacy[legacy.index('/* BEGIN borrowed-env-compat'):legacy.index('/* END borrowed-env-compat */')] + '\nconst char* outside_scope(void) { return getenv("PATH"); }\n')
check = subprocess.run([a.cc, '/nologo', '/WX', '/c', str(negative),
    '/Fo' + str(out/'env-warning-negative.obj')], capture_output=True, text=True)
(out/'env-warning-negative.log').write_text(check.stdout + check.stderr)
assert check.returncode != 0 and "'getenv' is deprecated" in check.stderr, check.stderr
print('borrowed exception warning scope negative control: PASS')
