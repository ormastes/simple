#!/usr/bin/env python3
"""Compile production env consumers with tiny ABI adapters, then execute them.
Run in the configured MSVC developer environment; --cc selects pinned clang-cl.
"""
import argparse
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--cc", required=True)
parser.add_argument("--output", required=True)
args = parser.parse_args()
root = Path(__file__).resolve().parents[2]
out = Path(args.output).resolve()
out.mkdir(parents=True, exist_ok=True)
source = (root / "src/runtime/runtime_native.c").read_text()
def function(signature):
    start = source.index(signature)
    body = source.index("{", start)
    depth = 1
    end = body + 1
    while depth:
        depth += (source[end] == "{") - (source[end] == "}")
        end += 1
    return source[start:end]
prefix = r'''
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <errno.h>
static int snapshot_mode, injected_freed;
static void* injected;
static errno_t fixture_dupenv(char** value, size_t* length, const char* key) {
    if (snapshot_mode == 1) { *value = NULL; *length = 0; return ENOMEM; }
    if (snapshot_mode == 2 || snapshot_mode == 3) {
        *value = malloc(1); assert(*value); (*value)[0] = 0;
        *length = 1; injected = *value;
        return snapshot_mode == 3 ? ENOMEM : 0;
    }
    return _dupenv_s(value, length, key);
}
static void fixture_free(void* p) {
    if (p && p == injected) { injected_freed++; injected = NULL; }
    free(p);
}
#define _dupenv_s fixture_dupenv
#define free fixture_free
#include "runtime_env_owned.h"
#undef free
#undef _dupenv_s
#define SIMPLE_STARTUP_ASPECT_ENV "SIMPLE_STARTUP_FIXTURE"
#define SIMPLE_STARTUP_ASPECT_SEP ';'
static int load_count, fail_load, fail_path_alloc;
static char loaded[4][40];
static void* rt_observed_malloc_v1(size_t n) {
    return fail_path_alloc ? NULL : malloc(n);
}
static int simple_startup_load_aspect_pack(const char* path) {
    assert(load_count < 4 && strlen(path) < sizeof(loaded[0]));
    memcpy(loaded[load_count], path, strlen(path) + 1); load_count++;
    /* Simulate a real plugin callback mutating the source environment. */
    assert(_putenv_s(SIMPLE_STARTUP_ASPECT_ENV, "mutated") == 0);
    return fail_load;
}
static char captured[4096];
static int64_t rt_core_nil(void) { return 3; }
static int64_t rt_string_new(const uint8_t* p, uint64_t n) {
    assert(n < sizeof(captured)); memcpy(captured, p, (size_t)n);
    captured[n] = 0; return 77;
}
static char* rt_core_text_arg_to_cstr(const uint8_t* p, uint64_t n) {
    if (!p) return NULL;
    char* copy = malloc((size_t)n + 1); assert(copy);
    memcpy(copy, p, (size_t)n); copy[n] = 0; return copy;
}
'''
functions = "\n".join(function(s) for s in [
    "int64_t rt_env_get_i64(", "int64_t rt_env_home(void)",
    "int64_t rt_env_temp(void)",
    "static int simple_startup_load_aspect_spec(",
    "int __simple_startup_before_main("])
main = r'''
int main(void) {
    assert(_putenv_s("SIMPLE_ENV_FIXTURE", "") == 0);
    assert(!rt_env_owned("SIMPLE_ENV_FIXTURE"));
    assert(!rt_env_present("SIMPLE_ENV_FIXTURE"));
    assert(_putenv_s("SIMPLE_ENV_FIXTURE", "before") == 0);
    char* held = rt_env_owned("SIMPLE_ENV_FIXTURE");
    assert(held && strcmp(held, "before") == 0);
    assert(_putenv_s("SIMPLE_ENV_FIXTURE", "after") == 0);
    assert(strcmp(held, "before") == 0); free(held);
    const uint8_t* key = (const uint8_t*)"SIMPLE_ENV_FIXTURE";
    assert(rt_env_get_i64(key, 18, 41) == 41);
    assert(_putenv_s("SIMPLE_ENV_FIXTURE", " -27tail") == 0);
    assert(rt_env_get_i64(key, 18, 41) == -27);
    assert(_putenv_s("SIMPLE_ENV_FIXTURE", "") == 0);
    assert(rt_env_get_i64(key, 18, 41) == 41);
    assert(rt_env_get_i64(NULL, 0, 41) == 41);
    assert(_putenv_s("HOME", "") == 0);
    assert(_putenv_s("USERPROFILE", "profile") == 0);
    assert(rt_env_home() == 77 && strcmp(captured, "profile") == 0);
    assert(_putenv_s("HOME", "home") == 0);
    assert(rt_env_home() == 77 && strcmp(captured, "home") == 0);
    assert(_putenv_s("HOME", "") == 0);
    assert(_putenv_s("USERPROFILE", "") == 0);
    assert(rt_env_home() == 3);
    assert(_putenv_s("TMPDIR", "first") == 0);
    assert(_putenv_s("TMP", "second") == 0);
    assert(_putenv_s("TEMP", "third") == 0);
    assert(rt_env_temp() == 77 && strcmp(captured, "first") == 0);
    assert(_putenv_s("TMPDIR", "") == 0);
    assert(rt_env_temp() == 77 && strcmp(captured, "second") == 0);
    assert(_putenv_s("TMP", "") == 0);
    assert(rt_env_temp() == 77 && strcmp(captured, "third") == 0);
    assert(_putenv_s("TEMP", "") == 0);
    assert(rt_env_temp() == 77 && strcmp(captured, "/c/Temp") == 0);
    char* snapshot = NULL;
    snapshot_mode = 2;
    assert(rt_env_snapshot("empty", &snapshot) == 0 && snapshot && !snapshot[0]);
    fixture_free(snapshot); assert(injected_freed == 1);
    snapshot_mode = 3;
    assert(rt_env_snapshot("error", &snapshot) != 0 && !snapshot);
    assert(injected_freed == 2);
    snapshot_mode = 0;
    char* argv[] = {"fixture", "--startup-extension", "argv-pack", NULL};
    assert(_putenv_s(SIMPLE_STARTUP_ASPECT_ENV, "first;second") == 0);
    assert(__simple_startup_before_main(3, argv) == 0);
    assert(load_count == 3 && strcmp(loaded[0], "first") == 0);
    assert(strcmp(loaded[1], "second") == 0 && strcmp(loaded[2], "argv-pack") == 0);
    load_count = 0; snapshot_mode = 1;
    assert(__simple_startup_before_main(3, argv) == 1 && load_count == 0);
    snapshot_mode = 0;
    assert(_putenv_s(SIMPLE_STARTUP_ASPECT_ENV, "first;second") == 0);
    fail_path_alloc = 1;
    assert(__simple_startup_before_main(3, argv) == 1 && load_count == 0);
    fail_path_alloc = 0; fail_load = 1;
    assert(__simple_startup_before_main(3, argv) == 1 && load_count == 1);
    fail_load = 0; load_count = 0;
    assert(_putenv_s(SIMPLE_STARTUP_ASPECT_ENV, "") == 0);
    assert(__simple_startup_before_main(1, argv) == 0 && load_count == 0);
    puts("owned env production consumers and startup callbacks: PASS");
    return 0;
}
'''
fixture = out / "env-owned.c"
fixture.write_text(prefix + functions + main)
exe = out / "env-owned.exe"
subprocess.run([args.cc, "/nologo", "/clang:-Werror=deprecated-declarations",
    "/I" + str(root / "src/runtime"), str(fixture),
    "/Fo" + str(out / "env-owned.obj"), "/Fe" + str(exe)], check=True)
subprocess.run([str(exe)], check=True)
