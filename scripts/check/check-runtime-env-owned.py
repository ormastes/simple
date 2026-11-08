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
#include "runtime_env_owned.h"
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
    "int64_t rt_env_temp(void)"])
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
    puts("owned env production consumers: PASS");
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
