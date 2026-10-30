#!/usr/bin/env python3
"""Compile the production C commit snapshot against the installed Windows SDK.

Also run the dependency-free Rust snapshot tests with the requested 24 threads.
This is a bounded host ABI regression, not seed or phase admission.
"""
import argparse
import pathlib
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument("--cc", default="clang")
parser.add_argument("--output", required=True)
parser.add_argument("--layout-only", action="store_true", help="check Simple source ABI constants against SDK without rerunning native or Rust snapshots")
args = parser.parse_args()
root = pathlib.Path(__file__).resolve().parents[2]
out = pathlib.Path(args.output).resolve()
out.mkdir(parents=True, exist_ok=True)
runtime = (root / "src/runtime/runtime_native.c").read_text(encoding="utf-8")
start = runtime.index("int64_t rt_host_commit_headroom_bytes_v1(void) {")
end = runtime.index("\n}\n", start) + 3
production = runtime[start:end]
simple_owner = (root / "src/app/bootstrap_builder/native_group_windows_main.spl").read_text(encoding="utf-8")
memory_owner = (root / "src/lib/nogc_sync_mut/io/windows_process_owner.spl").read_text(encoding="utf-8")


def source_integer(source, pattern):
    matches = re.findall(pattern, source)
    if len(matches) != 1:
        raise RuntimeError(f"expected exactly one Simple ABI field matching {pattern!r}")
    return int(matches[0])


# Check the actual Simple fallback's numeric ABI against the installed SDK.
# This is a source-layout contract, not execution of the Simple fallback.
layout_assertions = []
for local, sdk in [("total", "CommitTotal"), ("limit", "CommitLimit"), ("page", "PageSize")]:
    offset = source_integer(simple_owner, rf"val {local} = if queried != 0: volatile_read_u64\(info \+ (\d+)\)")
    layout_assertions.append(f'_Static_assert({offset} == offsetof(PERFORMANCE_INFORMATION, {sdk}), "Simple {sdk} offset");')
size = source_integer(simple_owner, r"val info = HeapAlloc\(heap, 8u32, (\d+)u64\)")
layout_assertions.append(f'_Static_assert({size} == sizeof(PERFORMANCE_INFORMATION), "Simple performance size");')
for local, sdk in [("available", "ullAvailPhys"), ("commit_available", "ullAvailPageFile")]:
    offset = source_integer(memory_owner, rf"val {local} = if queried != 0: volatile_read_u64\(status \+ (\d+)\)")
    layout_assertions.append(f'_Static_assert({offset} == offsetof(MEMORYSTATUSEX, {sdk}), "Simple {sdk} offset");')
size = source_integer(memory_owner, r"val status = HeapAlloc\(heap, 8u32, (\d+)u64\)")
layout_assertions.append(f'_Static_assert({size} == sizeof(MEMORYSTATUSEX), "Simple memory size");')
fixture = r'''
#include <windows.h>
#include <psapi.h>
#include <stdint.h>
#include <limits.h>
#include <string.h>
#include <stdio.h>
#include <stddef.h>
'''+"\n".join(layout_assertions)+"\n"+production+r'''
int main(void) {
    PERFORMANCE_INFORMATION info = {0};
    info.cb = sizeof(info);
    if (!K32GetPerformanceInfo(&info, sizeof(info))) return 1;
    uint64_t before = (info.CommitLimit - info.CommitTotal) * info.PageSize;
    int64_t actual = rt_host_commit_headroom_bytes_v1();
    if (actual <= 0 || (uint64_t)actual % info.PageSize != 0) return 2;
    if (!K32GetPerformanceInfo(&info, sizeof(info))) return 3;
    uint64_t after = (info.CommitLimit - info.CommitTotal) * info.PageSize;
    uint64_t low = before < after ? before : after;
    uint64_t high = before > after ? before : after;
    /* Permit concurrent allocations between these three real snapshots. */
    uint64_t tolerance = 256ULL * 1024 * 1024;
    if ((uint64_t)actual + tolerance < low || (uint64_t)actual > high + tolerance) return 4;
    printf("PASS production commit headroom: %lld bytes, SDK page size: %llu\n",
           (long long)actual, (unsigned long long)info.PageSize);
    return 0;
}
'''
c_source = out / "commit-capacity.c"
c_source.write_text(fixture, encoding="utf-8")
if args.layout_only:
    subprocess.run([args.cc, "-c", str(c_source), "-o", str(out / "simple-capacity-layout.o")], check=True)
    print("PASS Simple fallback ABI source-layout contract against SDK (not Simple execution)", flush=True)
    raise SystemExit(0)
c_exe = out / "commit-capacity.exe"
subprocess.run([args.cc, str(c_source), "-o", str(c_exe), "-lkernel32"], check=True)
print("PASS Simple fallback ABI source-layout contract against SDK (not Simple execution)", flush=True)
subprocess.run([str(c_exe)], check=True)
# Reinsert the original Win64 offset bug into the actual production body.
# The same SDK oracle must reject this negative control.
needle = "uint64_t page_size = info.PageSize;"
if needle not in fixture:
    raise RuntimeError("production PageSize statement changed; update the negative control")
negative_source = out / "commit-capacity-offset88.c"
negative_source.write_text(fixture.replace(needle,
    "uint64_t page_size; memcpy(&page_size, (const unsigned char*)&info + 88, sizeof(page_size));"),
    encoding="utf-8")
negative_exe = out / "commit-capacity-offset88.exe"
subprocess.run([args.cc, str(negative_source), "-o", str(negative_exe), "-lkernel32"], check=True)
negative = subprocess.run([str(negative_exe)])
if negative.returncode not in (2, 4):
    raise RuntimeError(f"offset88 negative control returned unexpected status {negative.returncode}")
print(f"PASS original offset88 bug rejected by SDK oracle (status {negative.returncode})", flush=True)
rust_exe = out / "host-capacity-tests.exe"
rust_source = root / "src/compiler_rust/compiler/src/interpreter_extern/host_capacity_platform.rs"
subprocess.run(["rustc", "--edition=2021", "--test", str(rust_source),
                "-C", "codegen-units=24", "-o", str(rust_exe)], check=True)
subprocess.run([str(rust_exe), "--test-threads=24"], check=True)
