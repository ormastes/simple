#!/usr/bin/env python3
"""Exercise actual ARM32 native lease/section owner bodies with mocked state.

This does not execute the exception entry, CP15 instructions, or a guest. The
separate real ARM target compile is required for those source/ABI inputs.
"""
import argparse
import hashlib
import pathlib
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parents[2]
BOOT = ROOT / 'examples/09_embedded/simple_os/arch/arm32/boot'

HARNESS = r'''
#include <stdint.h>
#include <stddef.h>
#include <stdio.h>
#include "arm32_authenticated_syscall_v1.h"
static uint32_t g_arm32_exec_state = 0;
static uint32_t g_arm32_auth_phase;
static uint32_t root_storage[8192];
static uint32_t *g_arm32_el0_l1;
static uint32_t actual_root;
static uint32_t arm32_current_ttbr0(void) { return actual_root; }
@OWNER@
@PREFLIGHT@
static int controls;
#define CHECK(x) do { ++controls; if (!(x)) { fprintf(stderr,"control %d failed: %s\n",controls,#x); return 1; } } while (0)
int64_t simple_arm32_authenticated_syscall_dispatch_v1(uint64_t id,
    uint64_t task, uint64_t gen, uint64_t root, uint64_t a3, uint64_t a4)
{
    (void)a3; (void)a4;
    if (id != 0x7fff0000U || task != 3 || gen != 11 || root != actual_root ||
        g_arm32_auth_phase != 1 || rt_arm32_authenticated_scope_epoch_v1(task,gen,root)) return -1;
    return 0x41524d31;
}
int main(void)
{
    g_arm32_el0_l1 = (uint32_t *)(((uintptr_t)root_storage + 16383U) & ~(uintptr_t)16383U);
#ifdef TRANSLATION_ONLY
    CHECK(arm32_auth_par_identity_page_v1(0x40012000U,0x40012abcU));
    CHECK(!arm32_auth_par_identity_page_v1(0x40012001U,0x40012000U));
    CHECK(!arm32_auth_par_identity_page_v1(0x40012002U,0x40012000U));
    CHECK(!arm32_auth_par_identity_page_v1(0x40013000U,0x40012000U));
    uint32_t parent[4096] = {0}, child[4096] = {0};
    uint32_t section = 0x40000402U;
    CHECK(arm32_auth_supervisor_section_v1(section | 32U,7) && !arm32_auth_user_coarse_v1(0x40000001U,7));
    CHECK(arm32_auth_supervisor_section_v1(section | 32U,4) && !arm32_auth_user_coarse_v1(0x40000001U,4));
    CHECK(arm32_auth_user_coarse_v1(0x40000001U,5));
    CHECK(!arm32_auth_user_coarse_v1(0x40000021U,5));
    parent[4095] = child[4095] = 0xFFF00402U;
    CHECK(arm32_auth_section_span_v1(parent,child,1,UINT64_C(0xfffffff0),UINT64_C(0x100000000)));
    CHECK(!arm32_auth_section_span_v1(parent,child,1,UINT64_C(0xfffffff0),UINT64_C(0x100000001)));
    CHECK(!arm32_auth_section_span_v1(parent,child,1,0x40010000U,0x40011000U));
    parent[1024] = child[1024] = section;
    CHECK(arm32_auth_section_span_v1(parent,child,1,0x40010000U,0x40011000U));
    CHECK(arm32_auth_identity_ram_v1(0x4000140EU,1,0x40012000U));
    CHECK(!arm32_auth_identity_ram_v1(0x4010140EU,1,0x40012000U));
    CHECK(!arm32_auth_identity_ram_v1(0x4000140EU,3,0x40012000U));
    CHECK(!arm32_auth_identity_ram_v1(0x40000402U,1,0x40012000U));
    CHECK(!arm32_auth_identity_ram_v1(0x40001C0EU,1,0x40012000U));
    CHECK(!arm32_auth_identity_ram_v1(0x4000940EU,1,0x40012000U));
    printf("arm32-native-translation-controls-ok:%d\n",controls);
    return 0;
#endif
#ifdef INSTALL_NEGATIVE_ONLY
    actual_root = (uint32_t)(uintptr_t)g_arm32_el0_l1;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root));
    g_arm32_auth_prepared_root = actual_root;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root + 1U));
    CHECK(!rt_arm32_authenticated_install_v1(UINT64_C(0x100000003),11,actual_root));
    g_arm32_exec_state = 1;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root));
    printf("arm32-native-install-negative-controls-ok:%d\n",controls);
    return 0;
#endif
#ifdef PREFLIGHT_ONLY
    uint32_t parent[4096] = {0}, child[4096] = {0};
    uint32_t section = 0x40000402U;
    CHECK(arm32_auth_supervisor_section_v1(section,1));
    CHECK(!arm32_auth_supervisor_section_v1(section,3));
    CHECK(!arm32_auth_supervisor_section_v1(section | 0x800U,1));
    CHECK(!arm32_auth_supervisor_section_v1(section | (1U << 18),1));
    CHECK(!arm32_auth_supervisor_section_v1(section | 1U,1));
    CHECK(!arm32_auth_supervisor_section_v1(0x40000001U,1));
    CHECK(!arm32_auth_supervisor_section_v1(section | 32U,1));
    CHECK(arm32_auth_supervisor_section_v1(section | 32U,4));
    CHECK(!arm32_auth_section_span_v1(parent,child,1,0x40010000U,0x40011000U));
    parent[1024] = child[1024] = section;
    CHECK(arm32_auth_section_span_v1(parent,child,1,0x40010000U,0x40011000U));
    child[1024] ^= 0x100000U;
    CHECK(!arm32_auth_section_span_v1(parent,child,1,0x40010000U,0x40011000U));
    CHECK(!arm32_auth_section_span_v1(parent,child,1,0,32));
    CHECK(arm32_auth_supervisor_section_v1(section | 32U,7) && !arm32_auth_user_coarse_v1(0x40000001U,7));
    CHECK(arm32_auth_supervisor_section_v1(section | 32U,4) && !arm32_auth_user_coarse_v1(0x40000001U,4));
    CHECK(arm32_auth_user_coarse_v1(0x40000001U,5));
    CHECK(!arm32_auth_user_coarse_v1(0x40000021U,5));
    printf("arm32-native-preflight-controls-ok:%d\n",controls);
    return 0;
#endif

    CHECK((uintptr_t)g_arm32_el0_l1 <= UINT32_MAX);
    actual_root = (uint32_t)(uintptr_t)g_arm32_el0_l1;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root));
    g_arm32_auth_prepared_root = actual_root;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root + 1U));
    CHECK(!rt_arm32_authenticated_install_v1(UINT64_C(0x100000003),11,actual_root));
    g_arm32_exec_state = 1;
    CHECK(!rt_arm32_authenticated_install_v1(3,11,actual_root));
    g_arm32_exec_state = 0;
    g_arm32_auth_prepared_root = actual_root;
    CHECK(!rt_arm32_authenticated_install_v1(3,12,actual_root));
    g_arm32_auth_prepared_root = actual_root;
    CHECK(rt_arm32_authenticated_install_v1(3,11,actual_root) == 1);
    CHECK(!rt_arm32_authenticated_install_v1(4,11,actual_root));
    CHECK(!rt_arm32_authenticated_scope_epoch_v1(3,11,actual_root));
    g_arm32_auth_epoch = 41;
    CHECK(rt_arm32_authenticated_scope_matches_v1(3,11,actual_root,41));
    CHECK(!rt_arm32_authenticated_scope_matches_v1(4,11,actual_root,41));
    CHECK(!rt_arm32_authenticated_scope_matches_v1(3,12,actual_root,41));
    CHECK(!rt_arm32_authenticated_scope_matches_v1(3,11,actual_root,40));
    CHECK(!rt_arm32_authenticated_scope_matches_v1(3,11,actual_root,0));
    actual_root ^= 16384;
    CHECK(!rt_arm32_authenticated_scope_matches_v1(3,11,g_arm32_auth_root,41));
    actual_root ^= 16384;
    g_arm32_auth_completed = 1;
    CHECK(!rt_arm32_authenticated_reap_v1(3,11,actual_root));
    g_arm32_auth_epoch = 0;
    CHECK(!rt_arm32_authenticated_reap_v1(4,11,actual_root));
    CHECK(rt_arm32_authenticated_reap_v1(3,11,actual_root) == 1);
    CHECK(!rt_arm32_authenticated_scope_matches_v1(3,11,actual_root,41));
    CHECK(!rt_arm32_authenticated_reap_v1(3,11,actual_root));
    printf("arm32-native-owner-controls-ok:%d\n",controls);
    return 0;
}
'''

def main():
    p = argparse.ArgumentParser()
    p.add_argument('--cc', required=True)
    p.add_argument('--out', required=True, type=pathlib.Path)
    p.add_argument('--preflight-only', action='store_true')
    p.add_argument('--translation-only', action='store_true')
    p.add_argument('--install-negative-only', action='store_true')
    args = p.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    inputs = [BOOT / 'baremetal_stubs.c', BOOT / 'arm32_authenticated_syscall_v1.h']
    snapshots = [path.read_bytes() for path in inputs]
    source = snapshots[0].decode('utf-8').replace('\r\n', '\n')
    before = [hashlib.sha256(data).hexdigest() for data in snapshots]
    start = source.index('/* ARM32_AUTHENTICATED_SCOPE_V1_BEGIN')
    end = source.index('/* ARM32_AUTHENTICATED_SCOPE_V1_END */', start)
    section_start = source.index('/* ARM32_SECTION_PREFLIGHT_V1_BEGIN */')
    section_end = source.index('/* ARM32_SECTION_PREFLIGHT_V1_END */', section_start)
    test = out / 'actual-owner-control.c'
    test.write_text(HARNESS.replace('@OWNER@', source[start:end]).replace('@PREFLIGHT@', source[section_start:section_end]))
    exe = out / 'actual-owner-control.exe'
    groups = [(args.preflight_only, 'PREFLIGHT_ONLY'),
              (args.translation_only, 'TRANSLATION_ONLY'),
              (args.install_negative_only, 'INSTALL_NEGATIVE_ONLY')]
    if sum(enabled for enabled, _ in groups) > 1:
        p.error('choose only one control group')
    defines = [f'-D{name}=1' for enabled, name in groups if enabled]
    linker_flags = ['-Wl,--image-base,0x400000'] if sys.platform == 'win32' else ['-no-pie']
    subprocess.run([args.cc, *defines, '-std=c11', '-O1', *linker_flags,
                    '-I', str(BOOT), str(test), '-o', str(exe)], check=True)
    run = subprocess.run([str(exe)], capture_output=True, timeout=10)
    (out / 'stdout.bin').write_bytes(run.stdout)
    (out / 'stderr.bin').write_bytes(run.stderr)
    count = 4 if args.install_negative_only else 18 if args.translation_only else 16 if args.preflight_only else 20
    kind = 'install-negative' if args.install_negative_only else 'translation' if args.translation_only else 'preflight' if args.preflight_only else 'owner'
    marker = f'arm32-native-{kind}-controls-ok:{count}'.encode()
    if run.returncode or run.stderr or run.stdout not in (marker + b'\n', marker + b'\r\n'):
        raise SystemExit(f'owner controls failed: rc={run.returncode}, stdout={run.stdout!r}, stderr={run.stderr!r}')
    after = [hashlib.sha256(path.read_bytes()).hexdigest() for path in inputs]
    if before != after:
        raise SystemExit('production inputs changed during native controls')
    (out / 'result.sdn').write_text(f'schema: arm32-native-{kind}-controls-v1\nstatus: PASS\ncontrols: {count}\n' +
        f'source_sha256: "{before[0]}"\nheader_sha256: "{before[1]}"\n' +
        'qualification: host_mock_only\nguest_execution: false\n')
    print(f'PASS: {count} actual native {kind} controls; guest execution unverified')

if __name__ == '__main__':
    main()
