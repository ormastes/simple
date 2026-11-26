# Darwin: worker code-address probe also matches DATA (dladdr fallback)

Status: fix-implemented-verification-pending (2026-11-26, branch `work/fix-darwin-code-probe-20261126`). Found 2026-11-07 in review of PR #7420 / #7432.

`src/runtime/runtime_thread.c` `rt_native_address_is_code` has a real
executable-range test on Windows (`VirtualQuery`) and ELF hosts
(`dl_iterate_phdr`), but on macOS it fell back to
`dladdr(...) != 0 && dli_fname != NULL`, which is also true for DATA addresses
inside the image (its own comment says so).

`spl_worker_callable` uses the probe twice: the #7420 bare-entry fast path
(a non-capturing fn value passed as its bare entry address) and the decoded
payload check right after it. On macOS a TAG_HEAP word pointing at a static
closure record in `__DATA` can therefore be taken as code and called.
Guarding only the fast path (tried in #7432, reverted) brings back the #7420
crash for bare entries and leaves the second site exposed.

## Fix Implemented (2026-11-26)

- Added a `#elif defined(__APPLE__)` branch to `rt_native_address_is_code` in
  `src/runtime/runtime_thread.c` (line 707; includes `<mach/mach.h>` and
  `<mach/mach_vm.h>`).
- Strips the arm64 TBI top-byte tag (`~RT_NATIVE_PTR_TAG_BITS`), rejects small
  sentinels (`target < 4096ULL`), and runs a bounded (max depth 16)
  `mach_vm_region_recurse(mach_task_self(), &addr, &size, &depth, (vm_region_recurse_info_t)&info, &count)`
  loop with `vm_region_submap_short_info_data_64_t` /
  `VM_REGION_SUBMAP_SHORT_INFO_COUNT_64`:
  - At each depth, requires `kr == KERN_SUCCESS`, `size > 0`, `addr <= target`,
    and `(target - addr) < size` (guarding against `mach_vm_region_recurse`
    advancing past an unmapped gap).
  - If `info.is_submap`, increments `depth` and descends into the submap (so
    functions inside the dyld shared cache submap are resolved to their leaf
    VM protection rather than misclassified as non-code).
  - Otherwise returns `(info.protection & VM_PROT_EXECUTE) != 0`.
- Kept Windows (`VirtualQuery`), ELF (`dl_iterate_phdr`), and `#else` paths
  unchanged.
- Added Darwin regression `src/runtime/test/darwin_thread_code_dispatch_test.c`
  modelled on `src/runtime/test/windows_thread_code_dispatch_test.c`
  (non-Apple compiles cleanly and returns exit 77 SKIP for CI
  `check-c-runtime-compiles-push.shs` and `c-runtime` test kind compatibility).
  Covers local code, initialized/uninitialized `__DATA`/`__bss`, `TAG_HEAP`
  static closure records, dyld shared cache code (`&puts`, `dlsym(puts)`) vs
  data (`&stdout`, `dlsym(__stdoutp)`), arm64 TBI tags, sentinels `0`/`1`/`4095`,
  RW/RX/`MAP_JIT`/`PROT_NONE`/`munmap`, guarded RW->RX transition, deterministic
  2-page unmap gap-advance, and `rt_thread_spawn_isolated*` dispatch.

## Evidence (macOS arm64, Darwin 25.5.0, Apple clang 17.0.0)

- **RED 1 (before fix, `dladdr` fallback)**:
  ```
  clang -O2 -std=gnu11 -I src/runtime -I src/runtime/platform \
    src/runtime/test/darwin_thread_code_dispatch_test.c \
    src/runtime/runtime_memtrack.c -lpthread \
    -o /tmp/darwin_thread_code_dispatch_test_red && \
  /tmp/darwin_thread_code_dispatch_test_red
  ```
  Output: `FAIL: initialized static __DATA address classified as code` (exit 1).

- **RED 2 (non-recursive `mach_vm_region` against dyld shared cache)**:
  `&puts` / `dlsym(RTLD_DEFAULT, "puts")` returned `is_code=0` because the dyld
  shared cache resides inside a Mach VM submap.

- **GREEN (after `mach_vm_region_recurse` fix, standalone `-Wall -Wextra -Werror`)**:
  ```
  clang -O2 -std=gnu11 -Wall -Wextra -Werror -I src/runtime -I src/runtime/platform \
    src/runtime/test/darwin_thread_code_dispatch_test.c \
    src/runtime/runtime_memtrack.c -lpthread \
    -o /tmp/darwin_thread_code_dispatch_test_v2 && \
  /tmp/darwin_thread_code_dispatch_test_v2
  ```
  Output: `darwin_thread_code_dispatch: PASS` (exit 0, 0 warnings).

- **GREEN (non-Apple syntax & skip check, `-U__APPLE__`)**:
  `cc -fsyntax-only -std=gnu11 -Wall -Wextra -Werror` passed both with and
  without `-U__APPLE__`; non-Apple build printed
  `SKIP: darwin_thread_code_dispatch_test requires macOS/Darwin` and exited `77`.

- **GREEN (core-C archive linked with `-DSIMPLE_TEST_CORE_RUNTIME=1 -Wall -Wextra -Werror`, 20x repeated)**:
  Compiled all core-C runtime objects from `runtime_core_c_sources_v1` (excluding
  unity-included `runtime_thread.c`) into `libcore_c.a`, linked
  `darwin_thread_code_dispatch_test.c` against real `runtime_native.c` closure
  registry, ran 20/20 iterations: `darwin_thread_code_dispatch: PASS` (exit 0).

- **Not verified**: Linux/Windows cross-host builds and full native/bootstrap
  suites were not run on this macOS arm64 host (out of scope / memory cap);
  Linux and Windows branches in `rt_native_address_is_code` are untouched.
  Note: the Rust seed twin `native_address_is_code` in
  `src/compiler_rust/runtime/src/executor.rs` still uses `dladdr` on macOS
  (separate Rust runtime scope; untouched by this C runtime fix).
