# Bug: LLVM backend never emits `__module_init` — heap-typed module-global initializers are dropped (left null)

- **ID:** llvm_backend_missing_module_init_heap_globals_2026-06-15
- **Severity:** P1 (silent: any `var/val X: [T] = [...]`, `= "..."`, or struct-literal module-global is null at runtime under the LLVM backend; `.len()`/index/field/method on it derefs null)
- **Backend:** LLVM (target-independent — reproduced on `x86_64-unknown-linux-gnu` host and `riscv64-unknown-none` kernel)
- **Status:** RESOLVED 2026-06-15 — LLVM backend now emits `__module_init_<prefix>`
  for heap-typed module globals (mirrors cranelift `generate_module_init`); rv64
  boot calls `__simple_call_module_inits` after heap init; init-caller compiled
  with `-mcmodel=medany`. Oracle `scripts/qemu/qemu_rv64_http_test.shs
  --with-storage` now reaches `GET /health (HTTP)... PASS (200)`. See
  `codegen/llvm/backend_core.rs:generate_module_init`,
  `pipeline/native_project/{compiler.rs,linker.rs}`,
  `src/os/kernel/arch/riscv64/boot.spl`. NOTE: a cache-key gap masked the fix on
  the first attempt — see `native_object_cache_key_omits_seed_version_2026-06-15`.
  Separately, `for v in <array>` segfaults on BOTH backends (even local arrays)
  — a pre-existing iterator bug, NOT this issue; explicit indexing + `.len()`
  on init'd globals verified correct.

## Symptom

After fixing the GlobalLoad-`dest()` bug
(`llvm_globalload_dest_missing_folds_to_initializer_2026-06-15`), the RV64 kernel
still soft-restart-loops. First fault (QEMU `-d int,guest_errors`):
```
riscv_cpu_do_interrupt: cause:0x5 (fault_load) epc:0x80210112 tval:0x8
```
`epc 0x80210112` = `boot_nvme_production_handoff_ready` doing `ld a0, 8(a0)` with
`a0 = 0`: the global `_boot_nvme_devices` (declared `var _boot_nvme_devices:
[BlockDevice] = []`) is null, so `rt_array_len` reads offset 8 of null.

This is actually the INTENDED path on the virtio-blk gate (no real NVMe → the
device is correctly never provisioned → `ready()` should return false → mount is
skipped → os_main proceeds to the HTTP server). It faults instead of returning 0
purely because the empty global array was never allocated.

## Root cause

Module-level heap-typed global initializers require a runtime initializer
function (they cannot be a static .data constant — an array/string/struct is a
heap object built via `rt_array_new`/`rt_string_new`/`rt_alloc`).

- The **cranelift** backend generates this: `generate_module_init` in
  `compiler/src/codegen/common_backend.rs` (~line 1633) emits a
  `__module_init_<prefix>` function that allocates each heap global and stores
  the handle, registered so it runs before `main()`.
- The **LLVM** backend has NO equivalent. `grep -rn "generate_module_init\|__module_init"
  src/compiler_rust/compiler/src/codegen/llvm/` returns nothing. It only emits the
  data global with a scalar `const_zero` initializer
  (`codegen/llvm/backend_core.rs:250`). The heap allocation is silently dropped.

Evidence:
- Host LLVM binary: `nm` shows `__simple_call_module_inits` as **weak undefined
  (`w`)** and **zero** `__module_init_*` symbols. `.init_array` contains only the
  libc `__frame_dummy_init_array_entry`.
- Kernel ELF: **zero** `module_init` symbols.
- The linker already aggregates inits: `linker.rs:generate_init_caller` (called on
  both hosted and freestanding paths) scans object symbols for `__module_init_*`
  and synthesizes `__simple_call_module_inits`. It finds none → empty body.

## Minimal repro (host, LLVM backend)

```simple
var _xs: [i64] = [1, 2, 3]
fn ready() -> bool:
    _xs.len() > 0
fn main():
    if ready():
        print("OK")
    else:
        print("BAD")
```
`simple native-build ... --backend llvm` → resulting binary SIGSEGVs (exit 139).
`_xs` is never allocated; `.len()` derefs null+8. Empty literal `= []` segfaults
identically. (Cranelift backend initializes these correctly.)

## Blast radius (why a point-fix is insufficient)

The HTTP server itself relies on heap-typed module globals:
- `src/os/kernel/boot/http_baremetal.spl:14` `val SIMPLEOS_HTTP_LISTEN_ADDR: text = "0.0.0.0:8080"`
- `src/os/kernel/boot/http_baremetal.spl:15` `val SIMPLEOS_HTTP_RESPONSE: text = "HTTP/1.1 200 OK..."` (the 200 body)

These would be null under the LLVM backend, so even a null-tolerant `rt_array_len`
patch on `ready()` would only move the crash into the HTTP path. The HTTP-200
oracle is reachable ONLY by the systemic fix. (A null-tolerant `len()` is also a
mask, not a fix: it returns correct 0 for empty but wrong answers for `[1,2,3]`.)

## Correct fix (scoped, not yet applied)

Two pieces, both required:

1. **Port `generate_module_init` to the LLVM backend** (`codegen/llvm/`): emit a
   `__module_init_<prefix>` function (inkwell IR) that, for each entry in
   `mir.global_init_strings / _arrays / _functions / _structs`, builds the heap
   object via `rt_string_new` / `rt_array_new`(+`rt_array_push` / `rt_byte_array_new`
   +`rt_typed_bytes_u8_push`) / `rt_alloc`, and stores the handle into the global.
   Mirror the ~250-line cranelift implementation (common_backend.rs:1633-~1900).
   The linker's `generate_init_caller` already discovers `__module_init_*` and
   builds `__simple_call_module_inits` — no linker change needed.

2. **Wire the freestanding kernel boot to call `__simple_call_module_inits`.** The
   hosted `main()` stub (linker.rs:562) calls it, but the kernel uses
   `--entry-closure --entry boot.spl` (custom `_start`), bypassing that stub. The
   RV64 boot (`src/os/kernel/arch/riscv64/boot.spl` / `boot/*.c`) must call
   `__simple_call_module_inits()` after the runtime/heap is up and before
   `os_main`. (Declare it weak-extern in the boot C and call if non-null.)

Verify with the host repro (→ `OK`), then rebuild the kernel and run
`scripts/qemu/qemu_rv64_http_test.shs --with-storage` (oracle: `GET /health (HTTP)
... PASS (200)` + storage lines).

### Risk
`generate_module_init` touches the default native backend (LLVM). Regression risk
to all native builds; gate behind the full spec suite. Boot wiring is kernel-local
and low-risk.

## Related
- `llvm_globalload_dest_missing_folds_to_initializer_2026-06-15` (fixed prerequisite)
- `module_level_text_const_empty_in_jit`, `jit_string_method_on_var_receiver_folds`
  (same family — module-level heap globals empty/null under JIT/AOT).
