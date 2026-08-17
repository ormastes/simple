# SimpleOS `rt_free` ABI signature mismatch

- **Re-verified by content 2026-08-17 (os/runtime lane):** `src/os/libc/simpleos_simple_runtime.c:72` is `void rt_free(void *ptr) {` (one arg) and `src/os/sdk/include/simpleos.h:98` is `void rt_free(void *ptr);` — signatures agree; no second `size` parameter survives anywhere under `src/os/libc/`. `sh scripts/check/check-c-runtime-compiles-push.shs` = `PASS — 104 file(s) compiled, 0 errors`.

- **ID:** `simpleos_rt_free_abi_signature_mismatch_2026-08-02`
- **Status:** FIXED — claimed and repaired by `pure_parser_close` on 2026-08-02
- **Severity:** High (allocator ABI / undefined behavior)

## Reproduction

`src/os/sdk/include/simpleos.h` and every hosted runtime expose
`void rt_free(void *ptr)`, but `src/os/libc/simpleos_simple_runtime.c` defines
`void rt_free(void *ptr, spl_i64 size)`. A caller compiled from the public
header therefore invokes a function with an incompatible definition.

## Scope

Repair the SimpleOS compatibility runtime first and lock the one-argument ABI
with exact and adjacent platform-contract tests. The RISC-V boot runtime's
no-op `rt_free` is a documented bump-arena boundary, not evidence that hosted
Linux/macOS/Windows/BSD deallocation is missing. Likewise, allocator caching
or bounded hardening quarantine can retain RSS after a real `free`.

## Platform matrix

| Runtime | Linux | macOS | Windows | BSD | SimpleOS |
|---|---|---|---|---|---|
| Hosted C/native | `free` | `free` | CRT `free` | `free` | N/A |
| Rust interpreter/seed | `std::alloc::dealloc` | same | same | same | N/A |
| Pure `simple_core` | host `free` | host `free` | host `free` | host `free` | libc `free` |
| Freestanding boot | N/A | N/A | N/A | N/A | RISC-V bump arena; no individual reclaim |

## Fix and verification

The compatibility runtime now defines the public one-argument ABI and still
delegates to libc `free`. The focused SimpleOS contract test checks the exact
signature, rejects the former adjacent two-argument form, and checks the real
deallocation call. It passed in interpreter mode. The C source also compiled
with `-std=c11 -Wall -Wextra -Werror`, and `git diff --check` passed.
