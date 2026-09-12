# Vulkan runtime Simple byte-array ABI mismatch

**Status:** CLOSED-STALE (2026-09-12: not re-verifiable from the record; reopen with a fresh repro against the current seed)

The native Simple ABI passes `[u8]` as a tagged `RuntimeArray`. The Vulkan
runtime instead treated shader, upload, readback, and push-constant arguments
as raw byte pointers. Engine2D therefore initialized the Vulkan device but
rejected its first SPIR-V module after reading the array header as shader data.

The shared runtime owner now validates byte-packed arrays and uses their exact
backing pointer and length. Shader compilation no longer scans an arbitrary
64 MiB pointer range; unknown shader handles and unsupported nonzero copy
offsets fail closed.

Evidence: the focused packed-array runtime test passes, the Vulkan-feature
runtime and strict daemon build without stubs, and replaying the captured ARM
HELLO now returns status `PASS`, reason `0`, render mask `1`, and processing
mask `0`. Live ARM rendering remains separately blocked by the freestanding
RuntimeArray header mismatch exposed after HELLO.

## Triage 2026-09-12

Reviewed in the 2026-09-12 bug-db triage sweep (Rule C: filed before 2026-07-29, no runnable repro in the record, no status line existed); closed as stale per the "too old / not valid -> close" triage policy. Evidence: worktree `simple-bugdb-triage` branch `work/bugdb-triage-2026-09-12`; deployed seed `/home/yoon/dev/simple/bin/release/aarch64-unknown-linux-gnu/simple` (50,093,192 B, 2026-09-06 09:59) available for re-verification if reopened.
