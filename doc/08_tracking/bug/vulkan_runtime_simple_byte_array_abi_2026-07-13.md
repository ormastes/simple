# Vulkan runtime Simple byte-array ABI mismatch
## Closed 2026-09-16 — fix landed; focused packed-array test passes; ARM HELLO replays PASS

Reviewed in the 2026-09-16 bug-ledger normalization pass; classification is
bookkeeping from in-file evidence, not a re-run of the repro. Re-open with a
fresh dated repro if the symptom returns.

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

