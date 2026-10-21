# Windows core-C GPU fallback discarded a Rust provider section

Fixed at the core-C fallback owner. The C runtime reports no active GPU
backend (zero); a linked strong provider must own the public symbol.

The frozen native-all archive SHA256
`af21f3205ebeaa4fb6f4075e1763aff36dbf0802be6ffea513cc8c18e694f088`
merged `rt_host_gpu_active_backend_handle` and
`rt_vulkan_async_session_supported` at offset zero in cgu.00 section 241,
a three-byte COFF COMDAT with SelectionNoDuplicates. A constant registry
in cgu.03 referenced the latter. The previous strong C host-handle
definition displaced the merged Rust section; lld-link then reported
`relocation against symbol in discarded section` for the Vulkan export.

The C owner now uses a private `core_c_*` function and MSVC alternatename,
or a GNU weak public function. Both fallback paths still return zero.
No Vulkan capability, linker suppression, or Rust provider change is added.
The implementation stays in runtime_native.c so its existing cache input
fingerprint covers every changed byte.

## Evidence

Base: shell provider tip `af74a5083c0754a98bd215c08540b19cd2222e29`.
Bootstrap-only seed SHA256:
`32014b3401e3cb76aec44acb475a22f2385fefcd1d19ab71049e52d633356825`.
Private evidence root:
`D:/dev/simple-windows-http-provider-20261021/build/session/gpu-owner-repair`.
Original section/symbol dumps are in sibling `vulkan-discarded-review`.

- `HOST_GPU_FALLBACK_MSVC=1 CC=clang-cl bash test/01_unit/scripts/host_gpu_backend_fallback_test.shs`:
  production fallback returns zero without a provider; strong provider returns
  73; synthetic merged COFF provider retains both exports (both return 73).
- The same absent/strong controls pass with GNU GCC 15.2.
- `mixed.sh`: exact formerly failing shell bootstrap_main source, frozen
  native-all, new core-C supplement, and original thread witness now link:
  one module compiled, zero failed. Its execution exits 2 at scalar stdout
  assertion; this is retained as a separate mixed-old-runtime shell failure,
  not a shell qualification PASS.
- `gpu-mixed.sh`: same producer/archive/bundle and thread witness with the
  focused GPU entry compiles one module, zero failed, executes exit zero:
  `PASS GPU mixed provider: both zero-valued exports reachable`.

Both scripts use private project, HOME, temporary, frontend and runtime-object
caches, `--runtime-bundle core-c-bootstrap --backend llvm --mode one-binary`,
and entry `src/bootstrap_main.spl`. Their logs, commands, objects and output
are retained under the private evidence root. No parent cache was written.
