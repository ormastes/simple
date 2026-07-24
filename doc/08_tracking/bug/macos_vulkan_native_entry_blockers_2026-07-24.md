# macOS Vulkan native entry blockers — 2026-07-24

## Status

OPEN — Vulkan installation, pure-Simple AOT entry, MoltenVK instance creation,
and device enumeration now work. The canonical Engine2D capture reaches
`backend=vulkan` but fails before readback because the hosted runtime bundle is
incomplete.

## Host evidence

- macOS 26.5, arm64 Apple M4
- `vulkaninfo --summary`: Vulkan 1.4.350
- physical device: Apple M4
- driver: MoltenVK 1.4.1
- loader: Homebrew `vulkan-loader 1.4.350.1`
- ICD: `/opt/homebrew/share/vulkan/icd.d/MoltenVK_icd.json`

## Reproduction

The canonical environment wrapper was run with the native self-hosted binary:

```
SIMPLE_BIN=bin/release/aarch64-apple-darwin/simple \
  GUI_WEB_2D_VULKAN_BUILD_DIR=build/gui-web-2d-vulkan-macos-native \
  scripts/setup/setup-gui-web-2d-vulkan-env.shs --run
```

Structured evidence:
`build/gui-web-2d-vulkan-macos-native/evidence.env`.

The pure-Simple focused run is recorded in
`build/vulkan-readback-pure-simple-macos/`.

## Independent blockers

1. `scripts/setup/setup-gui-web-2d-vulkan-env.shs` initially selects an
   executable Linux release path on Darwin. Pinning the native arm64 binary
   bypasses selection but does not make the backend available.
2. The self-hosted interpreter links the core C runtime, where
   `rt_vulkan_is_available()` is hard-coded to return zero. This is the existing
   `rt_vulkan_only_executes_under_classic_interpret_2026-06-17.md` defect.
3. The classic Rust interpreter's `vulkan_dlopen::load_vulkan()` treats Darwin
   as generic Unix and probes only `.so` names, not Homebrew's Vulkan dylibs.
4. Native/JIT lowering reaches imported font-atlas code before the GPU probe
   and emits nonexistent external method symbols for imported numeric globals:
   first `FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION_dot_to_string`, then
   `FONT_ATLAS_COMPOSITE_SEMANTICS_VERSION_dot_to_text`. It falls back to the
   interpreter and therefore hits blocker 2.
5. Chromium/Electron on this macOS build rejects ANGLE Vulkan. Electron logs
   list only ANGLE OpenGL and Metal as allowed implementations, so browser
   bitmap output is not Vulkan evidence.

## Source progress

- `render_text_to_buffer` no longer uses the stale `.bytes()[i]` workaround;
  it uses the repaired `char_code_at(i)` scalar path. This removed the first
  HIR lowering error.
- Numeric cache-key conversions now use the native-standard `.to_text()` API.
  Imported-global method lowering still needs a compiler fix.

## Required fixes

- Implement or link real `rt_vulkan_*` providers for the self-hosted
  interpreter/native runtime; do not keep the zero-device stub as the active
  provider for hosted GPU programs.
- Make Darwin dynamic loading probe `libvulkan.1.dylib`,
  `libvulkan.dylib`, and an approved Homebrew/Vulkan SDK path.
- Fix imported typed-global method lowering so numeric conversions resolve as
  scalar operations rather than synthesized external symbols.
- Make the canonical setup wrapper choose a host-compatible self-hosted binary
  before inspecting optional loader strings.
- Use a browser build that genuinely supports ANGLE Vulkan on macOS, or mark
  the browser Vulkan lane unsupported and keep it distinct from Simple
  Engine2D MoltenVK evidence.

## Update — isolated real provider prepared

A feature-built macOS runtime now exists outside the shared Cargo target:

```
build/vulkan-runtime-macos/release/libsimple_runtime.a
```

It was built with the `vulkan` feature and exports distinct real
`rt_vulkan_*` implementations, including availability, init, device count,
buffer allocation, SPIR-V compilation, compute dispatch, and readback. The
isolated path prevents unrelated default Cargo builds from overwriting it with
the no-Vulkan stub archive.

The imported-global lowering workaround was also narrowed: the semantics
version is first copied into a typed local before `.to_text()` is called.

Execution is still blocked before link/run:

- the current source-loaded pure compiler fails with
  `method has not found on type nil`; its three dirty MIR lowering files belong
  to another active lane and were not modified here;
- the compiled pure stage3 compiler scans the full repository and stops on the
  pre-existing `add-dir` / `add_dir` sanitized module-name collision.

Build logs and the single-file probe are under
`build/vulkan-runtime-macos/`. No Rust seed fallback was used.

## Update — loader available, instance creation fails

The isolated feature-built runtime was tested from a normal non-SIP test
executable with Homebrew's loader and MoltenVK ICD:

```
DYLD_LIBRARY_PATH=/opt/homebrew/lib \
VK_ICD_FILENAMES=/opt/homebrew/share/vulkan/icd.d/MoltenVK_icd.json \
cargo test -p simple-runtime --features vulkan test_vulkan_available
```

Result: PASS. The runtime can load Vulkan.

The next hard-gated test,
`vulkan::tests::test_instance_creation`, fails at
`VulkanInstance::get_or_init()`. Inspection of
`src/compiler_rust/runtime/src/vulkan/instance.rs` shows the macOS instance
path enables `VK_EXT_metal_surface`, but does not enable
`VK_KHR_portability_enumeration` and does not set
`VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR`. MoltenVK advertises the
portability extension on this host, and device enumeration cannot be considered
working until the runtime requests the portability contract.

This is now a separate runtime blocker after loader availability:

1. add the portability-enumeration extension on macOS;
2. set `vk::InstanceCreateFlags::ENUMERATE_PORTABILITY_KHR`;
3. rerun the instance, device, buffer, compute, and readback gates once;
4. then link the provider into the pure-Simple AOT probe after the unrelated
   active MIR lane and stage3 module collision are resolved.

## Update — Simple MoltenVK instance/device PASS; Engine2D bundle still blocked

The macOS instance path now:

- enables `VK_KHR_portability_enumeration`;
- sets `VK_INSTANCE_CREATE_ENUMERATE_PORTABILITY_BIT_KHR`;
- enables `VK_LAYER_KHRONOS_validation` only when the loader advertises it.

After rebuilding the isolated runtime archive, a pure-Simple stage3 AOT probe
completed successfully with:

```
vulkan_runtime_available=true
vulkan_runtime_initialized=true
vulkan_runtime_device_count=1
vulkan_runtime_shutdown=true
```

The stale deployed July 5 compiler was the source of the earlier
`method has not found on type nil` failure. The July 24 pure-Simple stage3
compiler builds the probe. The full-tree collision was also repaired by
removing the redundant hyphenated `commands/add-dir/index.spl` and
`validation.spl`; the underscored canonical modules and the unique
hyphenated `add-dir.spl` remain.

The hosted Rust runtime was missing the Engine2D span ABI. It now implements
and unit-tests `rt_engine2d_simd_fill_span_u32` and
`rt_engine2d_simd_copy_span_u32`.

Three bounded canonical Engine2D launch cycles were used:

1. dyld failure: missing `rt_engine2d_simd_copy_span_u32`;
2. dyld failure: missing dead Intel-backend upload/download symbols;
3. with the compiler's explicit `SIMPLE_STUB_MISSING_RT=1` completion mode,
   the executable reached `backend=vulkan`, then failed with
   `runtime error: field access on nil receiver` after weak-stubbed
   RenderDoc/runtime helper calls.

Per the mandatory three-cycle guard, no further Engine2D retry was made.
Vulkan readback/render capture and event evidence remain unproven, so web,
GUI, WM, Metal, and QEMU checks must not yet be treated as reached.
