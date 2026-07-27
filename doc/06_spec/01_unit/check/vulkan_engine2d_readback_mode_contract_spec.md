# Vulkan Engine2D readback execution mode

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

## Scenarios

### runs evidence and focused specs in the requested mode

Requires the shell gate to preserve the requested native mode, reject an
interpreter fallback, and run both focused Vulkan specs in that mode.

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.

```simple
val source = file_read("scripts/check/check-vulkan-engine2d-readback.shs")
expect(source).to_contain("SIMPLE_EXECUTION_MODE:-native")
expect(source.contains("--mode=interpreter")).to_equal(false)
expect(source).to_contain("native_execution_reason=interpreter-fallback")
expect(source).to_contain("vulkan_strict_spec.spl --mode=")
expect(source).to_contain("engine2d_cpu_vulkan_parity_spec.spl --mode=")
expect(source).to_contain("TEST_EXECUTION_MODE")
```

</details>

### rejects CPU fallback, duplicate keys, incomplete buffers, and missing device provenance

Pins exact-one evidence keys, 256-pixel buffers, and deterministic checksums
before accepting the 16x16 Vulkan receipt.

<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.

```simple
val source = file_read("scripts/check/check-vulkan-engine2d-readback.shs")
expect(source).to_contain("backend_probe_initialized(probe)")
expect(source.contains("probe.is_ok()")).to_equal(false)
expect(source).to_contain("read_pixels_with_source()")
expect(source).to_contain("readback_pixels\")\" = \"256")
expect(source).to_contain("clear-pixels-not-256")
expect(source).to_contain("140735349260160")
expect(source).to_contain("140781974135910")
expect(source).to_contain("not-device-readback")
expect(source).to_contain("backend-handle-missing")
expect(source).to_contain("device-identity-missing")
expect(source).to_contain("device-identity-mismatch")
expect(source).to_contain("if (matches != 1) exit 1")
expect(source).to_contain("if [ \"$(value_of overall)\" != \"pass\" ]")
expect(source).to_contain("clear_present_readback.source != \"host_cache_after_device_present\"")
expect(source).to_contain("rect_present_readback.source != \"host_cache_after_device_present\"")
expect(source.index_of("val clear_readback = engine.read_pixels_with_source()")).to_be_less_than(source.index_of("engine.present()"))
```

</details>

### keeps the Windows producer on the same exact device-readback contract

Requires Windows to reject duplicate evidence keys while retaining exact
counts, canonical checksums, device identity, and direct device-readback
provenance rather than a post-present host cache.

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.

```simple
val wrapper = file_read("scripts/check/check-vulkan-engine2d-readback.ps1")
val producer = file_read("scripts/check/vulkan_engine2d_readback_evidence.spl")
expect(wrapper).to_contain("readback-pixels-not-256")
expect(wrapper).to_contain("readback-checksum-not-canonical")
expect(wrapper).to_contain("readback-device-provenance-invalid")
expect(wrapper).to_contain("readback-evidence-invalid")
expect(wrapper).to_contain("Read-ExactOneKeyValueFile")
expect(wrapper).to_contain("vulkan_engine2d_readback_clear_device_identity=")
expect(wrapper).to_contain("gui_web_2d_vulkan_simple_argb_pixel_count=")
expect(producer).to_contain("val clear_readback = engine.read_pixels_with_source()")
expect(producer).to_contain("val rect_readback = engine.read_pixels_with_source()")
expect(producer).to_contain("if clear_pixels.len() != 256:")
expect(producer).to_contain("if rect_pixels.len() != 256:")
expect(producer).to_contain("clear_present_readback.source != \"host_cache_after_device_present\"")
expect(producer).to_contain("rect_present_readback.source != \"host_cache_after_device_present\"")
```

</details>
