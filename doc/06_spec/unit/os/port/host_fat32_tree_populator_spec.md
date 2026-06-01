# Host Fat32 Tree Populator Specification

## Scenarios

### host_fat32_tree_populator

#### mirrors host directories and files into a formatted FAT32 image and flushes

1.  cleanup
   - Expected: rt_dir_create_all(source_root + "/APPS/TOOLS") is true
   - Expected: rt_file_write_bytes(image_path, _make_formatted_fat32_image()) is true
   - Expected: rt_file_write_bytes(source_root + "/KERNEL.BIN", [107u8, 101u8, 114u8, 110u8, 101u8, 108u8, 45u8, 105u8, 109u8, 97u8, 103u8, 101u8]) is true
   - Expected: rt_file_write_bytes(source_root + "/APPS/HELLO.SMF", [104u8, 101u8, 108u8, 108u8, 111u8, 45u8, 97u8, 112u8, 112u8]) is true
   - Expected: rt_file_write_bytes(source_root + "/APPS/TOOLS/EMPTY.DAT", []) is true
   - Expected: populate_result.is_ok() is true
   - Expected: _od_hex(image_path, 0, 64) contains `02 01 20 00 02`
   - Expected: _od_hex(image_path, root_dir + 0, 11) equals `41 50 50 53 20 20 20 20 20 20 20`
   - Expected: _od_hex(image_path, root_dir + 11, 1) equals `10`
   - Expected: _od_hex(image_path, root_dir + 26, 2) equals `03 00`
   - Expected: _od_hex(image_path, root_dir + 32, 11) equals `4b 45 52 4e 45 4c 20 20 42 49 4e`
   - Expected: _od_hex(image_path, root_dir + 32 + 11, 1) equals `20`
   - Expected: _od_hex(image_path, root_dir + 32 + 26, 2) equals `07 00`
   - Expected: _od_hex(image_path, root_dir + 32 + 28, 4) equals `0c 00 00 00`
   - Expected: _od_hex(image_path, apps_dir + 0, 11) equals `2e 20 20 20 20 20 20 20 20 20 20`
   - Expected: _od_hex(image_path, apps_dir + 32, 11) equals `2e 2e 20 20 20 20 20 20 20 20 20`
   - Expected: _od_hex(image_path, apps_dir + 64, 11) equals `54 4f 4f 4c 53 20 20 20 20 20 20`
   - Expected: _od_hex(image_path, apps_dir + 64 + 11, 1) equals `10`
   - Expected: _od_hex(image_path, apps_dir + 64 + 26, 2) equals `04 00`
   - Expected: _od_hex(image_path, apps_dir + 96, 11) equals `48 45 4c 4c 4f 20 20 20 53 4d 46`
   - Expected: _od_hex(image_path, apps_dir + 96 + 11, 1) equals `20`
   - Expected: _od_hex(image_path, apps_dir + 96 + 26, 2) equals `06 00`
   - Expected: _od_hex(image_path, apps_dir + 96 + 28, 4) equals `09 00 00 00`
   - Expected: _od_hex(image_path, tools_dir + 64, 11) equals `45 4d 50 54 59 20 20 20 44 41 54`
   - Expected: _od_hex(image_path, tools_dir + 64 + 11, 1) equals `20`
   - Expected: _od_hex(image_path, tools_dir + 64 + 26, 2) equals `05 00`
   - Expected: _od_hex(image_path, tools_dir + 64 + 28, 4) equals `00 00 00 00`
   - Expected: _od_hex(image_path, _cluster_offset(6), 9) equals `68 65 6c 6c 6f 2d 61 70 70`
   - Expected: _od_hex(image_path, _cluster_offset(7), 12) equals `6b 65 72 6e 65 6c 2d 69 6d 61 67 65`

2.  cleanup


<details>
<summary>Executable SPipe</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/host_fat32_tree_populator_spec"
val image_path = root + "/disk.img"
val source_root = root + "/src"
_cleanup(root)

expect(rt_dir_create_all(source_root + "/APPS/TOOLS")).to_equal(true)
expect(rt_file_write_bytes(image_path, _make_formatted_fat32_image())).to_equal(true)
expect(rt_file_write_bytes(source_root + "/KERNEL.BIN", [107u8, 101u8, 114u8, 110u8, 101u8, 108u8, 45u8, 105u8, 109u8, 97u8, 103u8, 101u8])).to_equal(true)
expect(rt_file_write_bytes(source_root + "/APPS/HELLO.SMF", [104u8, 101u8, 108u8, 108u8, 111u8, 45u8, 97u8, 112u8, 112u8])).to_equal(true)
expect(rt_file_write_bytes(source_root + "/APPS/TOOLS/EMPTY.DAT", [])).to_equal(true)

val populate_result = populate_host_tree_into_fat32_image(image_path, source_root)
expect(populate_result.is_ok()).to_equal(true)
expect(_od_hex(image_path, 0, 64).contains("02 01 20 00 02")).to_equal(true)

val root_dir = _cluster_offset(2)
expect(_od_hex(image_path, root_dir + 0, 11)).to_equal("41 50 50 53 20 20 20 20 20 20 20")
expect(_od_hex(image_path, root_dir + 11, 1)).to_equal("10")
expect(_od_hex(image_path, root_dir + 26, 2)).to_equal("03 00")
expect(_od_hex(image_path, root_dir + 32, 11)).to_equal("4b 45 52 4e 45 4c 20 20 42 49 4e")
expect(_od_hex(image_path, root_dir + 32 + 11, 1)).to_equal("20")
expect(_od_hex(image_path, root_dir + 32 + 26, 2)).to_equal("07 00")
expect(_od_hex(image_path, root_dir + 32 + 28, 4)).to_equal("0c 00 00 00")

val apps_dir = _cluster_offset(3)
expect(_od_hex(image_path, apps_dir + 0, 11)).to_equal("2e 20 20 20 20 20 20 20 20 20 20")
expect(_od_hex(image_path, apps_dir + 32, 11)).to_equal("2e 2e 20 20 20 20 20 20 20 20 20")
expect(_od_hex(image_path, apps_dir + 64, 11)).to_equal("54 4f 4f 4c 53 20 20 20 20 20 20")
expect(_od_hex(image_path, apps_dir + 64 + 11, 1)).to_equal("10")
expect(_od_hex(image_path, apps_dir + 64 + 26, 2)).to_equal("04 00")
expect(_od_hex(image_path, apps_dir + 96, 11)).to_equal("48 45 4c 4c 4f 20 20 20 53 4d 46")
expect(_od_hex(image_path, apps_dir + 96 + 11, 1)).to_equal("20")
expect(_od_hex(image_path, apps_dir + 96 + 26, 2)).to_equal("06 00")
expect(_od_hex(image_path, apps_dir + 96 + 28, 4)).to_equal("09 00 00 00")

val tools_dir = _cluster_offset(4)
expect(_od_hex(image_path, tools_dir + 64, 11)).to_equal("45 4d 50 54 59 20 20 20 44 41 54")
expect(_od_hex(image_path, tools_dir + 64 + 11, 1)).to_equal("20")
expect(_od_hex(image_path, tools_dir + 64 + 26, 2)).to_equal("05 00")
expect(_od_hex(image_path, tools_dir + 64 + 28, 4)).to_equal("00 00 00 00")

expect(_od_hex(image_path, _cluster_offset(6), 9)).to_equal("68 65 6c 6c 6f 2d 61 70 70")
expect(_od_hex(image_path, _cluster_offset(7), 12)).to_equal("6b 65 72 6e 65 6c 2d 69 6d 61 67 65")

_cleanup(root)
```

</details>

#### mirrors AI CLI staged package layout with node-compatible runtime paths

1.  cleanup
   - Expected: rt_dir_create_all(source_root + "/sys/runtime/node-compatible/x86") is true
   - Expected: rt_dir_create_all(source_root + "/sys/apps/codex") is true
   - Expected: rt_file_write_bytes(image_path, _make_formatted_fat32_image()) is true

2.  write text

3.  write text

4.  write text

5.  write text
   - Expected: populate_result.is_ok() is true
   - Expected: _image_contains(image_path, "AI_CLI_RUNTIME_X86_NODE_COMPATIBLE") is true
   - Expected: _image_contains(image_path, "__simple_ai_cli_smoke") is true
   - Expected: _image_contains(image_path, "manifest-package-smoke:codex:20260530") is true
   - Expected: _image_contains(image_path, "[ai-cli] runtime:start app=codex") is true

6.  cleanup


<details>
<summary>Executable SPipe</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = "/tmp/host_fat32_ai_cli_tree_populator_spec"
val image_path = root + "/disk.img"
val source_root = root + "/src"
_cleanup(root)

expect(rt_dir_create_all(source_root + "/sys/runtime/node-compatible/x86")).to_equal(true)
expect(rt_dir_create_all(source_root + "/sys/apps/codex")).to_equal(true)
expect(rt_file_write_bytes(image_path, _make_formatted_fat32_image())).to_equal(true)

_write_text(source_root + "/sys/runtime/node-compatible/x86/runtime.smf", "AI_CLI_RUNTIME_X86_NODE_COMPATIBLE")
_write_text(source_root + "/sys/apps/codex/codex.js", "globalThis.__simple_ai_cli_smoke = true;")
_write_text(source_root + "/sys/apps/codex/AI_MANIFEST.SDN", "manifest-package-smoke:codex:20260530")
_write_text(source_root + "/sys/apps/codex/qemu_markers.txt", "[ai-cli] runtime:start app=codex")

val populate_result = populate_host_tree_into_fat32_image(image_path, source_root)
expect(populate_result.is_ok()).to_equal(true)
expect(_image_contains(image_path, "AI_CLI_RUNTIME_X86_NODE_COMPATIBLE")).to_equal(true)
expect(_image_contains(image_path, "__simple_ai_cli_smoke")).to_equal(true)
expect(_image_contains(image_path, "manifest-package-smoke:codex:20260530")).to_equal(true)
expect(_image_contains(image_path, "[ai-cli] runtime:start app=codex")).to_equal(true)

_cleanup(root)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/port/host_fat32_tree_populator_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- host_fat32_tree_populator

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |

