# SimpleOS target payload image admission — operator manual

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/simpleos_deploy_image_simple_toolchain_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Negative image-admission coverage through the production SimpleOS image
builder. These scenarios prove that unadmitted payloads cannot create
/SYS/SIMPLETOOL.SDN. They do not prove image boot or guest execution.

## Scenarios

### SimpleOS deploy image Simple toolchain payload

#### should reject a marker payload without a provenance stamp

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should reject a marker payload without a provenance stamp
- Submit a marker payload to the production image builder


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reject a marker payload without a provenance stamp")
val root = "build/tmp/simpleos_deploy_image_marker_rejection"
dir_create_all(root)
val payload = root + "/simple-target.smf"
val image = root + "/simpleos-disk.img"

step("Submit a marker payload to the production image builder")
expect(file_write(payload, "SMF_FAKE_TARGET_SIMPLE\nrole=compiler-interpreter-loader\n")).to_be(true)
val result = build_install_image_with_simple_binary(PkgArch.X86_64, "", "", image, 64, payload)
expect(result.is_err()).to_be(true)
if val Err(message) = result:
    expect(message).to_contain("lacks target provenance")
expect(file_exists(image + ".contents/rootfs/SYS/SIMPLETOOL.SDN")).to_be(false)
```

</details>

#### should reject payload provenance from the Rust bootstrap seed

- This is negative admission coverage; a green result does not establish a
  deployable payload or bootable image.
- Positive image and same-run guest evidence remain blocked by B-HOST-CLI,
  B-TARGET-SIMPLE, B-GUEST-LLD, B-IMAGE, and B-DESKTOP-LIVE.
- Full acceptance remains
  `test/03_system/os/simpleos_toolchain_deployment_desktop_boot_spec.spl`.
