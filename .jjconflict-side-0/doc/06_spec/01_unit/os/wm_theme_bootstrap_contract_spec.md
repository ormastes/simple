# Wm Theme Bootstrap Contract Specification

> Tests covering WM theme bootstrap ownership.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Wm Theme Bootstrap Contract Specification

## Scenarios

### WM theme bootstrap ownership

#### installs the resolved host package before backend and compositor creation

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- installs the resolved host package before backend and compositor creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the resolved host package before backend and compositor creation")
val source = file_read("src/os/hosted/hosted_entry.spl")
val install = source.index_of("install_default_host_wm_theme()")
val css_override = source.index_of("apply_host_wm_css_theme_override(")
val backend = source.index_of("HostedWinitBufferBackend.create(")
val compositor = source.index_of("HostCompositor.new_headless(")
expect(source).to_contain("install_default_host_wm_theme")
expect(source).to_contain("apply_host_wm_css_theme_override")
expect(install).to_be_greater_than(0)
expect(install).to_be_less_than(backend)
expect(install).to_be_less_than(compositor)
expect(css_override).to_be_greater_than(install)
expect(css_override).to_be_less_than(backend)
expect(source).to_contain("rt_env_get(\"SIMPLE_WM_THEME_FILE\")")
expect(source).to_contain("file_read(theme_file)")
```

</details>

#### prefers active state then the package-owned snapshot projection

- prefers active state then the package-owned snapshot projection


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("prefers active state then the package-owned snapshot projection")
val source = file_read("src/os/compositor/host_wm_theme_bootstrap.spl")
val active = source.index_of("active_wm_theme_snapshot_present()")
val unchecked = source.index_of("active_wm_theme_snapshot_unchecked()")
val fallback = source.index_of("install_host_wm_theme(default_theme_id())")
val projected = source.index_of("theme_package_render_snapshot(theme_id)")
expect(active).to_be_greater_than(0)
expect(unchecked).to_be_greater_than(active)
expect(fallback).to_be_greater_than(unchecked)
expect(projected).to_be_greater_than(0)
expect(source).to_contain("apply_theme_render_snapshot_to_wm_chrome")
expect(source.contains("load_theme_package(")).to_be(false)
expect(source.contains("aetheric_dark_theme_render_snapshot()")).to_be(false)
expect(source.contains("active_wm_theme_render_snapshot()")).to_be(false)
expect(source).to_contain("fn apply_host_wm_css_theme_override(css_text: text) -> bool:")
expect(source).to_contain("apply_wm_css_theme_text(css_text)")
expect(source).to_contain("fn active_host_wm_theme_snapshot() -> ThemeRenderSnapshot:")
```

</details>

#### installs an explicit host package through the canonical snapshot projection

- installs an explicit host package through the canonical snapshot projection
   - Expected: snapshot.id equals `aetheric_dark`
   - Expected: active_wm_theme_id() equals `snapshot.id`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs an explicit host package through the canonical snapshot projection")
val snapshot = install_host_wm_theme("glass_dark")
expect(snapshot.id).to_equal("aetheric_dark")
expect(snapshot.source_manifest_sha256.len()).to_be_greater_than(0)
expect(snapshot.material_sha256.len()).to_be_greater_than(0)
expect(active_wm_theme_id()).to_equal(snapshot.id)
```

</details>

#### reprojects a valid host CSS override into the active snapshot identity

- reprojects a valid host CSS override into the active snapshot identity
   - Expected: effective_snapshot.background_rgba equals `0xFF112233u32`
   - Expected: effective_snapshot.foreground_rgba equals `0xFF445566u32`
   - Expected: effective_snapshot.accent_rgba equals `0xFF778899u32`
   - Expected: effective_snapshot.material.window_fill_rgba equals `0xFFAABBCCu32`
   - Expected: effective_snapshot.material.inactive_title_fill_rgba equals `0xFFDDEEFFu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("reprojects a valid host CSS override into the active snapshot identity")
val package_snapshot = install_host_wm_theme("glass_dark")
val installed = apply_host_wm_css_theme_override(
    "--wm-bg: #112233; --wm-fg: #445566; --wm-accent: #778899; --wm-surface: #aabbcc; --wm-surface-hover: #ddeeff; --wm-error: #ff0000;"
)
expect(installed).to_be(true)
val effective_snapshot = active_host_wm_theme_snapshot()
expect(effective_snapshot.background_rgba).to_equal(0xFF112233u32)
expect(effective_snapshot.foreground_rgba).to_equal(0xFF445566u32)
expect(effective_snapshot.accent_rgba).to_equal(0xFF778899u32)
expect(effective_snapshot.material.window_fill_rgba).to_equal(0xFFAABBCCu32)
expect(effective_snapshot.material.inactive_title_fill_rgba).to_equal(0xFFDDEEFFu32)
expect(effective_snapshot.material_sha256).to_not_equal(package_snapshot.material_sha256)
```

</details>

#### installs the generated Aetheric snapshot through one x86_64 owner

- installs the generated Aetheric snapshot through one x86_64 owner


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the generated Aetheric snapshot through one x86_64 owner")
val source = file_read("examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl")
val install = source.index_of("install_generated_simpleos_wm_theme()")
val engine = source.index_of("var engine = create_fb_engine_sized(")
val expected_import = "use os.compositor.simpleos_wm_theme_bootstrap." +
    "{" + "install_generated_simpleos_wm_theme" + "}"
expect(source).to_contain(expected_import)
expect(install).to_be_greater_than(0)
expect(install).to_be_less_than(engine)
expect(source.contains("use common.ui.generated.aetheric_dark_theme_snapshot")).to_be(false)
expect(source.contains("apply_theme_render_snapshot_to_wm_chrome(")).to_be(false)
```

</details>

#### installs the same generated Aetheric snapshot before ARM64 compositor creation

- installs the same generated Aetheric snapshot before ARM64 compositor creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the same generated Aetheric snapshot before ARM64 compositor creation")
val source = file_read("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
val install = source.index_of("install_generated_simpleos_wm_theme()")
val mount = source.index_of("val vfs_mounted = vfs_boot_init_virtio_fat32()")
val theme_css = source.index_of("val theme_css = if vfs_mounted:")
val override = source.index_of("val theme_override_applied = if vfs_mounted:")
val framebuffer = source.index_of("val framebuffer_address = raw_alloc(")
val engine = source.index_of("var engine = create_fb_engine_sized(")
val expected_import = "use os.compositor.simpleos_wm_theme_bootstrap." +
    "{" + "install_generated_simpleos_wm_theme" + "}"
expect(source).to_contain(expected_import)
expect(source).to_contain("use os.services.vfs.vfs_init.{vfs_boot_init_virtio_fat32, g_vfs_read_file_text}")
expect(install).to_be_greater_than(0)
expect(install).to_be_less_than(framebuffer)
expect(install).to_be_less_than(engine)
expect(mount).to_be_greater_than(install)
expect(theme_css).to_be_greater_than(mount)
expect(override).to_be_greater_than(theme_css)
expect(engine).to_be_greater_than(override)
expect(source).to_contain("[theme-override] path=/THEME.CSS mount=")
```

</details>

#### installs the generated Aetheric snapshot before x86_64 compositor creation

- installs the generated Aetheric snapshot before x86_64 compositor creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the generated Aetheric snapshot before x86_64 compositor creation")
val source = file_read("examples/09_embedded/simple_os/arch/x86_64/gui_entry_desktop.spl")
val install = source.index_of("install_generated_simpleos_wm_theme()")
val mount = source.index_of("g_vfs_mounted = vfs_boot_init()")
val theme_css = source.index_of("val theme_css = if g_vfs_mounted:")
val override = source.index_of("val theme_override_applied = if g_vfs_mounted:")
val engine = source.index_of("var engine = create_fb_engine_sized(")
val expected_import = "use os.compositor.simpleos_wm_theme_bootstrap." +
    "{" + "install_generated_simpleos_wm_theme" + "}"
expect(source).to_contain(expected_import)
expect(source).to_contain("g_vfs_read_file_text")
expect(source).to_contain("vfs_boot_init()")
expect(install).to_be_greater_than(0)
expect(mount).to_be_greater_than(install)
expect(theme_css).to_be_greater_than(mount)
expect(override).to_be_greater_than(theme_css)
expect(engine).to_be_greater_than(override)
expect(source).to_contain("[theme-override] path=/THEME.CSS mount=")
```

</details>

#### installs the generated Aetheric snapshot before RV64 compositor creation

- installs the generated Aetheric snapshot before RV64 compositor creation


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("installs the generated Aetheric snapshot before RV64 compositor creation")
val source = file_read("examples/09_embedded/simple_os/arch/riscv64/gui_entry_desktop.spl")
val install = source.index_of("install_generated_simpleos_wm_theme()")
val mount = source.index_of("val vfs_mounted = vfs_boot_init_riscv64_virtio_fat32()")
val theme_css = source.index_of("val theme_css = g_vfs_read_file_text(\"/THEME.CSS\")")
val override = source.index_of("val theme_override_applied = apply_simpleos_css_theme_override(theme_css)")
val font = source.index_of("simpleos_desktop_register_selected_fonts_from_vfs()")
val engine = source.index_of("var engine = create_fb_engine_sized(")
val expected_import = "use os.compositor.simpleos_wm_theme_bootstrap." +
    "{" + "install_generated_simpleos_wm_theme" + "}"
expect(source).to_contain(expected_import)
expect(source).to_contain("use os.services.vfs.vfs_init.{vfs_boot_init_riscv64_virtio_fat32, g_vfs_read_file_text}")
expect(install).to_be_greater_than(0)
expect(mount).to_be_greater_than(install)
expect(theme_css).to_be_greater_than(mount)
expect(override).to_be_greater_than(theme_css)
expect(font).to_be_greater_than(override)
expect(engine).to_be_greater_than(font)
expect(source).to_contain("[theme-override] path=/THEME.CSS mount=")
```

</details>

#### keeps boot FAT32 THEME.CSS short-name routing for both root-case variants

- keeps boot FAT32 THEME.CSS short-name routing for both root-case variants
   - Expected: source contains `if path == "/THEME.CSS" or path == "/theme.css":`
   - Expected: source contains `return "THEME.CSS"`
   - Expected: source contains `if short_name == "THEME  CSS":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps boot FAT32 THEME.CSS short-name routing for both root-case variants")
val source = (file_read("src/os/services/vfs/vfs_boot_init.spl") + file_read("src/os/services/vfs/vfs_boot_core.spl") + file_read("src/os/services/vfs/vfs_boot_state.spl") + file_read("src/os/services/vfs/vfs_ambient_context.spl") + file_read("src/os/services/vfs/nvme_boot_runtime_owner.spl") + file_read("src/os/services/vfs/nvme_filesystem_direct_io.spl") + file_read("src/os/services/vfs/nvme_q35_lease_perf.spl") + file_read("src/os/services/vfs/direct_fat32_boot_reader.spl"))
expect(source.contains("if path == \"/THEME.CSS\" or path == \"/theme.css\":")).to_equal(true)
expect(source.contains("return \"THEME.CSS\"")).to_equal(true)
expect(source.contains("if short_name == \"THEME  CSS\":")).to_equal(true)
```

</details>

#### does not let hosted state or a package registry override the SimpleOS boot theme

- does not let hosted state or a package registry override the SimpleOS boot theme


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not let hosted state or a package registry override the SimpleOS boot theme")
val source = file_read("src/os/compositor/simpleos_wm_theme_bootstrap.spl")
expect(source).to_contain("val snapshot = fluid_light_theme_render_snapshot()")
val forbidden_active_import = "use common.ui.wm_chrome_theme." + "{" + "active_wm_theme_render_snapshot" + "}"
expect(source.contains(forbidden_active_import)).to_be(false)
expect(source.contains("use common.ui.theme_package.")).to_be(false)
```

</details>

#### projects the installed theme id without a freestanding optional pattern binding

- projects the installed theme id without a freestanding optional pattern binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("projects the installed theme id without a freestanding optional pattern binding")
val owner = file_read("src/lib/common/ui/wm_chrome_theme.spl")
val shell = file_read("src/os/desktop/shell.spl")
expect(owner).to_contain("fn active_wm_theme_id() -> text:")
expect(owner).to_contain("_active_theme_render_snapshot[0].id")
expect(shell).to_contain("val installed_theme_id = active_wm_theme_id()")
expect(shell).to_contain("if installed_theme_id != \"\":")
expect(shell.contains("if val snapshot = active_wm_theme_render_snapshot():")).to_be(false)
```

</details>

#### keeps native WM, web, taskbar, and capture consumers off the broken snapshot Option ABI

- keeps native WM, web, taskbar, and capture consumers off the broken snapshot Option ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps native WM, web, taskbar, and capture consumers off the broken snapshot Option ABI")
val sources = [
    "src/os/compositor/simple_web_window_renderer.spl",
    "src/os/compositor/wm_action_applier.spl",
    "src/os/compositor/hosted_wm_capture_evidence.spl",
    "src/app/ui.web/wm_bridge.spl",
    "src/app/ui.web/server.spl",
    "src/app/ui.web/_HostTaskbarRuntime/mode_and_layout_helpers.spl",
    "src/app/ui.web/_HostTaskbarRuntime/host_taskbar_runtime.spl"
]
for path in sources:
    val source = file_read(path)
    expect(source.contains("active_wm_theme_render_snapshot()")).to_be(false)
val capture = file_read("src/os/compositor/hosted_wm_capture_evidence.spl")
expect(capture).to_contain("active_wm_theme_snapshot_present()")
expect(capture).to_contain("active_wm_theme_snapshot_unchecked()")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/wm_theme_bootstrap_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WM theme bootstrap ownership.
- WM theme bootstrap ownership

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `00678c3c85ec4b3d13df5c2fcc0888a33aa9fe2a79617b7f1160a973bfd2fdd7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00678c3c85ec4b3d13df5c2fcc0888a33aa9fe2a79617b7f1160a973bfd2fdd7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00678c3c85ec4b3d13df5c2fcc0888a33aa9fe2a79617b7f1160a973bfd2fdd7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/os/wm_theme_bootstrap_contract_spec.spl
mirror: doc/06_spec/01_unit/os/wm_theme_bootstrap_contract_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/os/wm_theme_bootstrap_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/wm_theme_bootstrap_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/wm_theme_bootstrap_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/os/wm_theme_bootstrap_contract_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/os/wm_theme_bootstrap_contract_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs the resolved host package before backend and compositor creation' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/wm_theme_bootstrap_contract_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'prefers active state then the package-owned snapshot projection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/wm_theme_bootstrap_contract_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'installs an explicit host package through the canonical snapshot projection' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
