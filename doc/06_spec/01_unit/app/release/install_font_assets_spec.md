# Release Font Assets

> Checks installer and packaging source contracts require the registry-pinned

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Release Font Assets

Checks installer and packaging source contracts require the registry-pinned

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/release/install_font_assets_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Checks installer and packaging source contracts require the registry-pinned
immutable font bundle, root license, and notices in canonical installed/package layouts.

## Scenarios

### release installer font assets

#### should install only the preflighted immutable font bundle through one share root

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should install only the preflighted immutable font bundle through one share root
- Verify immutable font assets and notices in release layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should install only the preflighted immutable font bundle through one share root")
step("Verify immutable font assets and notices in release layouts")
val source = read_file_text("src/app/release/install.spl") ?? ""
val font_copy = source.slice(source.index_of("fn copy_font_tree"), source.index_of("fn copy_file_unchanged"))

expect(source).to_contain("copy_font_tree(src: script_dir + \"/assets/fonts\"")
expect(source.index_of("copy_font_tree(src: script_dir + \"/assets/fonts\"") < source.index_of("# Install runtime binary")).to_be(true)
expect(source).to_contain("prefix + \"/share/simple/assets/fonts\"")
expect(source).to_contain("export SIMPLE_ASSET_ROOT=\\\"$SHARE_DIR\\\"")
expect(font_copy).to_contain("selected_font_bundle_asset_pins()")
expect(font_copy).to_contain("pins.len() != 57 or files.len() != pins.len()")
expect(font_copy).to_contain("pin.path == \"assets/fonts/\" + rel")
expect(font_copy).to_contain("if not pinned: return false")
expect(font_copy).to_contain("if not rt_file_exists(source_path): return false")
expect(font_copy).to_contain("sha256_u8_hex(rt_file_read_bytes(source_path)) != pin.sha256")
expect(font_copy).to_contain("rt_file_copy(source_path, dst_file)")
expect(font_copy).to_contain("sha256_u8_hex(rt_file_read_bytes(dst_file)) != pin.sha256")
expect(font_copy.index_of("rt_file_read_bytes(source_path)") < font_copy.index_of("rt_dir_create(get_parent(dst_file)")).to_be(true)
expect(font_copy.contains("rt_file_copy(f, dst_file)")).to_be(false)
expect(source).to_contain("bundled font installation incomplete")
expect(source).to_contain("return 1")
expect(source).to_contain("if not rt_file_copy(runtime_src, runtime_dst)")
expect(source).to_contain("if not rt_file_write_text(wrapper_path, wrapper)")
expect(source).to_contain("if wrapper_chmod.2 != 0")
expect(source).to_contain("THIRD_PARTY_NOTICES.md")
expect(source).to_contain("/share/simple/LICENSE")
```

</details>

#### should stage fonts and root notices in every host release package

- should stage fonts and root notices in every host release package
- Verify immutable font assets and notices in release layouts


<details>
<summary>Executable SSpec</summary>

Runnable source: 56 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("should stage fonts and root notices in every host release package")
step("Verify immutable font assets and notices in release layouts")
val workflow = read_file_text(".github/workflows/release.yml") ?? ""
val nsis = read_file_text("config/packaging/windows/simple.nsi") ?? ""

expect(workflow).to_contain("cp -r assets \"${PKG_DIR}/\"")
expect(workflow).to_contain("cp -r assets \"$PKG_ROOT/\"")
expect(workflow).to_contain("cp -r assets/fonts staging-deb/usr/local/share/simple/assets/")
expect(workflow).to_contain("cp LICENSE THIRD_PARTY_NOTICES.md staging-deb/usr/local/share/simple/")
expect(workflow).to_contain("cp -r assets/fonts staging-win/assets/")
expect(workflow).to_contain("cp LICENSE THIRD_PARTY_NOTICES.md staging-win/")
expect(workflow).to_contain("BIN_NAME=\"simple-runtime\"")
expect(workflow).to_contain("export SIMPLE_ASSET_ROOT=\"$SCRIPT_DIR/..\"")
expect(workflow).to_contain("set \"SIMPLE_ASSET_ROOT=%~dp0..\"")
expect(workflow).to_contain("$LINUX_PKG_ROOT/bin/simple-runtime")
expect(workflow.contains("if [ -f bin/simple-runtime ]; then")).to_be(false)
expect(workflow).to_contain("export SIMPLE_ASSET_ROOT=/usr/local/share/simple")
expect(nsis).to_contain("File /r \"${SOURCE_DIR}\\assets\\fonts\\*.*\"")
expect(nsis).to_contain("File \"${SOURCE_DIR}\\THIRD_PARTY_NOTICES.md\"")
expect(nsis).to_contain("\"SIMPLE_ASSET_ROOT\" \"$INSTDIR\"")

val dist = read_file_text("src/lib/nogc_sync_mut/package/dist.spl") ?? ""
expect(dist).to_contain("[\"-r\", \"assets\", \"\{pkg_dir\}/\"]")
expect(dist).to_contain("[\"LICENSE\", \"THIRD_PARTY_NOTICES.md\", \"\{pkg_dir\}/\"]")
expect(dist).to_contain("else: \"simple-runtime\"")
expect(dist).to_contain("set SIMPLE_ASSET_ROOT=%SCRIPT_DIR%..")
expect(dist).to_contain("export SIMPLE_ASSET_ROOT=\"$SCRIPT_DIR/..\"")

for path in [
    "src/lib/nogc_sync_mut/package/build.spl",
    "src/lib/nogc_async_mut/package/build.spl",
    "src/lib/gc_async_mut/package/build.spl"
]:
    val build = read_file_text(path) ?? ""
    expect(build).to_contain("val assets_result = process_run(\"cp\", [\"-r\", \"assets\", tmp_dir])")
    expect(build).to_contain("file_copy(\"THIRD_PARTY_NOTICES.md\", tmp_dir + \"/THIRD_PARTY_NOTICES.md\")")
    expect(build).to_contain("if platform.starts_with(\"windows\"): \"simple.exe\" else: \"simple\"")
    expect(build).to_contain("bin/release/\{platform\}/\{runtime_name\}")
    expect(build).to_contain("val is_windows = platform.starts_with(\"windows\")")
    expect(build).to_contain("if is_windows: \"/bin/simple.exe\" else: \"/bin/simple-runtime\"")
    expect(build).to_contain("tmp_dir + \"/bin/simple.bat\"")
    expect(build).to_contain("set \"SIMPLE_ASSET_ROOT=%~dp0..\"")
    expect(build).to_contain("export SIMPLE_ASSET_ROOT=\"$SCRIPT_DIR/..\"")

for path in [
    "src/lib/nogc_sync_mut/package/installer/staging.spl",
    "src/lib/nogc_async_mut/package/installer/staging.spl",
    "src/lib/gc_async_mut/package/installer/staging.spl"
]:
    val staging = read_file_text(path) ?? ""
    expect(staging).to_contain("\{staging\}/usr/local/share/simple/assets/fonts/")
    expect(staging).to_contain("\{staging\}/usr/local/share/simple/THIRD_PARTY_NOTICES.md")
    expect(staging).to_contain("\{staging\}/assets/fonts/")
    expect(staging).to_contain("\{staging\}/THIRD_PARTY_NOTICES.md")
    expect(staging).to_contain("export SIMPLE_ASSET_ROOT=/usr/local/share/simple")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `47062ba2c3aa3c32f78fe82b7ff26b39db686f00c00eb143447d312874eb98c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47062ba2c3aa3c32f78fe82b7ff26b39db686f00c00eb143447d312874eb98c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47062ba2c3aa3c32f78fe82b7ff26b39db686f00c00eb143447d312874eb98c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/release/install_font_assets_spec.spl
mirror: doc/06_spec/01_unit/app/release/install_font_assets_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/release/install_font_assets_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/release/install_font_assets_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/release/install_font_assets_spec.spl:23:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should install only the preflighted immutable font bundle through one share root' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/release/install_font_assets_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should install only the preflighted immutable font bundle through one share root' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/release/install_font_assets_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should stage fonts and root notices in every host release package' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/app/release/install_font_assets_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should stage fonts and root notices in every host release package' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
