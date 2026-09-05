# Release Archive Layout

> Checks release workflow source resolves installed runtimes from the extracted

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Release Archive Layout

Checks release workflow source resolves installed runtimes from the extracted

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/release/release_archive_layout_spec.spl` |
| Updated | 2026-07-19 |
| Generator | `simple spipe-docgen` (Simple) |

Checks release workflow source resolves installed runtimes from the extracted
archive root and reuses the declared bootstrap runtime and launcher for fallback.

## Scenarios

### release archive layout

#### should derive installer runtime paths from the extracted archive root

- Verify release archives expose the installed runtime layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify release archives expose the installed runtime layout")
val workflow = rt_file_read_text(".github/workflows/release.yml") ?? ""

expect(workflow).to_contain("LINUX_PKG_ROOT=\"${LINUX_ARCHIVE%.spk}\"")
expect(workflow).to_contain("$LINUX_PKG_ROOT/bin/simple-runtime")
expect(workflow).to_contain("WINDOWS_PKG_ROOT=\"${WINDOWS_ARCHIVE%.spk}\"")
expect(workflow).to_contain("$WINDOWS_PKG_ROOT/bin/simple.exe")
expect(workflow.contains("if [ -f bin/simple-runtime ]; then")).to_be(false)
expect(workflow.contains("if [ -f bin/simple.exe ]; then")).to_be(false)
```

</details>

#### should reuse the bootstrap runtime and launcher in the full fallback

- Verify release archives expose the installed runtime layout


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Verify release archives expose the installed runtime layout")
val workflow = rt_file_read_text(".github/workflows/release.yml") ?? ""

expect(workflow).to_contain("needs: [check-version, build-bootstrap]")
expect(workflow).to_contain("name: bootstrap-linux-x86_64")
expect(workflow).to_contain("FULL_BOOTSTRAP_ROOT=\"${FULL_ARCHIVE%.spk}\"")
expect(workflow).to_contain("test -x \"$FULL_BOOTSTRAP_ROOT/bin/simple-runtime\"")
expect(workflow).to_contain("test -x \"$FULL_BOOTSTRAP_ROOT/bin/simple\"")
expect(workflow).to_contain("cp \"$FULL_BOOTSTRAP_ROOT/bin/simple-runtime\" \"$PKG_ROOT/bin/\"")
expect(workflow).to_contain("cp \"$FULL_BOOTSTRAP_ROOT/bin/simple\" \"$PKG_ROOT/bin/\"")
expect(workflow).to_contain("dist/simple-full-*.tar.gz.sha256")
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
