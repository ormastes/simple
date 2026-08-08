# ui_build_cli_spec

> ui_build CLI Integration Specification

<!-- sdn-diagram:id=ui_build_cli_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=ui_build_cli_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

ui_build_cli_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=ui_build_cli_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# ui_build_cli_spec

ui_build CLI Integration Specification

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | html_ui_toolchain AC-3, AC-4, AC-6, AC-8 |
| Category | Tooling |
| Status | In Progress |
| Design | doc/05_design/ui/html_ui/html_ui_toolchain.md |
| Source | `test/02_integration/app/ui_build/ui_build_cli_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

ui_build CLI Integration Specification

Overview
--------
Integration tests for `bin/simple run src/app/ui_build/main.spl` CLI.
Each `it` block uses isolated /tmp directories to avoid cross-contamination.
Commands run via `shell_output` from the repo root.

SMF stubs: compiled SMFs are currently 219-byte stubs (known gap,
doc/08_tracking/bug/emit_smf_stub_drops_module_content_2026-06-12.md). A
parallel change adds a `WARN stub smf:` line and `OK payload ... decoded`
verify line. These specs tolerate but do not require those additions. Stable
assertions: file existence, SMF first-4-bytes == `SMF\\0` (hex 534d4600),
sidecar contains form/elements, verify output contains "PASS" or "FAIL".

Examples
--------
  bin/simple run src/app/ui_build/main.spl -- build page.html -o /tmp/out --form=std
  bin/simple run src/app/ui_build/main.spl -- build page.html -o /tmp/out --form=dyn
  bin/simple run src/app/ui_build/main.spl -- verify /tmp/out/page.uib.sdn

## Scenarios

### ui_build CLI

#### std build produces an SMF with SMF\\0 magic and a sidecar with form and elements

- shell output
- make page
- ui build
- assert true
- assert true
- assert true
- assert true
- assert true
- shell output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell_output("rm -rf /tmp/ui_build_spec_std && mkdir -p /tmp/ui_build_spec_std/out")
make_page("/tmp/ui_build_spec_std")
ui_build("build /tmp/ui_build_spec_std/page.html -o /tmp/ui_build_spec_std/out --form=std")
assert_true(file_exists("/tmp/ui_build_spec_std/out/page.smf"))
assert_true(file_exists("/tmp/ui_build_spec_std/out/page.uib.sdn"))
val magic = smf_magic_hex("/tmp/ui_build_spec_std/out/page.smf")
assert_true(magic.contains("534d4600"))
val sidecar = file_read("/tmp/ui_build_spec_std/out/page.uib.sdn")
assert_true(sidecar.contains("form:"))
assert_true(sidecar.contains("elements:"))
shell_output("rm -rf /tmp/ui_build_spec_std")
```

</details>

#### dyn build produces an SMF artifact and a sidecar listing artifacts

- shell output
- make page
- ui build
- assert true
- assert true
- assert true
- shell output


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell_output("rm -rf /tmp/ui_build_spec_dyn && mkdir -p /tmp/ui_build_spec_dyn/out")
make_page("/tmp/ui_build_spec_dyn")
ui_build("build /tmp/ui_build_spec_dyn/page.html -o /tmp/ui_build_spec_dyn/out --form=dyn")
assert_true(file_exists("/tmp/ui_build_spec_dyn/out/page.smf"))
assert_true(file_exists("/tmp/ui_build_spec_dyn/out/page.uib.sdn"))
val sidecar = file_read("/tmp/ui_build_spec_dyn/out/page.uib.sdn")
assert_true(sidecar.contains("artifacts:"))
shell_output("rm -rf /tmp/ui_build_spec_dyn")
```

</details>

#### verify prints PASS on a freshly built std artifact

- shell output
- make page
- ui build
- assert true
- shell output


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell_output("rm -rf /tmp/ui_build_spec_vpass && mkdir -p /tmp/ui_build_spec_vpass/out")
make_page("/tmp/ui_build_spec_vpass")
ui_build("build /tmp/ui_build_spec_vpass/page.html -o /tmp/ui_build_spec_vpass/out --form=std")
val out = ui_build_capture("verify /tmp/ui_build_spec_vpass/out/page.uib.sdn")
assert_true(out.contains("PASS"))
shell_output("rm -rf /tmp/ui_build_spec_vpass")
```

</details>

#### verify prints FAIL after the smf artifact is truncated in a scratch copy

- shell output
- make page
- ui build
- shell output
- shell output
- shell output
- assert true
- shell output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell_output("rm -rf /tmp/ui_build_spec_vfail && mkdir -p /tmp/ui_build_spec_vfail/out")
make_page("/tmp/ui_build_spec_vfail")
ui_build("build /tmp/ui_build_spec_vfail/page.html -o /tmp/ui_build_spec_vfail/out --form=std")
# Copy to scratch so we don't poison sibling its; patch sidecar paths via sed
shell_output("cp -r /tmp/ui_build_spec_vfail/out /tmp/ui_build_spec_vfail/scratch")
shell_output("sed -i 's|/tmp/ui_build_spec_vfail/out|/tmp/ui_build_spec_vfail/scratch|g' /tmp/ui_build_spec_vfail/scratch/page.uib.sdn")
# Truncate the SMF to 10 bytes — too small for the 179-byte minimum
shell_output("dd if=/dev/zero of=/tmp/ui_build_spec_vfail/scratch/page.smf bs=1 count=10 2>/dev/null")
val out = ui_build_capture("verify /tmp/ui_build_spec_vfail/scratch/page.uib.sdn")
assert_true(out.contains("FAIL"))
shell_output("rm -rf /tmp/ui_build_spec_vfail")
```

</details>

#### theme showcase std build produces sidecar with at least 40 element entries

- shell output
- ui build
- assert true
- assert true
- assert true
- shell output


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
shell_output("rm -rf /tmp/ui_build_spec_theme && mkdir -p /tmp/ui_build_spec_theme/out")
val theme = "src/lib/common/ui/theme_html/theme_showcase.html"
ui_build("build " + theme + " -o /tmp/ui_build_spec_theme/out --form=std")
assert_true(file_exists("/tmp/ui_build_spec_theme/out/theme_showcase.smf"))
assert_true(file_exists("/tmp/ui_build_spec_theme/out/theme_showcase.uib.sdn"))
val cnt = shell_output(
    "grep -c '^  - ' /tmp/ui_build_spec_theme/out/theme_showcase.uib.sdn 2>/dev/null || echo 0"
).trim()
val n = cnt.to_i64() ?? 0
assert_true(n >= 40)
shell_output("rm -rf /tmp/ui_build_spec_theme")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Design:** [doc/05_design/ui/html_ui/html_ui_toolchain.md](doc/05_design/ui/html_ui/html_ui_toolchain.md)


</details>
