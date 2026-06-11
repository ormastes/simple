# Fixed Backend Success Specification

> 1. fail

<!-- sdn-diagram:id=fixed_backend_success_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=fixed_backend_success_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

fixed_backend_success_spec -> app
fixed_backend_success_spec -> compiler
fixed_backend_success_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=fixed_backend_success_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Fixed Backend Success Specification

## Scenarios

### Fixed backend success path

#### links a valid library module when --fixed-be is enabled

1. fail
2. delete if exists
3. delete if exists
4. delete if exists
5. delete if exists
   - Expected: rt_file_write_text(src_path, "int main(void) { return 0; }\n") is true
6.   = shell
7. fail
8. var builder = LibSmfBuilder new
   - Expected: builder.add_module_data_with_object("pkg/fixed_backend", smf_bytes, object_bytes).is_ok() is true
   - Expected: builder.write(lib_path).is_ok() is true
9. extra flags: cfg extra flags push
   - Expected: link_result.is_ok() is true
   - Expected: link_result.unwrap() equals `out_path`
   - Expected: rt_file_exists(out_path) is true
10. delete if exists
11. delete if exists
12. delete if exists
13. delete if exists
14.   = shell


<details>
<summary>Executable SSpec</summary>

Runnable source: 49 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tmpdir = shell("mktemp -d").stdout.trim()
if tmpdir == "":
    fail("failed to create a temporary directory")

val src_path = "{tmpdir}/fixed_backend_fixture.c"
val obj_path = "{tmpdir}/fixed_backend_fixture.o"
val lib_path = "{tmpdir}/fixed_backend_fixture.lsm"
val out_path = "{tmpdir}/fixed_backend_fixture.out"

delete_if_exists(src_path)
delete_if_exists(obj_path)
delete_if_exists(lib_path)
delete_if_exists(out_path)

expect(rt_file_write_text(src_path, "int main(void) { return 0; }\n")).to_equal(true)

val compile = shell("cc -c -O0 -fPIC -fPIE -o '{obj_path}' '{src_path}' 2>&1")
if compile.exit_code != 0:
    _ = shell("rm -rf '{tmpdir}' >/dev/null 2>&1 || true")
    fail("cc failed: {compile.stdout}{compile.stderr}")

val object_bytes = file_read_bytes(obj_path)
val smf_bytes = build_fixed_backend_smf(object_bytes)

var builder = LibSmfBuilder.new()
expect(builder.add_module_data_with_object("pkg/fixed_backend", smf_bytes, object_bytes).is_ok()).to_equal(true)
expect(builder.write(lib_path).is_ok()).to_equal(true)

val cfg = NativeLinkConfig.default()
val fixed_cfg = NativeLinkConfig(
    libraries: cfg.libraries,
    library_paths: cfg.library_paths,
    runtime_path: "none",
    pie: cfg.pie,
    debug: cfg.debug,
    verbose: cfg.verbose,
    extra_flags: cfg.extra_flags.push("--fixed-be")
)

val link_result = link_to_native([lib_path], out_path, fixed_cfg)
expect(link_result.is_ok()).to_equal(true)
expect(link_result.unwrap()).to_equal(out_path)
expect(rt_file_exists(out_path)).to_equal(true)

delete_if_exists(src_path)
delete_if_exists(obj_path)
delete_if_exists(lib_path)
delete_if_exists(out_path)
_ = shell("rm -rf '{tmpdir}' >/dev/null 2>&1 || true")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/linker/fixed_backend_success_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Fixed backend success path

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
