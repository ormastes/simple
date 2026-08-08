# App Namespace Specification

> <details>

<!-- sdn-diagram:id=app_namespace_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=app_namespace_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

app_namespace_spec -> std
app_namespace_spec -> os
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=app_namespace_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# App Namespace Specification

## Scenarios

### SimpleOS app namespace contract

#### exposes the default process filesystem paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = app_namespace_default()
expect(ns.root).to_equal("/")
expect(ns.cwd).to_equal("/")
expect(ns.mount_view).to_equal(["/bin", "/usr/bin", "/sys/apps", "/lib", "/usr/lib", "/tmp", "/home", "/svc"])
expect(ns.cap_dirs).to_equal(["/svc"])
expect(ns.library_paths).to_equal(["/lib", "/usr/lib", "/usr/lib/simple"])
```

</details>

#### resolves relative paths from each process cwd

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base = app_namespace_default()
val home_ns = app_namespace_with_cwd(base, "/home/alice")
val tmp_ns = app_namespace_with_cwd(base, "/tmp")

expect(home_ns != nil).to_equal(true)
expect(tmp_ns != nil).to_equal(true)
expect(app_namespace_resolve_path(home_ns.unwrap(), "notes.txt")).to_equal(Some("/home/alice/notes.txt"))
expect(app_namespace_resolve_path(tmp_ns.unwrap(), "notes.txt")).to_equal(Some("/tmp/notes.txt"))
```

</details>

#### prevents dot-dot from escaping the process root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = app_namespace_default()
expect(app_namespace_resolve_path(ns, "../../bin/sh")).to_equal(nil)
expect(app_namespace_resolve_path(ns, "/tmp/../../bin/sh")).to_equal(nil)
expect(app_namespace_resolve_path(ns, "/tmp/../bin/sh")).to_equal(Some("/bin/sh"))
```

</details>

#### keeps resolved paths under a non-default root

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = app_namespace_create("/sys/apps/browser_demo", "/home/app", ["/home", "/lib"], ["/svc"], ["/lib"])
expect(ns != nil).to_equal(true)
expect(app_namespace_resolve_path(ns.unwrap(), "state.db")).to_equal(Some("/sys/apps/browser_demo/home/app/state.db"))
expect(app_namespace_resolve_path(ns.unwrap(), "../../../escape")).to_equal(nil)
```

</details>

#### orders library lookup by process paths before explicit manifest paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = app_namespace_default()
val candidates = app_namespace_library_candidates(ns, "libui.smf", ["/sys/apps/browser_demo/lib/libui.smf", "local/libextra.smf"])

expect(candidates).to_equal([
    "/lib/libui.smf",
    "/usr/lib/libui.smf",
    "/usr/lib/simple/libui.smf",
    "/sys/apps/browser_demo/lib/libui.smf",
    "/local/libextra.smf"
])
```

</details>

#### resolves explicit absolute library names before manifest extras

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ns = app_namespace_default()
val candidates = app_namespace_library_candidates(ns, "/sys/apps/browser_demo/lib/libui.smf", ["/usr/lib/libfallback.smf"])

expect(candidates).to_equal([
    "/sys/apps/browser_demo/lib/libui.smf",
    "/usr/lib/libfallback.smf"
])
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/loader/app_namespace_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- SimpleOS app namespace contract

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
