# Module Import New Submodule Specification

> 1.  run and check

<!-- sdn-diagram:id=module_import_new_submodule_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=module_import_new_submodule_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

module_import_new_submodule_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=module_import_new_submodule_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Module Import New Submodule Specification

## Scenarios

### Module Import - Compiled-In Package

#### existing functions (baseline)

#### imports existing std.cli_output function via init

1.  run and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check("baseline_init_import.spl", "baseline init import")
```

</details>

#### imports existing std.cli_output submodule directly

1.  run and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check("baseline_direct_import.spl", "baseline direct import")
```

</details>

#### new submodule file in compiled-in package

#### can load new spl file without parse errors (run directly)

1.  run setup probe direct and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_direct_and_check()
```

</details>

#### can import function from new submodule via direct path

1.  run setup probe and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_and_check("probe_direct_import.spl", "New submodule direct import fails")
```

</details>

#### buffer.spl (the actual module we need)

#### can import buffer_start via direct submodule path

1.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_direct_import.spl", "buffer.spl direct import fails")
```

</details>

#### can import log_print via direct submodule path

1.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_logprint_import.spl", "buffer.spl log_print import fails")
```

</details>

#### can import buffer functions via init reexport

1.  run and check known bug


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_and_check_known_bug("buffer_init_import.spl", "buffer.spl init re-export fails")
```

</details>

#### fresh non-compiled package (control test)

#### can import from a completely new package via direct path

1.  run setup fresh and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_fresh_and_check("fresh_pkg_direct_import.spl", "Fresh package direct import")
```

</details>

#### can import from a completely new package via init

1.  run setup fresh and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_fresh_and_check("fresh_pkg_init_import.spl", "Fresh package init import")
```

</details>

#### module loading diagnostics

#### buffer.spl is found by resolver (not module-not-found)

1.  run diag module loading


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_diag_module_loading()
```

</details>

#### extern fn in module does not prevent function registration

1.  run setup probe extern and check


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
if not _can_run:
    expect(_can_run).to_equal(false)
else:
    _run_setup_probe_extern_and_check()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/03_system/compiler/module_import/module_import_new_submodule_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Module Import - Compiled-In Package

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
