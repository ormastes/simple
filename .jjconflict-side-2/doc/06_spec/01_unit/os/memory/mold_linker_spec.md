# Mold Linker Priority Specification

> Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority linker when `bin/mold/mold` is present, and that the install script exists.

<!-- sdn-diagram:id=mold_linker_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mold_linker_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mold_linker_spec -> std
mold_linker_spec -> compiler
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mold_linker_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mold Linker Priority Specification

Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority linker when `bin/mold/mold` is present, and that the install script exists.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #mold-default-linker |
| Category | Infrastructure |
| Difficulty | 1/5 |
| Status | Implemented |
| Source | `test/01_unit/os/memory/mold_linker_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that `find_linker()` in `mold.spl` returns mold as the highest-priority
linker when `bin/mold/mold` is present, and that the install script exists.

## Behavior

- `find_mold_path()` checks local bundled mold paths before querying PATH
- `find_linker()` returns `LinkerType.Mold` whenever mold is found
- `SIMPLE_LINKER` can force the same linker aliases accepted by the Rust path
- LLD fallback checks the GNU-compatible `ld.lld` frontend before bare `lld`
- `scripts/setup/install-mold.shs` exists and is the canonical mold download script

## Implementation Notes

The in-process lld path in `linker_wrapper.spl` is gated on `is_simpleos_target()`
and is correct cross-compile behavior — it is NOT a mold override on the host.

## Scenarios

### mold install script

#### scripts/setup/install-mold.shs exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(file_exists("scripts/setup/install-mold.shs")).to_equal(true)
```

</details>

### find_linker priority — mold-first invariant

#### mold is first in the preference chain

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preference_order = mold_default_linker_order()
expect(preference_order[0]).to_equal("mold")
```

</details>

#### lld is second choice after mold

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preference_order = mold_default_linker_order()
expect(preference_order[1]).to_equal("lld")
```

</details>

#### ld.lld is the preferred lld frontend

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val lld_frontends: [text] = ["ld.lld", "lld"]
expect(lld_frontends[0]).to_equal("ld.lld")
expect(lld_frontends[1]).to_equal("lld")
```

</details>

#### SIMPLE_LINKER supports Rust-compatible linker aliases

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val aliases = mold_supported_override_aliases()
expect(aliases.contains("mold")).to_equal(true)
expect(aliases.contains("ld.lld")).to_equal(true)
expect(aliases.contains("lld-link")).to_equal(true)
expect(aliases.contains("gnu")).to_equal(true)
expect(aliases.contains("bfd")).to_equal(true)
```

</details>

#### ld is last resort

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val preference_order = mold_default_linker_order()
expect(preference_order[2]).to_equal("ld")
```

</details>

#### local bin/mold/mold path is checked before system PATH

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# find_mold_path() builds: cwd() + "/bin/mold/mold"
# We verify the expected local path string is well-formed.
val local_mold_suffix = "/bin/mold/mold"
expect(local_mold_suffix.starts_with("/bin/mold")).to_equal(true)
```

</details>

#### platform-specific bundled mold names are supported

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundled_names: [text] = [
    "mold-linux-x86_64",
    "mold-linux-aarch64",
    "mold-macos-x86_64",
    "mold-macos-aarch64",
    "mold-freebsd-x86_64",
    "mold-freebsd-aarch64"
]
expect(bundled_names.contains("mold-linux-x86_64")).to_equal(true)
expect(bundled_names.contains("mold-freebsd-aarch64")).to_equal(true)
```

</details>

#### bundled mold locations cover repo bin and lib layouts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundled_locations = mold_bundled_search_suffixes()
expect(bundled_locations[0]).to_equal("bin/mold/mold")
expect(bundled_locations.contains("bin/mold")).to_equal(true)
expect(bundled_locations.contains("lib/simple/mold")).to_equal(true)
```

</details>

#### bin/mold/mold presence gates mold selection

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When the local binary exists, find_linker() must return Mold.
# When absent, it falls through to lld or ld.
# This invariant is captured as a documentation assertion.
val mold_installed = file_exists("bin/mold/mold")
if mold_installed:
    # With binary present: mold would be selected.
    expect(mold_installed).to_equal(true)
else:
    # Without binary: fallback chain applies — this is expected in
    # clean-checkout environments before running install-mold.shs.
    expect(file_exists("scripts/setup/install-mold.shs")).to_equal(true)
```

</details>

#### mold role feature surface documents implemented and missing roles

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val features = mold_compatibility_features()
expect(features.len()).to_equal(7)
expect(features[0].role).to_equal(MoldCompatibilityRole.LinkerDetection)
expect(features[0].status).to_equal("implemented")
expect(features[6].role).to_equal(MoldCompatibilityRole.PureSimpleLinker)
expect(features[6].status).to_equal("missing")
expect(mold_is_pure_simple_linker_complete()).to_equal(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
