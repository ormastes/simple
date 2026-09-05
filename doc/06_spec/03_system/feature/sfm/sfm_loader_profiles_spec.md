# SFM Loader & Target Profiles

> The SFM runtime loads a `.sfm` across five target profiles — native, loader, script app, web app, mobile app. Each profile is selectable when loading and the loader reports which profile actually handled the module via `handled_profile`. This spec covers AC-6.

<!-- sdn-diagram:id=sfm_loader_profiles_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sfm_loader_profiles_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_loader_profiles_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sfm_loader_profiles_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFM Loader & Target Profiles

The SFM runtime loads a `.sfm` across five target profiles — native, loader, script app, web app, mobile app. Each profile is selectable when loading and the loader reports which profile actually handled the module via `handled_profile`. This spec covers AC-6.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFM |
| Category | Infrastructure |
| Status | Draft |
| Requirements | doc/04_architecture/language/simple_feature_module.md |
| Design | doc/05_design/simple_feature_module.md |
| Source | `test/03_system/feature/sfm/sfm_loader_profiles_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SFM runtime loads a `.sfm` across five target profiles — native, loader,
script app, web app, mobile app. Each profile is selectable when loading and the
loader reports which profile actually handled the module via `handled_profile`.
This spec covers AC-6.

## Key Concepts

| Concept | Description |
|---------|-------------|
| SfmProfile | Native / Loader / Script / Web / Mobile |
| load_sfm | Loads a `.sfm` preferring a profile; returns an SfmModule |
| SfmModule | Decoded manifest + embedded SMF bytes + the handling profile |
| handled_profile | The profile the loader used (reported back to caller) |

## Related Specifications

- [sfm_codec_spec.spl](sfm_codec_spec.spl) — the container the loader reads

## Scenarios

### SFM loader profiles

### AC-6: load across target profiles and report the handler

#### should load preferring the native profile and report native

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `native`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_native.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Native):
            Ok(mod):
                expect(profile_name(handled_profile(mod))).to_equal("native")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

#### should load preferring the loader profile and report loader

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `loader`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_loader.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Loader):
            Ok(mod):
                expect(profile_name(handled_profile(mod))).to_equal("loader")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

#### should load preferring the script profile and report script

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `script`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_script.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Script):
            Ok(mod):
                expect(profile_name(handled_profile(mod))).to_equal("script")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

#### should load preferring the web profile and report web

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `web`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_web.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Web):
            Ok(mod):
                expect(profile_name(handled_profile(mod))).to_equal("web")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

#### should load preferring the mobile profile and report mobile

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `mobile`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_mobile.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Mobile):
            Ok(mod):
                expect(profile_name(handled_profile(mod))).to_equal("mobile")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

#### should preserve the manifest through a file load

1. Err
   - Exec capture: after_step

2. Ok
   - Exec capture: after_step

3. Ok
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: mod.manifest.name equals `loadable`
   - Expected: mod.manifest.version equals `2.0.0`

4. Err
   - Exec capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path = "/tmp/sfm_loader_fields.sfm"
match write_sample(path):
    Err(e): expect("write failed: " + e).to_equal("ok")
    Ok(_):
        match load_with(path, SfmProfile.Native):
            Ok(mod):
                expect(mod.manifest.name).to_equal("loadable")
                expect(mod.manifest.version).to_equal("2.0.0")
            Err(e): expect("load failed: " + e).to_equal("ok")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/04_architecture/language/simple_feature_module.md](doc/04_architecture/language/simple_feature_module.md)
- **Design:** [doc/05_design/simple_feature_module.md](doc/05_design/simple_feature_module.md)


</details>
