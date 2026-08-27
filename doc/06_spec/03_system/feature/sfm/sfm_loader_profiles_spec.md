# SFM Loader & Target Profiles

> The SFM runtime loads a `.sfm` across five target profiles — native, loader, script app, web app, mobile app. Each profile is selectable when loading and the loader reports which profile actually handled the module via `handled_profile`. This spec covers AC-6.

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
| Updated | 2026-08-26 |
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

- should load preferring the native profile and report native
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load preferring the native profile and report native")
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

- should load preferring the loader profile and report loader
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `loader`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load preferring the loader profile and report loader")
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

- should load preferring the script profile and report script
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `script`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load preferring the script profile and report script")
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

- should load preferring the web profile and report web
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `web`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load preferring the web profile and report web")
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

- should load preferring the mobile profile and report mobile
   - Exec capture: after_step
   - Evidence: execution result verified by 1 expected check
   - Expected: profile_name(handled_profile(mod)) equals `mobile`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should load preferring the mobile profile and report mobile")
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

- should preserve the manifest through a file load
   - Exec capture: after_step
   - Evidence: execution result verified by 2 expected checks
   - Expected: mod.manifest.name equals `loadable`
   - Expected: mod.manifest.version equals `2.0.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should preserve the manifest through a file load")
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

- **Requirements:** `doc/04_architecture/language/simple_feature_module.md`
- **Design:** `doc/05_design/simple_feature_module.md`


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b976d16c792b60c531144e809e77756e491c7ccc500e5644f4714006f1bd4e5e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b976d16c792b60c531144e809e77756e491c7ccc500e5644f4714006f1bd4e5e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b976d16c792b60c531144e809e77756e491c7ccc500e5644f4714006f1bd4e5e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/feature/sfm/sfm_loader_profiles_spec.spl
mirror: doc/06_spec/03_system/feature/sfm/sfm_loader_profiles_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/sfm/sfm_loader_profiles_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/sfm/sfm_loader_profiles_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:90:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load preferring the native profile and report native' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should load preferring the native profile and report native' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load preferring the loader profile and report loader' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should load preferring the loader profile and report loader' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:116:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load preferring the script profile and report script' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should load preferring the script profile and report script' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:129:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load preferring the web profile and report web' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:142:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should load preferring the mobile profile and report mobile' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/feature/sfm/sfm_loader_profiles_spec.spl:155:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve the manifest through a file load' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
