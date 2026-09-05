# Startup dynamic-loading environment acceptance

> This executable acceptance manual is for compiler, interpreter, loader, and

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Startup dynamic-loading environment acceptance

This executable acceptance manual is for compiler, interpreter, loader, and

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md |
| Design | doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md |
| Research | doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md |
| Source | `test/03_system/app/simple/feature/startup_dynload_env_acceptance_spec.spl` |
| Updated | 2026-08-25 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

This executable acceptance manual is for compiler, interpreter, loader, and
release engineers. It proves that environment-selected extensions run before
application `main` and that checked dynSMF configuration is reusable without
application-level platform branches.

**Requirements:** N/A
**Plan:** doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md
**Design:** doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md
**Research:** doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md

## Overview

Two configuration layers intentionally coexist. `SIMPLE_STARTUP_ASPECTS`
selects raw hosted libraries for the true pre-main ABI. `SIMPLE_DYNLOAD_CONFIG`
and `SIMPLE_DYNLOAD` select checked dynSMF components through the reusable
application startup owner.

## Syntax and examples

`SIMPLE_STARTUP_ASPECTS=/path/a.so:/path/b.so app` loads native packs in list
order. `SIMPLE_DYNLOAD_CONFIG=profiles/ci.sdn` selects a checked configuration;
`SIMPLE_DYNLOAD=compiler_ext:presence=on,activation=startup` overlays one
component. Windows uses the platform delimiter behind the runtime boundary.

## Scope and assumptions

The host needs a C compiler and the repository runtime archive used by
`check-startup-aspect-dynload.shs`. The native gate builds real shared-library
fixtures. The remaining scenarios exercise platform-neutral configuration;
native Windows, macOS, and FreeBSD executions remain tracked in TODO 837.

## Primary workflow and evidence

Run this spec from the repository root. A passing receipt contains three
executed scenarios and the nested native gate reports exactly 13 checked
cases. The gate proves environment ordering, initialization before `main`,
missing-library and missing-symbol rejection, nonzero initializer rejection,
CLI composition, and the hard `--` boundary.

## Recovery and troubleshooting

If the native scenario cannot build, first run
`sh scripts/check/check-startup-aspect-dynload.shs` and inspect its retained
compile/link path. A missing runtime archive is absence of evidence, not a
skip. Configuration failures should name `malformed_env_entry` rather than
silently selecting defaults.

## Traceability and generation history

REQ-APP-STARTUP-001 is bound inside every executable scenario. This manual is
generated from the canonical spec and was introduced with TODO 837.

## Scenarios

### startup dynload environment acceptance

#### loads real environment-selected packs before main and fails closed

- Run the native environment and CLI startup-extension acceptance gate
   - Log capture: after_step
   - Evidence: log output verified by 2 expected checks
   - Expected: status equals `success_status`
   - Expected: stderr equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-STARTUP-001
step("Run the native environment and CLI startup-extension acceptance gate")
val (stdout, stderr, status) = process_run(
    "sh", ["scripts/check/check-startup-aspect-dynload.shs"])
val success_status = 0
val native_case_count = 13
expect(status).to_equal(success_status)
expect(stderr).to_equal("")
expect(stdout).to_contain("PASS — " + native_case_count.to_text() + " case(s) checked")
expect(stdout).to_contain("SIMPLE_STARTUP_ASPECTS")
```

</details>

#### selects config from the environment and lets ordered CLI settings win

- Resolve SIMPLE_DYNLOAD_CONFIG and SIMPLE_DYNLOAD without OS branches
   - Protocol capture: after_step
   - Evidence: protocol response verified by 10 expected checks
   - Expected: options.ok is true
   - Expected: options.config_path equals `profiles/ci.sdn`
   - Expected: options.explicit_config is true
   - Expected: config.ok is true
   - Expected: config.settings.len() equals `selected_extension_count`
   - Expected: config.settings[0].library_id equals `compiler_ext`
   - Expected: config.settings[0].presence equals `dynsmf_presence_off()`
   - Expected: config.settings[1].library_id equals `loader_ext`
   - Expected: config.settings[1].presence equals `dynsmf_presence_on()`
   - Expected: config.settings[1].activation equals `dynsmf_activation_startup()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-STARTUP-001
step("Resolve SIMPLE_DYNLOAD_CONFIG and SIMPLE_DYNLOAD without OS branches")
val options = dynsmf_startup_options_from_values(
    ["--dynload=compiler_ext:presence=off"],
    "profiles/ci.sdn",
    "compiler_ext:presence=on,activation=startup;loader_ext:presence=on,activation=startup")
expect(options.ok).to_equal(true)
expect(options.config_path).to_equal("profiles/ci.sdn")
expect(options.explicit_config).to_equal(true)

val config = dynsmf_dynload_settings_from_values(
    acceptance_manifest(), "", options.settings_text)
expect(config.ok).to_equal(true)
val selected_extension_count = 2
expect(config.settings.len()).to_equal(selected_extension_count)
expect(config.settings[0].library_id).to_equal("compiler_ext")
expect(config.settings[0].presence).to_equal(dynsmf_presence_off())
expect(config.settings[1].library_id).to_equal("loader_ext")
expect(config.settings[1].presence).to_equal(dynsmf_presence_on())
expect(config.settings[1].activation).to_equal(dynsmf_activation_startup())
```

</details>

#### honors the argument boundary and rejects malformed environment entries

- Keep application arguments isolated from startup extension policy
   - Protocol capture: after_step
   - Evidence: protocol response verified by 4 expected checks
   - Expected: bounded.ok is true
   - Expected: bounded.settings_text equals `compiler_ext:presence=on`
   - Expected: malformed.ok is false
   - Expected: malformed.settings.len() equals `rejected_setting_count`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-STARTUP-001
step("Keep application arguments isolated from startup extension policy")
val bounded = dynsmf_startup_options_from_values(
    ["--", "--dynload=compiler_ext:presence=off"],
    "", "compiler_ext:presence=on")
expect(bounded.ok).to_equal(true)
expect(bounded.settings_text).to_equal("compiler_ext:presence=on")

val malformed = dynsmf_dynload_settings_from_values(
    acceptance_manifest(), "", "compiler_ext presence=on")
expect(malformed.ok).to_equal(false)
expect(malformed.reason).to_contain("malformed_env_entry")
val rejected_setting_count = 0
expect(malformed.settings.len()).to_equal(rejected_setting_count)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** `doc/03_plan/compiler/startup_performance/startup_perf_plan_2026-08-17.md`
- **Design:** `doc/05_design/language/aop/aspect_facet_dynload_smf_pack_design_2026-08-04.md`
- **Research:** `doc/01_research/compiler/startup_perf/aspect_dynload_startup_loader_perf_research_2026-08-19.md`


</details>
