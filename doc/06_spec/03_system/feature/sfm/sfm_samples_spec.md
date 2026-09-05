# SFM Sample Apps & Reuse

> The SFM infra ships sample feature modules that exercise the public API end-to-end: a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login (AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version (AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct from the samples (AC-13).

<!-- sdn-diagram:id=sfm_samples_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=sfm_samples_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_samples_spec -> std
sfm_samples_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=sfm_samples_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# SFM Sample Apps & Reuse

The SFM infra ships sample feature modules that exercise the public API end-to-end: a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login (AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version (AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct from the samples (AC-13).

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SFM |
| Category | Infrastructure |
| Status | Draft |
| Requirements | doc/04_architecture/language/simple_feature_module.md |
| Plan | N/A |
| Design | doc/05_design/simple_feature_module.md |
| Research | N/A |
| Source | `test/03_system/feature/sfm/sfm_samples_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The SFM infra ships sample feature modules that exercise the public API end-to-end:
a native arg-parser app (AC-7), a runtime log-level changer (AC-8), a web-app login
(AC-9), a version-control layer (AC-10), a UI Help/Info menu surfacing the version
(AC-11), VERSION build integration (AC-12), and an in-repo reuse consumer distinct
from the samples (AC-13).

## Key Concepts

| Concept | Description |
|---------|-------------|
| arg_parse_sample | Parses sample args via the arg-parser front-end layer |
| sfm_set_log_level | Changes the active log level at runtime, observable in output |
| web_login_attempt | Authenticates a credential; rejects invalid ones |
| vcs_status | A VCS status/commit operation consumed via the SFM infra |
| help_info_text | Help/Info menu text surfacing module + VERSION version |
| read_version_md | Build-time VERSION reader feeding manifest.version |

## Syntax

These scenarios exercise public SFM sample calls directly: `arg_parse_sample(args)`,
`sfm_set_log_level(level)`, `web_login_attempt(user, password)`, `vcs_status()`,
`help_info_text()`, `consumer_describe_module()`, and `read_version_md()`.

## Examples

The examples cover a valid login returning a token, an invalid login returning an
error message, arg parsing with `--name alice deploy`, and version text surfaced
through both Help/Info and the reuse consumer.

## Related Specifications

- [sfm_codec_spec.spl](sfm_codec_spec.spl) — manifest/codec these samples build on
- [sfm_di_authz_spec.spl](sfm_di_authz_spec.spl) — DI/authz the samples resolve through

## Scenarios

### SFM sample: arg-parser app (AC-7)

#### should parse a flag and a positional argument from sample args

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = arg_parse_sample(["--name", "alice", "deploy"])
expect(parsed.get_str("name")).to_equal("alice")
expect(parsed.positionals[0]).to_equal("deploy")
```

</details>

#### should expose the arg parser as a front-end layer entry

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = arg_parse_sample(["--verbose"])
expect(parsed.get_bool("verbose")).to_equal(true)
```

</details>

### SFM sample: log-level changer (AC-8)

#### should change the active log level at runtime

1. sfm set log level
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: sfm_get_log_level() equals `parse_debug_level()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sfm_set_log_level(parse_debug_level())
expect(sfm_get_log_level()).to_equal(parse_debug_level())
```

</details>

#### should switch back from debug to info

1. sfm set log level
   - Log capture: after_step

2. sfm set log level
   - Log capture: after_step
   - Evidence: log output verified by 1 expected check
   - Expected: sfm_get_log_level() equals `parse_info_level()`


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
sfm_set_log_level(parse_debug_level())
sfm_set_log_level(parse_info_level())
expect(sfm_get_log_level()).to_equal(parse_info_level())
```

</details>

### SFM sample: web login (AC-9)

#### should authenticate a valid credential

1. Ok
   - API capture: after_step

2. Err
   - API capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match web_login_attempt("admin", "s3cret"):
    Ok(token): expect(token.len()).to_be_greater_than(0)
    Err(e): expect("valid login rejected: " + e).to_equal("ok")
```

</details>

#### should reject an invalid credential

1. Ok
   - API capture: after_step

2. Err
   - API capture: after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
match web_login_attempt("admin", "wrong"):
    Ok(_):  expect("invalid login accepted").to_equal("ok")
    Err(e): expect(e.len()).to_be_greater_than(0)
```

</details>

### SFM sample: version-control layer (AC-10)

#### should report a VCS status through the SFM infra

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val status = vcs_status(".")
expect(status).to_contain("branch")
```

</details>

### SFM sample: UI Help/Info menu (AC-11, AC-12)

#### should surface the module info in the help menu

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = help_info_text()
expect(text).to_contain("SFM")
```

</details>

#### should surface a version string from VERSION in the help menu

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ver = read_version_md("VERSION")
val text = help_info_text()
expect(text).to_contain(ver)
```

</details>

#### should read a non-empty version string from VERSION (AC-12)

**Scenario capture:** exec after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ver = read_version_md("VERSION")
expect(ver.len()).to_be_greater_than(0)
```

</details>

### SFM reuse: in-repo consumer (AC-13)

#### should consume the public SFM API to describe a module

**Scenario capture:** api after_step


<details>
<summary>Executable SPipe</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val desc = consumer_describe_module()
expect(desc).to_contain("name")
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


## Related Documentation

- **Requirements:** [doc/04_architecture/language/simple_feature_module.md](doc/04_architecture/language/simple_feature_module.md)
- **Design:** [doc/05_design/simple_feature_module.md](doc/05_design/simple_feature_module.md)


</details>
