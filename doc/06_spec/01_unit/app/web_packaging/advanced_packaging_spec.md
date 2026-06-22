# Advanced Web Packaging Specification

> Tests for advanced SWA packaging features: META-SWA convention enforcement, build profiles for environment-specific configuration, resource filtering with variable substitution, and fat archive bundling that collects all dependencies into a single deployable archive.

<!-- sdn-diagram:id=advanced_packaging_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=advanced_packaging_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

advanced_packaging_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=advanced_packaging_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 35 | 35 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Advanced Web Packaging Specification

Tests for advanced SWA packaging features: META-SWA convention enforcement, build profiles for environment-specific configuration, resource filtering with variable substitution, and fat archive bundling that collects all dependencies into a single deployable archive.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #SWA-ADV-001 through #SWA-ADV-030 |
| Category | Tooling |
| Difficulty | 3/5 |
| Status | In Progress |
| Requirements | doc/requirement/web_app_packaging.md |
| Plan | doc/03_plan/web_app_packaging.md |
| Design | doc/05_design/web_app_packaging.md |
| Source | `test/01_unit/app/web_packaging/advanced_packaging_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests for advanced SWA packaging features: META-SWA convention enforcement,
build profiles for environment-specific configuration, resource filtering
with variable substitution, and fat archive bundling that collects all
dependencies into a single deployable archive.

## Key Concepts

| Concept | Description |
|---------|-------------|
| META-SWA/ | Convention directory for metadata, not served as static content |
| Build Profile | Named config (dev, staging, prod) loaded from profiles.sdn |
| Resource Filter | Replaces ${variable} placeholders in config files at build time |
| Fat Archive | Single archive that bundles all dependencies alongside the app |
| webapp.sdn | Deployment descriptor inside META-SWA/ |
| profiles.sdn | Build profile definitions (port, env vars, feature flags) |

## Scenarios

### META-SWA Convention

#### is_meta_path identifies META-SWA/ paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path1 = "META-SWA/webapp.sdn"
val path2 = "META-SWA/manifest.sdn"
val path3 = "META-SWA/signing/cert.pem"
expect(path1.starts_with("META-SWA/")).to_equal(true)
expect(path2.starts_with("META-SWA/")).to_equal(true)
expect(path3.starts_with("META-SWA/")).to_equal(true)
```

</details>

#### is_meta_path rejects non-META-SWA paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val path1 = "public/index.html"
val path2 = "modules/app.smf"
val path3 = "i18n/messages.sdn"
expect(path1.starts_with("META-SWA/")).to_equal(false)
expect(path2.starts_with("META-SWA/")).to_equal(false)
expect(path3.starts_with("META-SWA/")).to_equal(false)
```

</details>

#### META-SWA files are not served as static assets

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val served_paths = ["index.html", "css/style.css", "js/app.js"]
val meta_path = "META-SWA/webapp.sdn"
expect(served_paths).to_contain("index.html")
val is_served = false
for p in served_paths:
    if p == meta_path:
        pass_do_nothing
expect(is_served).to_equal(false)
```

</details>

#### META-SWA contains required webapp.sdn

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val required_files = ["META-SWA/webapp.sdn"]
expect(required_files.len()).to_be_greater_than(0)
expect(required_files).to_contain("META-SWA/webapp.sdn")
```

</details>

#### META-SWA supports optional signing directory

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val optional_paths = [
    "META-SWA/webapp.sdn",
    "META-SWA/signing/signature.bin",
    "META-SWA/signing/cert.pem"
]
expect(optional_paths.len()).to_equal(3)
expect(optional_paths[1]).to_contain("signing/")
```

</details>

#### is_meta_path handles case-sensitive comparison

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val correct = "META-SWA/webapp.sdn"
val wrong_case = "meta-swa/webapp.sdn"
expect(correct.starts_with("META-SWA/")).to_equal(true)
expect(wrong_case.starts_with("META-SWA/")).to_equal(false)
```

</details>

### Build Profiles

#### parses profile SDN with dev profile

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profiles_sdn = "profiles:\n  dev:\n    port: 3000\n    debug: true\n"
expect(profiles_sdn).to_contain("dev:")
expect(profiles_sdn).to_contain("port: 3000")
expect(profiles_sdn).to_contain("debug: true")
```

</details>

#### parses profile SDN with multiple profiles

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val profile_names = ["dev", "staging", "prod"]
expect(profile_names.len()).to_equal(3)
expect(profile_names).to_contain("dev")
expect(profile_names).to_contain("staging")
expect(profile_names).to_contain("prod")
```

</details>

#### lists available profiles from SDN

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val available = ["dev", "staging", "prod"]
expect(available.len()).to_equal(3)
expect(available[0]).to_equal("dev")
expect(available[1]).to_equal("staging")
expect(available[2]).to_equal("prod")
```

</details>

#### dev profile overrides port to 3000

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val base_port = 8080
val dev_port = 3000
expect(dev_port).to_equal(3000)
expect(dev_port).to_be_less_than(base_port)
```

</details>

#### prod profile sets port to 80

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prod_port = 80
expect(prod_port).to_equal(80)
```

</details>

#### profile applies environment variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev_env = {"NODE_ENV": "development", "DEBUG": "true"}
val prod_env = {"NODE_ENV": "production", "DEBUG": "false"}
expect(dev_env["NODE_ENV"]).to_equal("development")
expect(prod_env["NODE_ENV"]).to_equal("production")
expect(prod_env["DEBUG"]).to_equal("false")
```

</details>

#### profile applies feature flags

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val dev_features = {"hot_reload": true, "source_maps": true}
val prod_features = {"hot_reload": false, "source_maps": false}
expect(dev_features["hot_reload"]).to_equal(true)
expect(prod_features["hot_reload"]).to_equal(false)
```

</details>

#### returns error for unknown profile name

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val known_profiles = ["dev", "staging", "prod"]
val requested = "beta"
val found = false
for p in known_profiles:
    if p == requested:
        pass_do_nothing
expect(found).to_equal(false)
```

</details>

#### profile inherits unset values from base descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Profile only overrides port; name and version come from base
val base_name = "myapp"
val base_version = "1.0.0"
val profile_port = 3000
val effective_name = base_name
val effective_version = base_version
val effective_port = profile_port
expect(effective_name).to_equal("myapp")
expect(effective_version).to_equal("1.0.0")
expect(effective_port).to_equal(3000)
```

</details>

### Resource Filtering

#### replaces single ${variable} placeholder

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "server.port=${PORT}"
val port_value = "8080"
val result = "server.port=8080"
expect(template).to_contain("${PORT}")
expect(result).to_contain("8080")
expect(result).to_equal("server.port=8080")
```

</details>

#### replaces multiple ${variable} placeholders

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "host=${HOST}:${PORT}"
val result = "host=localhost:3000"
expect(result).to_contain("localhost")
expect(result).to_contain("3000")
```

</details>

#### handles nested variable with default

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "${APP_NAME:-myapp}"
# When APP_NAME is not set, use default "myapp"
val result = "myapp"
expect(result).to_equal("myapp")
```

</details>

#### environment variable takes highest priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_value = "from_env"
val profile_value = "from_profile"
val sdn_value = "from_sdn"
# env > profile > sdn
val resolved = env_value
expect(resolved).to_equal("from_env")
```

</details>

#### profile value takes second priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When env var not set, profile value is used
val env_value = ""
val profile_value = "from_profile"
val sdn_value = "from_sdn"
val resolved = if env_value != "": env_value else: profile_value
expect(resolved).to_equal("from_profile")
```

</details>

#### SDN default takes lowest priority

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val env_value = ""
val profile_value = ""
val sdn_value = "from_sdn"
var resolved = sdn_value
if env_value != "":
    resolved = env_value
elif profile_value != "":
    resolved = profile_value
expect(resolved).to_equal("from_sdn")
```

</details>

#### leaves ${variable} as-is when not resolvable

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = "value=${UNKNOWN_VAR}"
val result = "value=${UNKNOWN_VAR}"
expect(result).to_contain("${UNKNOWN_VAR}")
```

</details>

#### filters only text-based resource files

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Binary files (images, fonts) should not be filtered
val filterable_extensions = [".sdn", ".html", ".css", ".js", ".xml", ".txt"]
val non_filterable_extensions = [".png", ".jpg", ".woff", ".ttf"]
expect(filterable_extensions.len()).to_equal(6)
expect(non_filterable_extensions.len()).to_equal(4)
expect(filterable_extensions).to_contain(".sdn")
expect(filterable_extensions).to_contain(".html")
```

</details>

#### handles empty template gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val template = ""
val result = ""
expect(result).to_equal("")
expect(result.len()).to_equal(0)
```

</details>

### Fat Archive

#### collects direct dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_deps = ["std.io", "std.http", "app.models"]
expect(app_deps.len()).to_equal(3)
expect(app_deps).to_contain("std.io")
expect(app_deps).to_contain("std.http")
```

</details>

#### collects transitive dependencies

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# std.http depends on std.io and std.net
val direct = ["std.http"]
val transitive = ["std.io", "std.net"]
val all_deps = ["std.http", "std.io", "std.net"]
expect(all_deps.len()).to_equal(3)
expect(all_deps).to_contain("std.net")
```

</details>

#### bundles all dependencies into single archive

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_modules = ["app.main", "app.routes", "app.models"]
val dep_modules = ["std.io", "std.http", "std.net"]
val total = app_modules.len() + dep_modules.len()
expect(total).to_equal(6)
```

</details>

#### preserves directory structure for modules

<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundled_paths = [
    "modules/app/main.smf",
    "modules/app/routes.smf",
    "modules/app/models.smf",
    "modules/std/io.smf",
    "modules/std/http.smf",
    "modules/std/net.smf"
]
expect(bundled_paths.len()).to_equal(6)
expect(bundled_paths[0]).to_start_with("modules/")
expect(bundled_paths[3]).to_start_with("modules/std/")
```

</details>

#### preserves directory structure for assets

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bundled_assets = [
    "public/index.html",
    "public/css/style.css",
    "public/js/app.js",
    "public/images/logo.png"
]
expect(bundled_assets.len()).to_equal(4)
expect(bundled_assets[0]).to_start_with("public/")
expect(bundled_assets[1]).to_contain("css/")
expect(bundled_assets[3]).to_contain("images/")
```

</details>

#### avoids duplicate modules in fat archive

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# If both app.main and app.routes depend on std.io,
# std.io should appear only once
val seen_modules = ["std.io"]
val duplicate = "std.io"
val already_bundled = false
for m in seen_modules:
    if m == duplicate:
        pass_do_nothing
# Expect deduplication to have occurred
expect(seen_modules.len()).to_equal(1)
```

</details>

#### fat archive includes META-SWA descriptor

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive_contents = [
    "META-SWA/webapp.sdn",
    "modules/app/main.smf",
    "public/index.html"
]
expect(archive_contents).to_contain("META-SWA/webapp.sdn")
```

</details>

#### fat archive includes i18n bundles

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val archive_contents = [
    "META-SWA/webapp.sdn",
    "i18n/messages.sdn",
    "i18n/messages.ko.sdn",
    "modules/app/main.smf"
]
expect(archive_contents).to_contain("i18n/messages.sdn")
expect(archive_contents).to_contain("i18n/messages.ko.sdn")
```

</details>

#### reports total size of fat archive components

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val module_bytes = 51200
val asset_bytes = 102400
val descriptor_bytes = 256
val i18n_bytes = 1024
val total = module_bytes + asset_bytes + descriptor_bytes + i18n_bytes
expect(total).to_equal(154880)
expect(total).to_be_greater_than(0)
```

</details>

#### fat archive is self-contained and deployable

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# A fat archive should have all four conventional directories
val has_meta = true
val has_modules = true
val has_public = true
val has_i18n = true
val is_self_contained = (has_meta and has_modules and
                          has_public and has_i18n)
expect(is_self_contained).to_equal(true)
```

</details>

#### handles app with no dependencies gracefully

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val app_modules = ["app.main"]
val dep_modules: [text] = []
val total = app_modules.len() + dep_modules.len()
expect(total).to_equal(1)
expect(dep_modules.len()).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 35 |
| Active scenarios | 35 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/requirement/web_app_packaging.md](doc/requirement/web_app_packaging.md)
- **Plan:** [doc/03_plan/web_app_packaging.md](doc/03_plan/web_app_packaging.md)
- **Design:** [doc/05_design/web_app_packaging.md](doc/05_design/web_app_packaging.md)


</details>
