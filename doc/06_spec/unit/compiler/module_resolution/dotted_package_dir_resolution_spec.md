# Dotted Package Directory Resolution

> This repository names roughly twenty source directories with a literal dot in

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Dotted Package Directory Resolution

This repository names roughly twenty source directories with a literal dot in

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Implemented |
| Source | `test/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

This repository names roughly twenty source directories with a literal dot in
the directory name -- `src/app/package.registry/`, `src/app/ui.chromium/`,
`src/app/ffi_gen.templates/`, and `src/app/ui.chromium.acid2/` among them. A
module inside such a directory is imported with an ordinary dotted module path
(`app.package.registry.config`), so the resolver has to decide, for each dot,
whether it separates two directories or is part of one directory's name.

The audience is anyone changing module resolution in either compiler. Both must
agree on this convention: the pure-Simple driver handles it through a rewrite
table in `src/compiler/80.driver/driver_source_loading.spl`, and the Rust seed
handles it in `interpreter_module/path_resolution.rs`.

## Scope and Preconditions

These scenarios import real modules from real dotted directories in this tree.
They need no fixtures, no network, and no build products -- if the import
resolves, the module's own functions are callable and are called here.

## Primary Workflow

An import naming a dotted directory resolves to the module inside it, and the
value that module returns is usable. The observable outcome is a real
configuration record, not a boolean that the import "worked".

## Recovery and Troubleshooting

A failure here reads as `semantic: Cannot resolve module: <path>` and the
example never runs. That is a resolver defect, not a defect in the imported
module. It is fixed in the resolver -- never by renaming the directory, which
would diverge this tree to suit one binary.

## Compatibility and Limitations

The seed half of this behavior is Rust code, so a seed older than the fix still
fails these scenarios until it is rebuilt and redeployed.

## Scenarios

### Dotted package directory resolution

#### loads a module from a dotted directory and returns its real value

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- loads a module from a dotted directory and returns its real value
- Import app.package.registry.config, whose directory is literally named package.registry
- Ask the imported module for the default registry configuration
- Confirm the value came from the real module, not an empty stand-in
   - Expected: cfg.registry_url equals `ghcr.io/simple-lang`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("loads a module from a dotted directory and returns its real value")
step("Import app.package.registry.config, whose directory is literally named package.registry")
step("Ask the imported module for the default registry configuration")
val cfg = default_config()

step("Confirm the value came from the real module, not an empty stand-in")
expect(cfg.registry_url).to_equal("ghcr.io/simple-lang")
expect(cfg.cache_dir).to_contain(".simple/cache/registry")
expect(cfg.credentials_path).to_contain("credentials.sdn")
```

</details>

#### keeps the dotted segments joined rather than reading them as nested directories

- keeps the dotted segments joined rather than reading them as nested directories
- Resolve the same module again and read a field whose value is built by the module itself
- A resolver that split package.registry into package/registry would never reach this module


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the dotted segments joined rather than reading them as nested directories")
step("Resolve the same module again and read a field whose value is built by the module itself")
val cfg = default_config()

step("A resolver that split package.registry into package/registry would never reach this module")
expect(cfg.index_url).to_contain("://")
expect(cfg.registry_url).to_not_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-MODRES-DOTTED-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `68a7ecd99c789d61ef3d0bc0073123f47bea4e7cd0b0d8fe92e8992d900220cb`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `68a7ecd99c789d61ef3d0bc0073123f47bea4e7cd0b0d8fe92e8992d900220cb`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `68a7ecd99c789d61ef3d0bc0073123f47bea4e7cd0b0d8fe92e8992d900220cb`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl
mirror: doc/06_spec/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=80 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=90; blocker cap makes effective=49
doc/06_spec/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'loads a module from a dotted directory and returns its real value' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/module_resolution/dotted_package_dir_resolution_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the dotted segments joined rather than reading them as nested directories' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
