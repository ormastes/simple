# Wrapper Generator

**Status:** Implemented

---

## Overview

`simple wrapper-gen` currently generates plugin-manifest scaffolding for the SFFI plugin flow.

Given a `.wrapper_spec` file, it:

- parses the wrapper spec
- derives the exported `rt_*` symbol list
- emits a `manifest.sdn`
- emits a `wrapper_info.txt` summary

This is the manifest/scaffold stage of the larger three-tier SFFI workflow. It does **not** currently generate the older tiered glue/class output described in earlier planning docs.

---

## Quick Start

```bash
# Preview generated manifest and summary
simple wrapper-gen examples/regex.wrapper_spec --dry-run

# Write scaffold files to the default plugin output dir
simple wrapper-gen examples/regex.wrapper_spec

# Write scaffold files to a custom output dir
simple wrapper-gen examples/regex.wrapper_spec --output=.build/plugins/regex
```

---

## Output

Default output directory:

```text
.build/plugins/<spec-name>/
```

Files written:

- `manifest.sdn`
- `wrapper_info.txt`

Example manifest:

```sdn
plugins:
    -
        name: regex
        library: .build/plugins/regex/libsimple_regex_ffi.so
        version: "0.1.0"
        functions: [rt_regex_new, rt_regex_is_match]
```

Example summary:

```text
wrapper: regex
lang: rust
library: libsimple_regex_ffi.so
output_dir: .build/plugins/regex
functions: rt_regex_new, rt_regex_is_match
```

---

## Command Options

| Option | Description |
|--------|-------------|
| `--dry-run` | Print `manifest.sdn` and `wrapper_info.txt` without writing files |
| `--output=DIR` | Output directory override |
| `--verbose` | Print parsed wrapper-spec details |
| `--verify` | Reserved for follow-on verification flow |
| `-h`, `--help` | Show help |

---

## Wrapper Spec Notes

The implemented command reads the existing `.wrapper_spec` format used by `src/app/wrapper_gen/spec_parser.spl`.

Current fields used by manifest generation:

- `name`
- `version`
- `lang`
- `functions`
- `methods`

Exported symbol naming:

- free function `new` in wrapper `regex` -> `rt_regex_new`
- method `is_match` in wrapper `regex` -> `rt_regex_is_match`

---

## Plugin Workflow

Typical flow:

```bash
# 1. Generate manifest scaffold
simple wrapper-gen examples/regex.wrapper_spec

# 2. Install generated manifest into the plugin registry
simple plugin install .build/plugins/regex/manifest.sdn

# 3. Inspect installed plugins
simple plugin list
```

Remove a plugin:

```bash
simple plugin remove regex
```

---

## Related

- `doc/02_requirements/feature/usage/sffi_bidirectional_interop.md`
- `doc/05_design/phase4_sffi_implementation_plan.md`
- `doc/05_design/sffi_bidirectional_interop.md`
- `doc/09_report/2026/03/sffi_bidirectional_interop_completion_2026-03-30.md`
