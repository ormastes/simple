# `bin/simple lint` dies with `string index out of bounds` on `*_spec.spl` files

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-4 while running the mandated "lint on touched .spl
  files" gate
- Severity: the lint gate cannot be run on any spec file, so spec changes go
  unlinted. Lint-only; the same files RUN clean (`bin/simple test` green).
- Binary: `bin/simple` -> `bin/release/aarch64-unknown-linux-gnu/simple`
  (Rust seed), sha256 `3d120a6f9ab5704b...`

## Symptom

    $ bin/simple lint test/01_unit/compiler/driver/assign_type_optional_payload_source_spec.spl
    error: semantic: string index out of bounds: index is 1809 but length is 1809
      (preview="# Purpose and audience: executable specification evidence fo")

The index always equals the length, and the length is the file size minus its
trailing newline — an off-by-one reading the file, at or just past the end.

## Not caused by any one file

Reproduced on three files of different sizes, one of them untouched by this lane
and long-standing in the tree:

| file | bytes | reported |
|---|---|---|
| `assign_type_optional_payload_source_spec.spl` (pre-existing, untouched) | 1811 | `index is 1809 but length is 1809` |
| `native_noop_request_env_unset_fallback_spec.spl` (this lane) | 2710 | `index is 2708 but length is 2708` |
| `bootstrap_fixed_entry_requires_requested_module_spec.spl` (this lane) | 3610 | `index is 3608 but length is 3608` |

The untouched control is what establishes this as a linter defect rather than
anything about the new specs.

## Scope not established

Whether this is specific to `*_spec.spl`, to the `# Purpose and audience:`
header these files share, or to any file whose last line lacks something the
lexer expects, was NOT determined — all three samples share both properties.
Bisect that before attempting a fix. Non-spec `.spl` files under
`src/compiler/80.driver/` lint cleanly in the same session, so it is not a
general lint failure.
