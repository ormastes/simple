# use compiler.tools.lint.main unresolvable from spec location

Date: 2026-09-15
Discovered by: test-wave agent B (spec triage)

## Affected spec (left RED)
- test/01_unit/lib/nogc_sync_mut/tooling/easy_fix/duplicate_typed_arg_signature_nil_miss_spec.spl

## Observed
`use compiler.tools.lint.main` fails to resolve from the spec's directory
(std-rooted resolution only). No sibling pattern exists to copy.

## Unblock condition
Expose the lint entry through a std.* path (or document the sanctioned way
for specs to import compiler tools), then fix the import.
