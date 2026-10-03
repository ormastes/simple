# Test Runner Source Owner Specification

Source: `test/01_unit/app/test_runner_new/runner_source_owner_spec.spl`

## Scenarios

1. Daemon protocol tags come from their defining `types.spl` module.
2. Assurance profile normalization comes from its defining policy module.
3. The MC/DC evidence parser is imported from the report gate that defines it.
4. Dependency graph persistence and file probes use the existing file facades.

The spec reads production source files and checks owner contracts. It does not
replace a source-bound native runner build, which is pending for both backends.
