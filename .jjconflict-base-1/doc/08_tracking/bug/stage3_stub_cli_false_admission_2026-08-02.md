# Stage 3 stub CLI false admission

## Status

Fixed in the Stage 4 operating contract; no compiler rebuild was performed.

## Reproduction

An ad-hoc Stage 3 refresh asked the bootstrap compiler to build
`src/app/cli/main.spl` with `--source ... --entry-closure`, but omitted
`SIMPLE_NO_STUB_FALLBACK=1`. The build reported `1505 compiled, 0 cached, 0
failed` and linked an 8.9 MiB executable while also reporting `Generating 635
stub functions for unresolved symbols`.

The artifact hash was
`3b69c4fd3271a144885ccbc34f1728077c87266b8a82239a6a4246e55b46d524`.
It was a complete ELF executable, not a truncated file, but it was not an
admissible Stage 3 bootstrap compiler: `--version` printed `Simple v1.0.0-beta`,
and both `run` and `-c` fell through successfully without executing work. Its
Stage 4 invocation consequently failed immediately with `MIR module has no
functions`.

## Root cause

The manual refresh bypassed three canonical contracts already implemented by
`bootstrap-from-scratch.sh`: Stage 3 uses `bootstrap_main.spl`, disables stub
fallback, and must pass `bootstrap_stage_sanity`. The local guard checked only
the native-build exit status, generic failure markers, and executable-file
existence. It did not reject positive stub-generation output or the wrong CLI
identity.

## Prevention

The Stage 4 lane plan now makes the canonical entry, strict-stub setting, log
rejection, bootstrap identity, unsupported-command behavior, frontend
admission, and stable candidate hash mandatory for every manual Stage 3
refresh. `stage4_manual_stage3_admission_contract_spec.spl` locks those rules.
