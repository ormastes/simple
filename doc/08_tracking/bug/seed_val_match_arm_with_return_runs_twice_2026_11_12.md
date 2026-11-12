# Seed interpreter runs a `val x = match` Err arm twice

- id: seed_val_match_arm_with_return_runs_twice_2026_11_12
- status: open
- severity: P2 (silent double side effects)
- found: 2026-11-12, lane work/t32-cli-pub-20261112
- binary: phase-1 seed `C:/dev/wt/p1-20261112/src/compiler_rust/target/bootstrap/simple.exe`

## Symptom

In `examples/10_tooling/trace32_tools/t32_cli/mod.spl` `t32_cli_main`, this
block ran every statement of the `Err` arm twice, one after the other. It
added two history records instead of one and printed the JSON error twice:

```
val dispatch_args = match prepare_access_args(args):
    Err(access_error):
        record_t32_access_failure(access_error)
        print_typed_access_error(access_error, true)
        return t32_access_exit_code
    Ok(prepared): prepared
```

Trace evidence: debug prints in that block showed `prepare` once, then
`arm-enter, arm-enter, arm-after-record, arm-after-record, <json>, <json>`.
`access_cli_grammar_spec.spl` caught it with "expected 4 to equal 2" on
`MCP_T32_HISTORY.len()`.

## Repro status

These standalone single-file reductions did NOT reproduce it (hits=1):
`?` propagation, a class error payload, module-global return value, and a
blank line after an early return. The trigger seems to need the cross-module
shape: app symlinked package, imported `AccessError`, `export use` re-export
in the same module. A minimal repro is still owed.

## Workaround (landed)

The code now uses a statement-form `match` and assigns
`dispatch_args = prepared` in the `Ok` arm. It is tagged
`@workaround bug=seed_val_match_arm_with_return_runs_twice_2026_11_12`.
