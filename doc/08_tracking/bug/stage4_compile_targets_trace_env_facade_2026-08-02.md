# Stage 4 compile-target trace environment facade

## Status

- Claimed: 2026-08-02
- Owner: Codex `stage4_bootstrap_close` fix lane B
- State: fixed and regression-covered

## Exact reproduction

The canonical strict full-CLI bootstrap completed Stage 2 and Stage 3, parsed
all 1,426 Stage 4 closure files, then failed HIR lowering with:

```text
src/app/io/_CliCompile/compile_targets.spl: unresolved name: rt_env_get
```

`_native_build_entry_closure` called the raw runtime symbol for both
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE` and
`SIMPLE_NATIVE_BUILD_TRACE_CLOSURE_TIMING`. The leaf module imported only the
pure-Simple `env_set` facade, even though its adjacent native-build environment
save/restore path already used `env_get`.

## Acceptance

- Both closure trace reads use the pure-Simple `app.io.env_ops.env_get` facade.
- The adjacent native-build environment save/restore reads retain that facade.
- The leaf contains no raw `rt_env_get` call.
- A focused exact-and-adjacent source contract passes before resuming bootstrap.

## Resolution and evidence

The leaf now imports `env_get` beside `env_set`, and both trace reads use that
facade. The adjacent save/restore reads remain facade-owned and no raw
`rt_env_get` reference remains in the file.

Focused source contract: 2 examples passed (exact trace pair plus adjacent
save/restore reads). `direct-env-runtime-guard.shs --working` also reported
`STATUS: PASS`.
