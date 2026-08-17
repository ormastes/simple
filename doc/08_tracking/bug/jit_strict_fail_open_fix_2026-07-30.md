# SIMPLE_JIT_STRICT fail-open fix (2026-07-30)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 02).

Assignment (part 1 of 2): fix the SIMPLE_JIT_STRICT fail-open hole flagged
as a side finding in the pass-12 `os.*` JIT root-cause doc — strict mode
printed a "refusing to fall back" message and then fell back anyway,
exiting 0.

## PROVED: exact fail-open site

`src/compiler_rust/compiler/src/codegen/jit.rs`'s
`first_unresolved_import` guard already differentiates its error message
under `SIMPLE_JIT_STRICT`:

```rust
if std::env::var_os("SIMPLE_JIT_STRICT").is_some_and(|v| v != "0") {
    return Err(BackendError::ModuleError(format!(
        "SIMPLE_JIT_STRICT: unresolved external symbol '{name}' would NULL-jump in JIT; \
         refusing to fall back to the interpreter"
    )));
}
return Err(BackendError::ModuleError(format!(
    "unresolved external symbol '{name}' would NULL-jump in JIT; deferring to interpreter"
)));
```

Both branches return an `Err` either way — the difference is only in the
message text. The actual "fall back to interpreter" decision is made by
the SOLE catch site in the whole codebase (confirmed via
`grep -rn 'JIT compilation failed, falling back' src/compiler_rust`):
`src/compiler_rust/driver/src/exec_core.rs`,
`ExecutionRunner::run_file_with_args`:

```rust
match std::panic::catch_unwind(...(|| self.run_file_jit(path))) {
    Ok(Ok(exit_code)) => Ok(exit_code),
    Ok(Err(jit_err)) => {
        eprintln!("[INFO] JIT compilation failed, falling back to interpreter: {}", jit_err);
        self.run_file_interpreted_with_args(path, args)   // <-- unconditional
    }
    ...
}
```

This site swallowed **every** `jit_err` into the same unconditional
interpreter fallback, whether or not it originated from the
`SIMPLE_JIT_STRICT`-tagged branch. The guard in `jit.rs` was structurally
inert: it could never actually stop execution, because its caller never
looked at which branch produced the error.

Traced the string through the wrapper layers to confirm the tag survives
intact to this catch site: `LocalExecutionManager::compile_module`
(`codegen/local_execution.rs`) wraps the Cranelift path's error with
`format!("Cranelift JIT compile: {}", e)`, and `run_file_jit`
(`exec_core.rs`) propagates it unchanged via `?` — the final string
observed at the catch site is e.g. `"Cranelift JIT compile: Module
error: SIMPLE_JIT_STRICT: unresolved external symbol 'hotp_sha1_bytes'
would NULL-jump in JIT; refusing to fall back to the interpreter"`,
which still contains the `"SIMPLE_JIT_STRICT:"` substring — matching
exactly what pass 12 observed empirically.

## Fix

`exec_core.rs`'s catch arm now checks for the tag before falling back:

```rust
Ok(Err(jit_err)) => {
    if jit_err.contains("SIMPLE_JIT_STRICT:") {
        return Err(jit_err);
    }
    eprintln!("[INFO] JIT compilation failed, falling back to interpreter: {}", jit_err);
    self.run_file_interpreted_with_args(path, args)
}
```

`Err(jit_err)` from `run_file_with_args` (`Result<i32, String>`) reaches
`driver/src/cli/basic.rs`'s top-level `run_file_with_args` wrapper, which
prints the error (`print_cli_error(&e)`) and returns exit code `1` —
satisfying the "non-zero exit, message naming the symbol" requirement
without any further plumbing changes.

**Blast-radius scoping**: only the `SIMPLE_JIT_STRICT:`-tagged message
(the unresolved-import/NULL-jump class specifically) is hard-failed.
Every other JIT failure reason routed through this same catch site
(lambda/closure ABI incompatibility, generator-function unsupported-ness,
genuine compiler bugs, panics) is untouched and continues to fall back
leniently exactly as before — this fix does not broaden strict mode's
reach beyond the one guard that already opted into tagging its own
message for it.

## Caution check: does any in-repo harness rely on the lenient behavior?

`grep -rln SIMPLE_JIT_STRICT scripts/ test/ src/app` found exactly one
hit: `scripts/check/check-compiler-provenance.shs`. Read in full — this
is a **string-presence** check (`strings -a <binary> | grep -c
'SIMPLE_JIT_STRICT'`) that verifies the literal exists in a built binary
as evidence a given commit's fix landed in that binary. It does not set
the env var, does not invoke strict mode, and is unaffected by this
change (the literal `"SIMPLE_JIT_STRICT"` still appears unchanged inside
`jit.rs`, which this pass did not touch). **No harness found that sets
`SIMPLE_JIT_STRICT=1` and relies on the current lenient fallback** — this
fix does not silently break anything on record.

## Validation (PROVED — built a candidate seed and ran both probes directly)

Built a candidate seed via `cargo build --release --bin simple` (scoped to
the `driver` binary, reusing the main repo's cargo target cache for
incremental compilation; finished in 3m45s). Ran both validation probes
directly against this patched binary (not `bin/simple`, which remains the
unpatched deployed seed):

```
$ SIMPLE_JIT_STRICT=1 <patched-seed> probe_hotp.spl   # calls os.crypto.hotp
exit_code=1
error: Cranelift JIT compile: Module error: SIMPLE_JIT_STRICT: unresolved
  external symbol 'hotp_sha1_bytes' would NULL-jump in JIT; refusing to
  fall back to the interpreter

$ SIMPLE_JIT_STRICT=1 <patched-seed> probe_trivial_lib.spl   # calls std.common.zzprobe.trivial
exit_code=0
trivial_lib=42
```

Both match the assignment's exact validation bar: the `os.*`-touching
strict run now exits non-zero and names the unresolved symbol; the clean
`std.*`/`lib.*` probe is completely unaffected and still succeeds. This
is a direct, both-cases observation against a real built binary, not an
inference from reading the source.

`cargo build --release --bin simple` for the patched crate completed
without new warnings or errors introduced by this change (pre-existing
unrelated warnings in `interpreter_call/block_execution.rs` were already
present, unrelated to `exec_core.rs`). A full `cargo clean` was not run
this pass (the incremental build reused the existing 104GB target cache
in the main repo to keep build time tractable within budget) — this is
INFERRED-safe (the change is 12 added lines in one function, no new
dependencies, no signature changes) but not empirically re-verified from
a fully clean build.
