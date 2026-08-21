# `[DEBUG declare_globals fallback]` printed unconditionally on the cranelift codegen path

- **Date:** 2026-08-21
- **Status:** OPEN (recorded only — gating deliberately NOT implemented here)
- **Severity:** low (noise, not miscompilation)
- **Found during:** `bin/simple build bootstrap` Stage 1, after the
  `auto`→backend resolution fix; Stage 1 is a plain `--backend=cranelift`
  `native-build` of the `src/app` entry closure.

## Symptom

Stage 1 stdout/stderr carries a stream of lines of the exact form:

```
[DEBUG declare_globals fallback] name=mir_lower_expr_trace_state module_prefix=Some("compiler__driver__driver")
[DEBUG declare_globals fallback] name=mir_mc_trace_state module_prefix=Some("compiler__driver__driver")
[DEBUG declare_globals fallback] name=mir_optional_inner_trace_state module_prefix=Some("compiler__driver__driver_aot_codegen_outputs")
```

This is a `[DEBUG …]`-tagged developer probe reaching an ordinary user-facing
build. It is not an error and does not affect the produced binary.

## Origin

`src/compiler_rust/compiler/src/codegen/common_backend.rs:1686-1694`, in
`declare_globals`, on the imported-global resolution path:

```rust
if use_hit.is_none()
    && import_hit.is_none()
    && std::env::var_os("SIMPLE_NO_DEPRECATED_WARNINGS").is_none()
{
    eprintln!(
        "[DEBUG declare_globals fallback] name={} module_prefix={:?}",
        name, self.module_prefix
    );
}
```

Two separate defects:

1. **Default-on.** The only guard is the *absence* of
   `SIMPLE_NO_DEPRECATED_WARNINGS`, so the probe fires by default on every
   build. A debug probe must be opt-in, not opt-out.
2. **Wrong knob.** `SIMPLE_NO_DEPRECATED_WARNINGS` is about deprecation
   warnings; this line is neither a deprecation nor a warning. Suppressing it
   today requires setting an unrelated variable, which also suppresses genuine
   deprecation output.

## Recommended fix (not applied)

Per `.claude/rules/code-style.md` the probe is **not** to be deleted — it is a
level-gated log, default off. The correct idiom already exists 140 lines above
in the same function, at `common_backend.rs:1546`:

```rust
let trace_global = std::env::var("SIMPLE_TRACE_DECLARE_GLOBALS").is_ok() ...
if trace_global {
    eprintln!("[declare-globals] import data name={}", name);
}
```

Reuse that existing `trace_global` flag for this call site, drop the
`SIMPLE_NO_DEPRECATED_WARNINGS` condition, and align the tag with the
neighbouring `[declare-globals]` prefix so one env var governs the whole
function.

## Notes

- Deliberately kept out of the backend-resolution fix landed the same day
  (`native_project/mod.rs` single-diagnostic + `misc_commands.rs` `auto` probe)
  to keep that diff minimal.
- The fallback itself may also be worth investigating separately: every observed
  name is a `*_trace_state` global, suggesting these genuinely miss both
  `use_map` and `import_map` and fall through to `mangle_name`. That is a
  distinct question from the logging and is not filed here.
