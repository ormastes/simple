# Prelude builtins (`exit`, `eprint`, `dprint`) are silently rebindable by a transitively imported top-level `fn`

- **Date:** 2026-08-10
- **Status:** OPEN — the general hazard. The one live instance (`eprint`) is
  fixed in
  `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`;
  the mechanism that allowed it is not.
- **Lanes:** both `interpreter` and `jit`.
- **Class:** silent semantic hijack / name resolution.

## Mechanism

`src/compiler_rust/compiler/src/interpreter_call/mod.rs:358-410`, `evaluate_call`:

```rust
// Priority 1: Check extern functions first (before builtins)
let has_local_def = is_extern
    && (functions.contains_key(name.as_str())
        || FUNCTION_OVERLOADS.with(|c| c.borrow().contains_key(name.as_str())));
if is_extern && !has_local_def { /* extern/builtin dispatch */ }

// Priority 2: Try built-ins (before user functions, so builtins can't be shadowed)
```

The `has_local_def` escape hatch was added deliberately, for
`rt_array_len_safe`: a pure-Simple helper whose name coincidentally matched a
runtime export had to win over the coincidental extern registration
(`seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`).

But **prelude builtins are registered in the same `EXTERN_FUNCTIONS` set**
(`interpreter_eval.rs:232` `PRELUDE_EXTERN_FUNCTIONS`, which lists `print`,
`eprint`, `dprint`, `exit`, `panic`, `input`, …). So the hatch applies to them
too, and the reassuring comment on the line below — *"before user functions, so
builtins can't be shadowed"* — is **false** for every prelude name Priority 1
reaches. A single top-level `fn exit` anywhere in a module's transitive import
closure silently rebinds `exit` for the whole program.

## Measured family

Synthetic 2-level transitive import (`main` → `mid` → `lib` defining the name),
`bin/simple`, both lanes:

| builtin | rebindable? | observed |
|---|---|---|
| `exit` | **YES** | user `fn exit` ran; `exit(0)` **did not terminate the process** |
| `dprint` | **YES** | user `fn dprint` ran |
| `eprint` | **YES** | real instance, see the linked bug |
| `print` / `println` | no | parser resolves the statement form ahead of call dispatch |
| `panic` | no | real panic fired; the user `fn panic` never ran |

`print`, `println` and `panic` are protected only by a **syntax accident** —
they have a statement form the parser handles before name resolution. That is
not a policy and it will not protect any prelude name added later.

## Why `exit` is the dangerous one

There are **12** top-level `fn exit` definitions in `src/`
(`src/app/io/cli_ops.spl:342`, `src/app/io/signal_handlers.spl:11`,
`src/lib/nogc_sync_mut/io/signal_handlers.spl:11`,
`src/compiler/70.backend/baremetal/link_wrapper.spl:296`, …). Any program whose
import closure reaches one of those and then calls bare `exit(code)` gets that
function instead of process termination — the program keeps running, and the
exit code is whatever `main` falls through to. That is a false-GREEN generator
for any harness that reads exit status.

## Why it is not fixed here

The obvious fix — move Priority 2 (builtins) ahead of Priority 1's
`has_local_def` fallback, or exclude `PRELUDE_EXTERN_FUNCTIONS` from the hatch —
directly re-opens the `rt_array_len_safe` regression, and it is a
name-resolution semantics change in the seed interpreter affecting every call
site in the compiler. It needs its own change with its own bootstrap
verification, not a drive-by inside a logging fix.

Preferred shape when it is done:

1. Split the two sets. The hatch should key on *coincidental runtime-symbol
   registration* (the `rt_*` manifest bulk-seed that motivated it), **not** on
   `PRELUDE_EXTERN_FUNCTIONS`. A prelude builtin should never be silently
   rebindable.
2. If a module genuinely needs its own `exit`/`eprint`, it should have to say so
   — a shadow of a prelude name should at minimum **warn** at load, naming both
   the builtin and the shadowing definition, the way the seed already warns for
   `compiler_cross_module_private_symbol_collision`.
3. Audit the 12 `fn exit` definitions: most look like they want a distinct name.

## Next step

Land (2) first — the load-time warning is cheap, non-breaking, and turns every
remaining instance of this class from silent into visible, which is what the
`eprint` case needed and did not have for months.

## Related

- `doc/08_tracking/bug/eprint_in_io_runtime_module_is_rerouted_to_stdout_2026-08-10.md`
- `doc/08_tracking/bug/seed_native_build_unknown_extern_rt_array_len_safe_2026-07-12.md`
- `scripts/check/check-eprint-reaches-stderr-fd.shs`
