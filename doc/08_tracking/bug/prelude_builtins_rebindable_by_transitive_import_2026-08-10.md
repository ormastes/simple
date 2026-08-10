# Prelude builtins (`exit`, `eprint`, `dprint`) are silently rebindable by a transitively imported top-level `fn`

- **Date:** 2026-08-10
- **Status:** PARTIALLY FIXED (2026-08-10, commit `d21332ede1f`) — `exit` is
  fenced in both lanes and every shadow now warns. The general hazard (the other
  50 user-facing prelude names remain shadowable, by an explicit and now-stated
  policy) is still OPEN. The one live instance (`eprint`) is
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


---

# Update 2026-08-10 — full sweep, `exit` fixed, policy chosen

## What changed (commit `d21332ede1f`)

`exit` is now **unshadowable in both lanes**, and every remaining prelude shadow
**warns once** naming the builtin and the shadowing definition. Guarded by
`scripts/check/check-prelude-builtins-unshadowable.shs`.

**Reproduction (before).** `main.spl` imports only `mid_helper` from `q29mid`,
which imports only `helper` from `q29lib`; `main` never names `exit`, and
`q29lib` defines `pub fn exit`:

```
BEFORE code=42
SHADOW_EXIT_RAN code=3
AFTER_EXIT_STILL_RUNNING      <-- process did not terminate
EXITCODE=0                    <-- and reported success
```

**After:** the shadow does not run, `AFTER_EXIT_STILL_RUNNING` is absent, and
`EXITCODE=3`, with a warning naming the shadowing `fn exit`.

## The hole had TWO independent causes

The predecessor analysis named only the first. Fixing either alone leaves the
defect live, which is why the guard probes both lanes:

1. **Interpreter** — the Priority-1 `has_local_def` escape hatch in
   `interpreter_call/mod.rs`, as originally diagnosed.
2. **JIT / native** — `hir/lower/expr/calls.rs` recognizes builtins by an
   **explicit whitelist**. `exit` was simply absent from it, so it fell through
   to ordinary function resolution. This also explains the JIT column below
   exactly: the names that resisted shadowing in the JIT lane are precisely the
   ones that whitelist mentions.

The bug doc's claim that `print`/`println`/`panic` are protected by a
"parser statement-form accident" is **wrong**. They are protected by that HIR
whitelist, and only in the JIT lane — in the interpreter, called in
**expression position** (`val r = println(1)`), `println` and `panic` are both
shadowable. Only `print` resisted in both lanes.

## Prelude x lane shadowability (measured, all 51 user-facing names)

Probe: 3-module transitive import as above; SHADOWABLE = the user `fn` ran.
JIT `safe` verdicts were positive-controlled (the builtin demonstrably ran:
`abs(1)`=1, `panic` really aborted) so "safe" never means "the program errored".
Runs that emitted `[jit-fallback]` are reported as such, never credited as JIT.

| lane | shadowable | safe |
|---|---|---|
| interpreter | **50 / 51** | `print` only |
| JIT | **43 / 51** | `print`, `print_raw`, `eprint`, `eprint_raw`, `input`, `println`, `eprintln`, `abs`, `panic` |

`dprint` is shadowable in **both** lanes. After this commit `exit` is safe in
both. Native lane not separately measured — it shares the HIR lowering path
with JIT, so the JIT column is the governing signal there; confirming it is
follow-up work.

## Policy chosen: fence process control, warn on the rest

Rejected: making all prelude names unshadowable. **22 of the 51 names already
have 102 top-level definitions in `src/**`** (inventory:
`prelude_shadow_inventory_2026-08-10.txt`) — `exit` 16, `min` 10, `abs` 8,
`sqrt`/`max`/`format_bytes` 7 each, and so on. Silently retargeting all of them
to builtins is a semantic change across the whole tree that cannot be verified
in one commit, and it would change baremetal behaviour (`os/kernel/arch/*/cstart.spl`
maps `exit` to `__spl_exit`, not to host process exit).

Adopted instead:
- **`PRELUDE_UNSHADOWABLE`** (currently `exit`) — always dispatches to the
  builtin. Justified for `exit` specifically because a shadowed `exit` is a
  false-GREEN generator, and because it is behaviour-preserving: all 16 live
  `fn exit` definitions in the host lanes delegate to `rt_exit` already, and the
  baremetal `cstart.spl` variants are never interpreted.
- **Everything else stays legal but is loud** — one warning per name, naming the
  builtin and the shadowing definition's line, silenceable with
  `SIMPLE_NO_PRELUDE_SHADOW_WARNING=1`. This is what the `eprint` incident
  needed and did not have for months.
- The `rt_*` escape hatch that motivated the whole mechanism is untouched:
  `is_user_facing_prelude` excludes `rt_*` / `compiler__*`, so
  `rt_array_len_safe` still wins over its coincidental extern registration.

This is a Rust-layer fix, against the repo's usual fix-in-`.spl` rule, because
the defect is in the seed interpreter's dispatch and in HIR lowering — there is
no `.spl` site to fix.

## Existing shadows: disposition

All 16 `fn exit` definitions delegate to `rt_exit` (or, in baremetal,
`__spl_exit`), so none of them was causing live non-termination — the fenced
builtin now makes that structural rather than incidental. The remaining 86
shadows across 21 other prelude names are **not yet triaged individually**; they
are now visible via the warning rather than silent, which is the point of the
policy. Triage remains open work and is the reason this bug is not closed.

## Verification

- Check: `scripts/check/check-prelude-builtins-unshadowable.shs`
  (`SIMPLE_BIN=<path>`), verdict line last, negative control included.
- Fixed binary (built to a private `CARGO_TARGET_DIR`, not the shared `target/`):
  `PASS — 3 probes checked`.
- **Revert-proof:** the same check against a binary predating the fix
  (`bin/release/x86_64-unknown-linux-gnu/simple`, Aug 9 04:50) reports
  `FAIL — [interpret]` and `FAIL — [jit]`, with the negative control still
  firing — so the PASS is caused by the fix, not by a broken harness.
