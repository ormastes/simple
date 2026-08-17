# `it` block reads a STALE module-level `var` after a helper writes it

**Status:** ROOT CAUSE PINNED + FIX LANDED 2026-08-17 (seed fix; redeploy pending)

## 2026-08-17 — the previously-unpinned site, and the fix

The "Not yet pinned" note below is now closed. It is not the `rt_bdd_*`
intrinsics and not capture-by-value at registration time. It is two lines:

1. `interpreter_call/bdd.rs:778` — `let mut test_env = env.clone();`. Every `it`
   body executes against a private COPY of the caller env, dropped after the
   body (deliberate, for per-example memory isolation).
2. `interpreter/expr/literals.rs:278` — the `Identifier` read returns that copy.
   The refresh immediately above it fires only for **imported** globals
   (`!env.is_local(name) && env.is_refreshed_global(name)`, keyed on owner
   provenance). A **same-file** module `var` has no owner provenance, so it is
   skipped, and the `MODULE_GLOBALS` fallback further down (`:312`) — which is
   where a callee's write actually lands via `place.rs sync_module_global` — is
   never reached, because the stale `env` binding already returned.

This also explains the original truth table exactly: A/D pass because the helper
reads `MODULE_GLOBALS` directly; C passes because the body's own write goes into
the same copy it then reads; only B crosses the two stores.

**Fix:** `literals.rs` — for an env binding that is NOT local, prefer
`MODULE_GLOBALS`, which is authoritative for these names (C/D passing proves a
direct write already syncs there).

**Blast radius is wider than this report recorded.** The class spec below found
two shapes not listed here:
- a module-level **container** mutated in place by a helper loses the writes
  entirely, degrading from a wrong value to a hard error
  (`array index out of bounds: index is 0 but length is 0`);
- a write performed by a **`before_each` hook** is invisible in the body — a
  common spec idiom that silently does nothing.

**Evidence.** RED on deployed seed (`bin/simple`, mtime 2026-08-16 22:59):
`Results: 8 total, 1 passed, 7 failed` (class spec) and `2 total, 0 passed, 2
failed` (ad-hoc repro of cases A/B). GREEN on a seed rebuilt with the fix
(`CARGO_TARGET_DIR=/mnt/data/b3-target`): `Results: 4 total, 4 passed, 0 failed`
and `Results: 8 total, 8 passed, 0 failed`.

**Not proven:** an ablation build (fix removed, same tree) was attempted and did
NOT execute — it aborted with `pure-Simple tool 'test' unavailable; refusing
Rust fallback`, so its exit 1 is a refusal, not a spec failure. The pre-fix RED
therefore comes from the deployed seed, a different build, not from an ablated
build of this tree. The causal chain is established by source reading, not by
ablation. Re-run the ablation before treating this as closed.

Specs: `test/01_unit/compiler/spec_module_var_live_read_spec.spl` (reproducer),
`test/01_unit/compiler/module_global_stale_shadow_class_spec.spl` (defect class:
payload type x writer depth x read position).

---

**Previous status:** OPEN (ARCHITECTURAL — Rust seed spec-runner registration; not pure-Simple fixable)
**Found:** 2026-08-04
**Re-verified:** 2026-08-10 — reproduced fresh via
`test/03_system/feature/baremetal/modvar2_spec.spl` (regression coverage added,
left RED on purpose per `.claude/rules/testing.md`):
`SIMPLE_TIMEOUT_SECONDS=120 bin/simple test --no-cache --no-cover-check
test/03_system/feature/baremetal/modvar2_spec.spl` → `4 examples, 1 failure`,
case B `expected -999 to equal 16`, exit 1 — identical to the original repro.
Root cause remains in the Rust bootstrap seed's `it`-body closure registration
(`rt_bdd_*` intrinsics / capture-by-value semantics), outside the
`.spl`/`.shs`-only, no-seed-rebuild constraints of this pass. No change made.

## Symptom

Inside an `it` block run by `bin/simple test`, reading a module-level `var` by
name returns the value it had at spec-registration time, not the live value —
even after a helper function in the same file has written it. The write itself
lands (a helper reading the same var sees the new value); only the *direct read
from inside the `it` body* is stale.

Minimal repro — `modvar2_spec.spl`:

```simple
var g = -999

fn setit(v: i64):
    g = v
    0

fn getit() -> i64:
    g

describe "module var mechanism":
    it "A: helper-read after helper-write":
        setit(15)
        expect(getit()).to_equal(15)

    it "B: direct-read after helper-write":
        setit(16)
        expect(g).to_equal(16)

    it "C: direct-write then direct-read":
        g = 17
        expect(g).to_equal(17)

    it "D: direct-write then helper-read":
        g = 18
        expect(getit()).to_equal(18)
```

Command:

```
SIMPLE_TIMEOUT_SECONDS=0 bin/simple test --no-cache --no-cover-check modvar2_spec.spl
```

Truth table (actual):

| case | shape | result |
|------|-------|--------|
| A | helper-write → helper-read | PASS |
| B | helper-write → **direct read in `it`** | **FAIL — `expected -999 to equal 16`** |
| C | direct-write → direct-read | PASS |
| D | direct-write → helper-read | PASS |

Only B fails. A proves the global really was updated; C proves a write performed
inside the `it` body creates a binding the body can then see; B proves the body's
*read* of an externally-updated global resolves to a stale snapshot.

## Root cause

The staleness is introduced by the **spec-runner path**, not by either execution
engine. Both engines produce the CORRECT value for the same code outside
`bin/simple test`:

- `bin/simple run` (Cranelift JIT), closure calling `setit(16)` then reading `g`
  → `16` (correct).
- `SIMPLE_EXECUTION_MODE=interpreter bin/simple run`, same file → `16` (correct).
- Hand-writing the wrapper's *output shape* (module `var` at top level,
  `describe`/`it` nested inside `fn main()`) and running it under **both**
  engines → `16` (correct).

So neither the JIT, the tree-walk interpreter, nor the mere nesting of
`describe`/`it` inside `fn main()` reproduces it. What is left is the spec
runner's own registration-and-replay of `it` bodies: the bodies are registered
as closures first and executed afterwards, and a module-level `var` free in the
body is captured **by value at registration time** (before any `it` has run),
so the later read returns the registration-time value.

The transformation that makes the `it` bodies nested closures is in
`src/lib/nogc_sync_mut/test_runner/test_result_wrapper.spl`:

- line 421-429 — lines at column 0 matching `spipe_is_top_level_start` (which
  includes `var `, line 291) are routed to `top_level_parts` and stay at module
  scope.
- line 449-453 — everything else, including the whole `describe`/`it` tree, is
  pushed into `body_parts` with an added 4-space indent.
- line 333 / 455-465 — `body` is then emitted wrapped in `fn main():`.

Capture-by-value for closures is the documented interpreter behaviour
(`src/compiler_rust/compiler/src/interpreter/expr/control.rs:49-50`: "For move
closures, we capture by value (clone the environment); For regular closures, we
share the environment reference") and matches the standing limitation in
`.claude/rules/language.md` ("Nested closure capture — can READ outer vars,
CANNOT MODIFY"). This report extends that limitation: under the spec runner the
READ is not merely non-mutable, it is **stale**.

**Not yet pinned:** the exact registration site that clones the environment for
an `it` body (the `rt_bdd_*` intrinsic family). The layer is proven by
elimination above; the specific Rust line is not.

## Impact

This is the root cause of at least 28 failures in the previously-unmeasured
`test/03_system/feature/baremetal` directory, all in specs that use module-level
`var` recorders as local stubs:

- `test/03_system/feature/baremetal/interrupt_spec.spl` — 20 of 29 failing, every
  one reading a `_last_*` recorder var that a stub helper had just written
  (`expected -999 to equal 15`, and siblings).
- `test/03_system/feature/baremetal/syscall_spec.spl` — 8 failing, same shape.

Note separately that both of those specs declare their recorders under the
comment `# --- Local stubs (module import doesn't resolve in interpreter mode) ---`,
so they exercise their own stubs rather than product code. Fixing this bug turns
them green but does NOT make them meaningful coverage; they need repointing at
the real modules afterwards (SHIM VACUITY).

## Why not fixed now

The fix belongs in the Rust bootstrap seed's spec-runner closure registration
(the `rt_bdd_*` intrinsics), not in `.spl` product source. Repo rules direct
fixes to pure-Simple source and discourage a seed rebuild unless essential
(`.claude/rules/bootstrap.md`, `feedback_fix_spl_not_rust`,
`feedback_no_bootstrap_unless_essential`), and the exact registration site is
still unpinned (see above), so a change now would be speculative. Changing
capture semantics for `it` bodies also affects every spec in the repo and needs
its own lane with a full regression pass.

The alternative fix — having `test_result_wrapper.spl` keep `describe`/`it` at
module scope instead of nesting them in `fn main()` — was NOT attempted here
because the hand-written nested form runs correctly on both engines, so nesting
is not by itself the trigger and removing it may not fix anything.
