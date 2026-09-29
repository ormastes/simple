# `Poll.unwrap` steals `.unwrap()` in `lower_and_check_impl` — a SECOND, independent bind site

- **Filed:** 2026-08-25
- **Status:** OPEN. Isolated by measurement, mechanism NOT yet located.
- **Severity:** blocks the Stage-2/Stage-3 self-host lane (rc=139 on hello world).
- **Parent record:** `stage3_n_modules_zero_segv_mir_lowering_x86_64_2026-08-24.md`
- **Gate:** `scripts/check/check-stage2-option-unwrap-not-stolen.shs` (ADVISORY, honestly RED — red *because of this bug*)

## What this is, and what it is NOT

`.unwrap()` on an Option whose receiver type is erased is bound to
`lib__nogc_async_mut__async__poll__Poll_dot_unwrap`. `Poll.unwrap` tests the
`Poll::Ready`/`Poll::Pending` discriminants, matches neither `Some` tag, falls
through and returns 0. Zero is `< 4096`, so `rt_heap_ref_wellformed` reports the
payload malformed while the field still holds a real enum — hence
`E-DRIVER-HIR-RETAINED-SURFACES-MALFORMED` and the rc=139 self-host death.

That much is the parent record's defect. **What is new here is that there are
TWO independent bind sites producing it, and only one has been fixed.**

**This is NOT the name-suffix single-candidate tail** in
`compile_method_call_static` (`codegen/instr/closures_structs.rs`). That site
was found, fixed, measured, and landed on 2026-08-25. Do not re-investigate it;
that is a solved path and re-litigating it has already cost this defect several
lanes.

## The measurement that isolates this site

Per-function callee counts by disassembly, pre-fix vs post-fix Stage 2, both
built from base `4d11699bc5b` by the same replayed bootstrap argv (cranelift,
full `src/compiler` + `src/app` + `src/lib` closure):

| function | `Poll_dot_unwrap` | `rt_unwrap_or_trap` |
|---|---|---|
| `run_named_pass_with_record` | 3 → **1** | 0 → **2** |
| `run_pass_on_module_checked` | 3 → **1** | 0 → **2** |
| **`lower_and_check_impl`** | **4 → 4** | **0 → 0** |
| whole binary | 307 → **272** (−35) | 117 → **151** (+34) |

Read this carefully, because it is the whole case:

- The suffix-binder fix works. `rt_unwrap_or_trap` gains exactly **+34**, and
  the sites moved in precisely the functions the original codegen probe named.
  (The whole-binary `Poll_dot_unwrap` delta reads −35 rather than −34 because
  of one further reference in the unrelated `DimSolver_dot_solve_constraint`
  that differs between two builds of the same fix — build variance, not this
  fix. The per-function rows are identical across both builds.)
- `lower_and_check_impl` did not move **at all** — not one of its 4 sites, and
  it gained zero builtin calls. A fix that genuinely covered this path could
  not leave it bit-for-bit unchanged.
- Therefore these 4 sites are reached by a **different mechanism**.

All 4 surviving sites target the same wrong symbol:

```
objdump -d <post-fix stage2>  # within lower_and_check_impl
  4 x <lib__nogc_async_mut__async__poll__Poll_dot_unwrap>
```

## Corroborating negative evidence

- The erased-receiver codegen probe (`SIMPLE_DEBUG_ERASED_RECEIVER_BIND=1`)
  reports **zero** `unwrap` suffix binds on the fixed compiler, and zero
  occurrences of the string `Poll_dot_unwrap` anywhere in its output — while
  remaining demonstrably live (64 bind lines across 12+ other methods:
  `with_note`, `build`, `map`, `kind`, `lower_const`, `add_port`, …). So this
  site does not announce itself through that reporter at all.
- The `calls.rs` import-ladder / `imports.rs` ambiguous-first-wins hypothesis is
  **refuted, twice, by instrumentation on real self-host builds**. Across a full
  compile the ladder probe fired exactly twice, both for the unrelated
  `expr_force_unwrap` via `use_map_direct`. Do not restart there.

## Why no fixture will reproduce this

`func_ids` is per-module. A small single-module build never has `Poll.unwrap` in
scope, so the decoy that makes the theft possible does not exist. Every attempt
to shrink this to a fixture has failed for that reason. Reproduction requires a
real Stage-2 self-host compile (~10 min on a warm cache) via the replayed
bootstrap argv — the bootstrap scrubs `SIMPLE_DEBUG_*`, so instrumenting it
requires replaying its argv rather than invoking it.

## Suggested next step

Instrument the resolution of a bare `unwrap` **outside** the suffix binder —
i.e. whatever path `lower_and_check_impl` actually takes — and bisect on which
call in that function produces the `lea`/indirect-call pair. Note
`grep -c "call.*Poll_dot_unwrap"` returns 0 on a binary calling it hundreds of
times (it is `lea` + indirect); use symbol-aware disassembly.

## Reproduce

```sh
sh scripts/check/check-stage2-option-unwrap-not-stolen.shs --stage2 <stage2-binary>
# expect: FAIL -- ... 4 Simple '*_dot_unwrap' call site(s) inside lower_and_check_impl ...
```

---

## 2026-08-31 — independent re-derivation, plus a 7-second reproducer and a candidate mechanism

Re-found from scratch while chasing
`stage2_positional_entry_segv_module_surfaces_null_2026-08-31.md`, which is the
same defect surfacing at the positional-entry gate. Recorded here because two
of the three items below are new.

### 1. Direct dynamic confirmation (lldb, not disassembly)

Binary: `build/bootstrap/stage2/aarch64-apple-darwin/simple.rejected`, 32010840
bytes, sha256 `3db6a922e3d856ef62d25e4e5f494a8afd4e4ad32e7a7b2541809b711809cdd0`.

- Breakpoint at `lower_and_check_impl+1048` (the `if self.ctx.module_surfaces
  != nil:` branch) **hits**; the branch body is
  `ldr x0, [x5, #0x80]` / `blr` -> `lib__nogc_async_mut__async__poll__Poll_dot_unwrap`
  / `str x0, [sp, #0x448]`.
- Breakpoint on `hirlowering_for_module_with_diagnostics` then hits with
  **`x1 == 0`** (`x1` is the `module_surfaces` argument). The field store into
  `HirLowering` is faithful (`str x1, [x7, #0x58]`, offset 0x58 = field index
  11 = `module_surfaces`); the VALUE is what is 0.
- Three frames later `module_surface_registry_index` faults at
  `ldr x0, [x6, #0x8]` with `x6 == 0`.

### 2. A 7-second reproducer (new — no bootstrap, no stage binary)

Built with the Rust seed using Stage 2's own flags (`--backend cranelift
--runtime-bundle core-c-bootstrap --entry-closure --mode one-binary`), 57 files,
6.6s wall:

```simple
use compiler.hir.hir_lowering.module_surface.{ModuleSurfacesByName}
use std.nogc_async_mut.async.poll.{Poll}        # <- the whole experiment

class Ctx:
    module_surfaces: ModuleSurfacesByName?

fn drive(ctx: Ctx) -> ModuleSurfacesByName:
    if ctx.module_surfaces != nil:
        return ctx.module_surfaces.unwrap()      # returns raw 0
    ModuleSurfacesByName.empty()
```

Per-variant verdicts (each variant separately built and RUN; counts, not a
sequence):

| variant | rc |
|---|---|
| `.unwrap()` on an `Option<Class>` field, `Poll` imported | **139** |
| identical file with the `Poll` import deleted | 0 |
| `use std.nogc_sync_mut.failsafe.core.*` instead of `Poll` | **139** |
| `.unwrap()` via a typed local `val o: T? = ctx.f` | **139** |
| `ctx.f ?? T.empty()` | 0 |
| `if val x = ctx.f:` | 0 |
| `match ctx.f: case Some(v) / case None` | 0 |

Two consequences:

- **Renaming `Poll.unwrap` is not a fix, and this is measured, not argued.**
  `FailSafeResult.unwrap` (`src/lib/nogc_sync_mut/failsafe/core.spl:140`) steals
  it identically; `src/` holds 13 `fn unwrap` definitions. Any one of them can
  be the thief.
- The trigger is **the presence of a bare-`unwrap` provider in the module's
  import surface**, not the receiver expression: a typed local fails too.

### 3. Candidate mechanism — INDICATED BY CODE READING, NOT YET INSTRUMENTED

`src/compiler_rust/compiler/src/pipeline/native_project/mangle.rs`,
`resolve_method_call_static` (:724).

That function already carries a guard for exactly this
(`unwrap | unwrap_or | unwrap_err | is_some | is_none | is_ok | is_err`), and its
comment even names `FailSafeResult.unwrap` as the hazard — **but the guard sits
in the `else` branch, i.e. it only runs when `resolve_name_variants` FAILS**:

```rust
if let Some(resolved) = resolve_name_variants(lookup_name, use_map, import_map) {
    *func_name = resolved;              // <- bare `unwrap` rebound here, guard never reached
} else {
    ... if matches!(method, "unwrap" | ...) { return; }   // the guard
}
```

When any closure module publishes a bare `unwrap` into the use/import map,
`resolve_name_variants` **succeeds** and the guard is bypassed. This is the same
fail-open shape the string-builtin guard was hoisted ABOVE `resolve_name_variants`
to close on 2026-07-25 (see that guard's comment in the same function), and it is
consistent with every row of the table above — including the refutation in the
section above, since this path is neither the `closures_structs.rs` suffix
binder nor the `calls.rs` import ladder.

**Not instrumented.** No probe was added to mangle.rs to observe the rebind
directly, so treat this as the strongest available hypothesis rather than a
located mechanism. The cheap next step is a one-line eprintln in that `if let
Some(resolved)` arm, gated on `method == "unwrap"`, replayed against the 7s
reproducer above — seconds per iteration.

**Do not simply hoist the enum-helper list.** The in-file comment records that
hoisting it was tried and reverted: it "broke legitimate resolution-success
rebinds (the compiled interpreter's own Option helpers printed `<unknown>` for
every text-option `??`, 2026-07-25)". A narrower predicate is required.
