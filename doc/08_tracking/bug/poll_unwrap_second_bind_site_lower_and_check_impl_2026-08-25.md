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
