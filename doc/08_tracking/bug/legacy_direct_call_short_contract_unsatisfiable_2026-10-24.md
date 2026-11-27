# Legacy modules reject every `f(&mut x)`: checked short-call contract is unpublishable (2026-10-24)

Class: (b) false positive in the self-hosted NLL borrow checker
(`src/compiler/55.borrow`). Found by Phase-3 run 11 (go-to-end ledger).

## Symptom

Phase-3 borrow-stage failures (point ids are function-relative MIR points,
not source lines — see "Diagnostic" below):

| module | diagnostic | function / source |
|---|---|---|
| compiler.hir.archive.interface_action_archive | `74:1 call argument requires a checked non-retaining short contract` | `route_archive_install_stage_owned_v1` (20.hir/archive/interface_action_archive.spl:389, `route_archive_install_stage_v1(&mut owned, archive)`) |
| same | `76:1 cannot use local(59) because it was mutably borrowed` (RELATED 73) | same fn, :390 `RouteArchiveInstallStageTransferV1(owned, result)` — `result` still carries the `&mut owned` loan |
| same | `77:1 returned out of the short-borrow boundary` | same fn, :390 tail return of the struct holding `result` |
| compiler.driver.action_graph.artifact_service_bridge | `170:1 call argument ...` | `demand_artifact_claim_owned_v1` / `demand_artifact_commit_owned_v1` (80.driver/action_graph/artifact_service_bridge.spl:153 / :161, `&mut owned`); deleting both removes 170 |
| compiler.driver.action_graph.demand_compile_integration | `394:1 call argument ...` | one of the `&mut counters` calls (demand_compile_integration.spl:133/167/216/298); bisect was not stable under closure compiles, run 12 will name it |
| compiler.backend.linker.lld_sffi | `6:1 call argument ...` | `lld_elf_link` (70.backend/linker/lld_sffi.spl:48, `spl_dlsym_process_checked(..., &mut fptr)`) |
| lib.nogc_sync_mut.sffi.dynamic | `4:1`, `6:1 call argument ...` | extern status/out calls `spl_*_checked(..., &mut slot)` at sffi/dynamic.spl:95/108/139/166 (go-to-end dedups identical messages, so only two lines survive) |

The archive rows were bisected by single-file `compile` of a copy of the
module with the reference Stage 2 (`bootstrap-p2shard-4`): deleting only
`route_archive_install_stage_owned_v1` removes 74/76/77.

## Minimal repro (correct program, rejected)

```
struct Counter:
    n: i64

fn bump(c: &mut Counter):
    c.n = c.n + 1

fn main() -> i64:
    var c = Counter(n: 0)
    bump(&mut c)
    c.n
```

`stage2 compile fn_mut.spl --format=smf` -> rc=1,
`3:1: short borrow escapes: call argument requires a checked non-retaining short contract`.

## Root cause

1. `BorrowChecker.record_short_call_contract` (borrow_check/mod.spl) records a
   `ShortCall` for every direct call; `NLLChecker.check_short_call`
   (nll_short_calls.spl:182) turns any loan-carrying argument whose slot mode
   is not `read-short`/`mutate-short` into an escape.
2. The only producer of slot modes, `MirLowering.publish_short_call_contracts`
   (50.mir/_MirLowering/short_call_contracts.spl), fills the map only when
   `module.nogc_strict`; the driver's admission round
   (`driver_nogc_param_effect_admission_round_v1`) skips inference for
   non-strict modules: "Legacy modules retain their existing policy". No module
   in the tree carries `@no_gc(strict)`.
3. So in every compiled module the requirement is unsatisfiable by
   construction. Introduced by 9bb344bb1cf (pointer borrow hardening).
4. The 76/77 half: `record_call_result_loans` unions argument loans into the
   call result; `Result<(), Enum>` is layout class 2 ("unknown") and is treated
   as retaining, so the `&mut owned` loan outlives the call through `result`.

## Fix

`borrow_check/mod.spl`:
- `record_direct_call_contract_v1`: direct named calls record the short-call
  contract check only when `nogc_strict`. Strict modules are unchanged.
- `record_call_result_loans(..., direct)`: for a direct call in a legacy
  module, an unknown-layout (class 2) result does not inherit argument loans.
  Reference-bearing (class 1) results and short-marked destinations still do,
  so `fn pick(x: &mut T) -> &mut U` results keep their provenance.
- Indirect calls are NOT relaxed: `record_indirect_call_contract_v1` stays
  conservative outside strict mode by its stated design.

## Diagnostic

`primary_span` is a function-relative MIR point. `check_mir_module` now
resolves it (same numbering as `analyze_mir_borrows`) to the instruction span,
falling back to the function span, and records the function name
(`NLLError.function_name/source_line/source_col`, defaulted).
`_format_nll_error` (80.driver/driver_source_loading.spl) prints
`<line>:<col>: <msg> [fn <name>, mir point <n>]`. The uncalled duplicate in
`driver_helpers.spl` was deleted. With names in the message, go-to-end will
stop deduping identical per-function lines, so run 12 can show MORE borrow
lines for the same modules; that is not a regression.

## Verification

- Red: reference Stage 2 rejects `fn_mut.spl` and the archive module copy
  (exact run-11 text). Repros under `build/repro/` of the p3wa worktree.
- Green: NOT executed. A compiler with this fix needs a Stage 2 rebuild.
  Specs added to `test/fixtures/compiler/nogc_mir_call_loans_probe.spl`
  (legacy accept x3, legacy reference-result reject, strict unknown-layout
  reject). The Rust seed cannot run this probe faithfully: it fails the
  pre-existing strict case "read and mutable slots aliased" on the unmodified
  checker too, and does not reproduce the legacy rejection on the baseline.
- Strict mode: `@no_gc(strict)` on the trivial fixture fails earlier with
  `NOGC-CONTRACT-001 ... ownership report does not cover exact local function
  identities` (pre-existing, separate).

Related: `extern_out_param_no_nonretaining_contract_2026-10-24.md` (strict-mode
gap for the extern out-param sites).
