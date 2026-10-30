# Stage 2 p2_add HIR-shard SIGSEGV: repro status and lldb evidence (2026-10-30)

Status: OPEN (not reproduced on release/1.0.0 HEAD; HEAD Stage 2 does not link)

## Original symptom
`[hir-shard] owner=0/1@0 status=CRASH exit=-139` while lowering
`compiler.bootstrap_admission.p2_add`, then `error: HIR aggregate failure`;
stage2-sanity.env status=fail. Evidence: attempt-20261023T220606-92456
`stage2-sanity.env.frontend-driver.log` (candidate sha 5556d2fd..., not retained).

## What was tried (2026-10-30)
1. Rejected beta.14 candidate (sha 294d0e94...): lowers p2_add fine; no SEGV.
2. Fresh diagnostic Stage 2 built by the seed from 3c09ef218c5 (a branch
   358 commits BEHIND release/1.0.0 99f6247fcf3). HIR shard passes
   (`[hir-shard] done shard=0/1 lowered=1`); the build instead dies with
   SIGABRT:
   `flat pool encoder string builder append failed site=text.value item=0 input_length=-1 result=0`
   lldb (final native_build_worker replayed with its captured argv+env):
   ```
   stop reason = signal SIGABRT
   #5 rt_panic
   #6 compiler__frontend__core__flat_pool_codec__flat_pool_builder_push + 576
   #7 flat_pool_enc_text_into + 192
   #8 flat_pool_enc_text + 88
   #9 _Ast__decl_nodes__flat_decl_pools_dump + 1112
   #10 module_assembly__flat_pools_dump_all + 84
   #11 module_assembly__flat_pools_dump_for_cache + 96
   #12 module_assembly__parse_and_build_module_with_scope_owner + 1956
   #14 frontend__frontend_parse_or_restore + 1012
   #18 CompilerDriver.lower_and_check_retained_owner_impl + 6464
   #21 _cli_native_build + 18428
   ```
   This is the already-fixed defect
   stage2_mir_shard_flat_pool_text_len_minus1_2026-10-22.md (a dangling
   pool text handle across the transient scope during the frontend-cache
   capture dump); release/1.0.0 carries the capture sanitize, per-path
   capture dedupe and parser_promote_transient_owners fixes.
3. Stage 2 from release/1.0.0 HEAD 99f6247fcf3 (same seed argv): compiles,
   but the LINK fails against the stale stage2-runtime-authority:
   `Undefined symbols: _rt_io_file_close_value` (from
   lib.nogc_sync_mut.sffi.fs io_file_close). A HEAD Stage 2 needs a
   runtime-authority rebuilt from the current src/runtime before the HIR
   SEGV can be checked.
4. Branch fix/stage2-frontend-smoke-sigsegv commits 2239ad0e68c (HIR codec
   presence-guarded dict store; p2_add SIGSEGV in hir_fn_scalars_at_v1) and
   4fe767530f3 (MIR closure emission) are ALREADY on release/1.0.0 as
   e606125a541 and 31cb5365440 (cherry-pick conflicts only because the
   content is present).

## Hypothesis
The Oct 23-24 exit=-139 is most likely one of the already-landed fixes'
targets (HIR-codec nil dict values / fold-walker optional payloads /
transient pool text reclaim). Not confirmed: no current-HEAD Stage 2 exists.

## Repro
Scripts (scratchpad, session 308676d8): build_stage2.sh (seed native-build of
src/app/cli/bootstrap_main.spl, --runtime-bundle core-c-bootstrap
--entry-closure --mode one-binary) and
`SIMPLE_SCV_INVENTORY_COLD_INIT=1 sh sanity_p2.sh <stage2> <fresh-out>`
(native-build p2_add, SIMPLE_BOOTSTRAP unset, private HOME/TMPDIR/cache).
To debug a child: copy the binary to a unique name, capture child argv+env
with `ps eww` polling, replay under `env -i <env> lldb -- <argv>`.

## Next step
Rebuild stage2-runtime-authority from HEAD src/runtime (provides
rt_io_file_close_value), relink HEAD Stage 2, rerun sanity_p2.sh.
