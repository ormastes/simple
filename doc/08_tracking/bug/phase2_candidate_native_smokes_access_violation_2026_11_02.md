# Phase 2 candidate native smokes fail with access violations

Status: OPEN (P1) — this candidate failed both native smoke invocations before execution; cause is unknown.

## Candidate and build

Candidate: `C:/dev/p3new/p2_layoutattr_71d_20261102/attempt/stage2.exe`.
Candidate SHA256:
`24164F6F390716ECF4DD021C0AD0D9103CC801670AB92D4E49E22269B66F3C38`.
Source commit: `c9078245fa1926391ee8a2fd48a56c8c87cbaa6b`.
Clean producer source tree: `a48366bcdfd56a57809d6d3d8dd4830fb600338a`.

A fixed-seed native build from clean source commit `c9078245fa1926391ee8a2fd48a56c8c87cbaa6b`
(tree `a48366bcdfd56a57809d6d3d8dd4830fb600338a`) using pinned FC56 seed
binary SHA256 `FC56D4B5FC384EA93ED20BEFD4503FF6E27DB7734214CA45E072B4DF1B081828`
reports 1545 compiled, zero failed, 1543 objects, and successful linking
(`attempt/result.txt`, `attempt/native-build.log`). The source preflight record
is `smoke_preflight.sdn`, SHA256
`46B7A01BA2FD7BDE57B518602BE1F8D592F131009195B519137ECF6A40F9CA7F`.
The input manifest's `producer_source_index_tree` value
`9023adc607c125c67c7fcfe60b6d7a7be1db56ee` is the smoke fixture index after
adding the three staged fixtures, not the producer source tree. No compiler
rebuild or source change is part of this tracking update.

## Two cases in one smoke attempt

Both native smoke invocations exited `-1073741819` (`0xC0000005`) before
executing a program. Each produced zero objects and no executable:

| Case | Failure phase and unit | Elapsed | Peak process-tree RSS |
|---|---|---:|---:|
| `hello` | `native_compile`, `app._scratch_ed.p2_candidate_smokes_20261102.hello` | 235.0 s | 0.93 GB |
| `variable` | `mir_lower`, `app._scratch_ed.p2_candidate_smokes_20261102.variable` | 82.9 s | 0.71 GB |

The retained summary is
`C:/dev/p3new/p2_layoutattr_71d_20261102/smokes/summary.sdn`, SHA256
`40BE412781CACB8694A1357617ECE554BCE2BBC1BD194BB9C0D34F745C73F007`.
It records nine admitted threads per invocation, zero raw cache object files,
zero executed programs, and reaping of the candidate process. The input manifest
is `smokes/input_manifest.sdn`; case-level build and run records and stderr are
under `smokes/hello/` and `smokes/variable/`.

Cache isolation was incomplete. The input manifest's private-cache statement
did not cover the HIR driver cache: the driver reads `SIMPLE_HIR_CACHE_DIR`,
while the native-cache argument was supplied only to the frontend. Retained HIR
artifacts used `/tmp/simple-cache`. In the variable case, the HIR store was
skipped because free disk space was 573,579,264 bytes, below the 2 GiB reserve;
the counters report `stores=0` and `io_failed=1`. Canonical source authority
was published normally, but this evidence does not establish fully private
HIR cache isolation or a successful HIR cache-store result.

Offline LLDB analysis of retained WER/minidump evidence is recorded in
`smokes/hello/offline_lldb.txt` (SHA256
`6A852186239C49D5BD7E868F621969CF546352AB864817E68D80EABC38CD7B03`) and
`smokes/variable/offline_lldb.txt` (SHA256
`CB86AC48BFC1F412069F39B3BDCAE9226A6A4C87FABFA4440DE25ECDBFA6974B`). For
Hello, the fault is at `MirToLlvm.translate_const+215`, called from
`core_codegen` through instruction/block/function/module translation and the
LLVM adapter, after MIR was complete. For the variable case, the fault is at
`mir_expr_symbol_id_value+68` on `movq (%rsi), %rax`, reached from
`lower_expr_impl`, `lower_bootstrap_print_call`, and
`lower_module_transient_scoped` during MIR lowering.

The variable faulting function is the same function observed in the older
`47D8...` candidate diagnostic. That recurrence does not establish a shared
source cause, and no use-after-free claim is made. The Hello and variable
boundaries remain distinct observations from this one candidate attempt.

These are two failed cases from one candidate smoke attempt, not two confirmed
independent defects. No common root cause is established. An earlier diagnostic
reported a variable-reference AV for candidate prefix `47D8...`; the same
faulting MIR function recurs here, but no exact matching candidate hash or
canonical tracking report was found in current release records, so this entry
does not merge or reclassify that history.

The same attempt included a LayoutAttr codec fixture, but the summary explicitly
records `layout_attr_fixture_executed: false`. This entry does not establish a
LayoutAttr result or qualify the candidate for Phase2 or Phase3.

## 2026-11-03 blocker (lane p1blk)

All retained evidence (candidate exe, `smokes/summary.sdn`, per-case stderr) is under
`C:/dev/p3new/p2_layoutattr_71d_20261102/`, which fix lanes are forbidden to touch. No
faulting address or stack has been recorded. The doc's own cache note means the
HIR-cache contamination is not ruled out (the driver reads `SIMPLE_HIR_CACHE_DIR`, but the
private cache was passed only to the frontend). Next step for the Phase 2 owner: rerun both
smokes with `SIMPLE_HIR_CACHE_DIR` set to a private empty dir, and capture a minidump of
the 0xC0000005.

## 2026-11-05 premise check (lane p1c-p2cav)

Still OPEN; not closed and not re-scoped as fixed, because it cannot be re-run here.

- **Premise still current.** Nothing in today's policy (nil only as `T?` absence, no `Any`
  outside unsafe, panic-free safe code, mono removed) makes the two smokes invalid: `print`
  of a hello string and of a `val` local are ordinary safe programs that a Phase 2 candidate
  must compile.
- **Fault site source is trivially safe.** `mir_expr_symbol_id_value(symbol: SymbolId) -> i64`
  (`src/compiler/50.mir/_MirLoweringExpr/expr_dispatch.spl:185`) is just `symbol.id`.
  Faulting on `movq (%rsi), %rax` there means the caller passed an invalid `SymbolId`
  reference, so the defect is in how candidate-compiled code moves the value, not in this
  function.
- **Source moved a lot since the candidate.** Candidate source `c9078245fa1` (2026-11-02).
  Since then, release/1.0.0 carries 10+ changes to `expr_dispatch.spl` alone that target this
  kind of stage2 value-transport miscompile. Among them: `cd656fa2d69` (local_map mirror for a
  mis-bucketed local index; that fixes `val`-then-use "undefined variable"),
  `87aaaa999c7` / `735ceebbfc6` (no by-value `HirExpr` hops on the stage2 binding path),
  `6406b3699ef`, `26becc4bd64` (stage3 AV +0xd1 through scalar accessors), `dc662dde275`.
  None of them is proven to fix either case.
- **Older stage2 did not fail this way.** The frozen stage2 from `ef0681fc0e1` (2026-10-27)
  compiled the stage3 objects and stage3 hello
  (`stage2_local_symbol_index_bucket_tagged_id_2026-11-03.md`). So this candidate's failures
  are either a regression in `ef0681fc0e1..c9078245fa1` or are specific to this candidate.
- **Repro blocked.** The only stage2 binary on the host is under `C:/dev/p3new`, which fix
  lanes may not touch, and it is in use. Building a fresh stage2 from the current base did not
  fit the host memory guard: 42.6 GB free commit at 13:40 KST, with a 70 GB build running.
- **Next step (owner):** build a stage2 candidate from the current release/1.0.0 tip, then
  rerun the `hello` and `variable` smokes with a private empty `SIMPLE_HIR_CACHE_DIR`. If both
  pass, close as superseded and cite that candidate's SHA256. If either fails, take a minidump
  and bisect `ef0681fc0e1..<tip>` on the smoke that fails.

## 2026-11-05 rerun on stage3 43 (lane p1w-p2av): no access violation

Binary: `s3_fable43.exe`, SHA256 `615859c5c2815f7164fa092ca62d95ad6f4ef5753cc76a3860beb25b827fccd7`
(built from release/1.0.0). I ran each case on its own as a single module. I used an adapted
copy of `C:/dev/p3new/s3sanity/run_case_g43b.ps1`, with `SIMPLE_HIR_CACHE=0` and a private
cache and output dir. It ran `native-build --entry-closure --entry test/s3sanity/<case>.spl
--target x86_64-pc-windows-gnu --backend llvm --keep-going`, then renamed the entry symbol and
linked manually with llvm-mingw clang.

| Case | Source | Build wall | Peak RSS | Run |
|---|---|---:|---:|---|
| `hello` | `print("hello")` | 464 s | 2.21 GB | rc=0, stdout `hello` |
| `variable` | `val s = "x"; print(s)` | 335 s | 2.30 GB | rc=0, stdout `x` |

Neither case hit `0xC0000005`. Both reached the stages where the candidate had faulted:
`translate_const` (native_compile) and `mir_expr_symbol_id_value` (mir_lower). Each produced its
`__simple_main` object. The driver's own rc=1 comes from the known 43 auto-link/entry-rename
step, which the gate recipe works around with a manual link. It is not a crash.

Verdict: the failures do not reproduce on the current pipeline. They are superseded by the
transport fixes listed in the premise check above. Status: verification-pending. Close this
once a Phase 2 stage2 candidate built from the current tip passes the same two smokes.

## 2026-11-05 compiler-defects sweep source audit (winboot-rel100 lane)
Nil-safety audit of the two fault sites (current source):
- `MirToLlvm.translate_const` / `translate_const_value` (src/compiler/70.backend/backend/_MirToLlvm/core_codegen.spl) match over MirConstValue, which has exactly 8 variants, all covered; per-variant type guards route ptr/int/float/i1 and an invalid const type records E-BACKEND-LLVM-CONST-TYPE via the fail-closed codegen_error. Defensive fix landed: an explicit `case _` arm in both translators records E-BACKEND-LLVM-CONST-GARBAGE (fail-closed, no object) instead of silently falling through on a garbage discriminant — the exact silent-fall-through class the stage2_symbol_display_name_option_transport workaround documented.
- `mir_expr_symbol_id_value` (expr_dispatch.spl:185) is the single field projection `symbol.id`; no in-language guard exists for a caller-passed invalid reference, consistent with the 2026-11-05 premise check (candidate-compiled value transport, not a source defect).
Host evidence: new test/01_unit/compiler/backend/llvm_const_value_total_match_guard_spec.spl 4/4 PASS; neighboring llvm_pointer_integer_constant_contract_spec.spl 8/8 PASS (seed interpreter). The AV repro itself still needs a fresh stage2 candidate from current tip with a private SIMPLE_HIR_CACHE_DIR.
