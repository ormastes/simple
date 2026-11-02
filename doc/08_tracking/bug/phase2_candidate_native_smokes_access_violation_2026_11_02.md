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
