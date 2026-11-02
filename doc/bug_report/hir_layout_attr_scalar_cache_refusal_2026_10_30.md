# LayoutAttr scalar producers prevent HIR cache publication

Status: OPEN (P1) — source fix merged; producer requalification pending. Live Phase3 source was not changed.

## Observed evidence

Source: `b81f148624f8c39dac0b3f865a8270472dd9fbbd`.
Producer SHA256: `76c04806d8321705424b7ebbf11ddfbe5726771ad4033696d4b308c24e8d33fd`.
Runtime archive SHA256: `5d7399d0c9c6b906b2981028c15185829ab35c960042bffb9d41e358ef8820e8`.
Windows GNU Phase3 attempt2 stderr:
`C:/dev/simple-mono-expected-result-20261029/build/bootstrap/phase3-diagnostic-b81f148-attempt2-20261030/stderr.log`.

First representative refusal, line58944:

```text
[hir-cache-store] refused reason=decode detail=reader kind=malformed detail=nil_in_non_optional_scalar:LayoutAttr.has_explicit_align line=11759/11916 token=N module=src/compiler/00.common/diagnostics/span.spl; entry not stored (further decode refusals are only counted)
```

The next two workers reported the same required-field failure for
`src/app/cli/native_build_mir_selective_admission.spl` and
`src/lib/common/io/types.spl`. Three shard summaries recorded 762 cache hits,
842 misses and 842 store refusals, with zero stores. Their `lowered=0` counter
counts successful new cache publication, not all actual HIR lowering work.
This prevents newly computed HIR from being reused by subsequent compilation.
It does not establish why the earlier attempt1 process exited.

## Cause and repair

`LayoutAttr` uses required `has_explicit_align: bool` and `explicit_align: i64`
fields. `parse_layout_attrs` still constructed the former optional representation:
it omitted the presence field and supplied `Some(value)` or `nil` as the scalar
value. The default, C-repr and packed factories omitted both fields.
The generated codec correctly refused the resulting required-field nil token.

Initialize the pair explicitly in all four owned production producers. The
parser preserves its existing power-of-two validation: 1 and16 are valid;
0 and3 leave the flag false and payload0. The generated decoder and cache
publication checks remain unchanged. No cache version change is needed: valid
wire layout is unchanged, and malformed entries were never published. The
source repair is present in release commit `8aafa6cf8544e4e2f126540a11cdd5c7139341dc`;
this does not establish that a producer built from that repair can requalify
the frozen Phase3 route.

## Focused validation for Luna

Run with a hash-admitted full CLI and the repaired source closure:

```text
<admitted-full-cli> test test/01_unit/compiler/hir/layout_attr_scalar_codec_spec.spl --no-session-daemon --mode=interpreter
```

The five cases exercise the real generated LayoutAttr codec from the parser
and all three factories, assert exact scalar values and byte-stable reencoding,
and require rejection of malformed nil presence/value fields. Runtime execution
has not occurred. Compiler cache behavior must subsequently be checked with a
producer rebuilt from this fix and a provenance record binding it to the source
revision; a frozen producer without that binding cannot establish whether the
repair is present.

## Current producer requalification attempt (2026-11-02)

The canonical Phase3 PC-compat continuation attempt failed before producing an
object. Its result record is
`C:/dev/p3new/cgprobe/tldr_api_fix_owner_artifacts/canonical_phase3_pccompat/campaign_result.sdn`.
The retained record SHA256 is
`0649DFD7818DA5977878AF67CC257E088689507A2467B522C3F1DFE2F5BD5F3F`.
It records frozen producer `C:/dev/p3new/stage2.exe` (SHA256
`1907A037F83463377B7148C19CE6EF12CC0487E7C33A68BBD5491231C9728100`) against
source snapshot `scv-revision-v1-4c79f68c48001378e755a575022362dadf09237b2209f3dd05794c9219749667`
(source inventory generation 14, digest
`59d9d829d774538f4223cb4d764dd6c0573335a163dea91eb5ca862e2751c6c3`). The
1489-module parse closure used request digest
`d0bed4b1fcbf0dacefbbc1dc9d7ad76373228b3430a1d2427cc154559e8cb20a`. Although
90 threads were requested, admission was HIR 4, MIR 3, and file workers 3, with
10 descendant processes at peak.

The run lasted 822.8 seconds, exited 1, was not killed, and produced zero
objects; stage3 was not linked. The first failure was
`nil_in_non_optional_scalar:LayoutAttr.has_explicit_align` at line 913/1449,
token `N`, while compiling `src/lib/common/plugin/iface_id.spl`. HIR completion
receipt publication then failed and blocked subsequent HIR ledger claims. The
result record reports one terminal HIR PASS receipt marked UNCACHED, with
`hir_done_ms=-1` and an empty object. This is not a completed module or a valid
codegen pass. It also reports three HIR worker errors, three MIR worker errors,
four failed workers, and zero completed workers. Evidence files are
`native-build.log`, `native-build.log.err`,
`native-build.log.cap`, `result.txt`, and `stage3.exe.go-to-end.sdn` under the
attempt root above.

The producer/source association is not authenticated by a build manifest; the
producer is identified by the result record's path and matching SHA256. This
attempt therefore proves that this frozen producer failed against the recorded
snapshot, not that a producer built from the merged repair failed. No
executable or Hello run was produced, and no Phase3 qualification is claimed.
The bug remains OPEN P1 until a provenance-bound producer containing commit
`8aafa6cf8544e4e2f126540a11cdd5c7139341dc` passes the focused codec regression
and relevant cache/build requalification.

## Current candidate did not reach LayoutAttr requalification (2026-11-02)

Candidate `C:/dev/p3new/p2_layoutattr_71d_20261102/attempt/stage2.exe`
(SHA256 `24164F6F390716ECF4DD021C0AD0D9103CC801670AB92D4E49E22269B66F3C38`)
was built from source commit `c9078245fa1926391ee8a2fd48a56c8c87cbaa6b`.
The clean producer source tree was `a48366bcdfd56a57809d6d3d8dd4830fb600338a`
and the pinned FC56 seed binary SHA256 was
`FC56D4B5FC384EA93ED20BEFD4503FF6E27DB7734214CA45E072B4DF1B081828`. The
retained build result reports 1545 compiled, zero failed, 1543 objects, and
successful linking. The input manifest's `producer_source_index_tree`
`9023adc607c125c67c7fcfe60b6d7a7be1db56ee` is the later smoke fixture index,
not the producer source tree.

The following canonical native smoke invocations then failed before execution,
with the same Windows access-violation status `-1073741819` (`0xC0000005`):

- `hello`: native compilation failed in unit
  `app._scratch_ed.p2_candidate_smokes_20261102.hello` after 235.0 seconds;
  zero objects, peak process-tree RSS 0.93 GB.
- `variable`: MIR lowering failed in unit
  `app._scratch_ed.p2_candidate_smokes_20261102.variable` after 82.9 seconds;
  zero objects, peak process-tree RSS 0.71 GB.

The retained summary is
`C:/dev/p3new/p2_layoutattr_71d_20261102/smokes/summary.sdn` (SHA256
`40BE412781CACB8694A1357617ECE554BCE2BBC1BD194BB9C0D34F745C73F007`). It
records nine admitted threads per invocation, zero raw cache object files,
zero executed programs, and `layout_attr_fixture_executed: false`; the
LayoutAttr codec fixture therefore did not run. Detailed build and case records
are `attempt/result.txt`, `attempt/native-build.log`, each case's
`build-result.txt`, `run-result.sdn`, and `native-build.log.err` under the same
candidate root.

These two failed cases belong to the same candidate smoke attempt. They do not
establish two independent compiler defects or a shared root cause. The earlier
`47D8...` variable-reference AV has no matching exact candidate hash or report
in the current release tracking records; no causal relationship is asserted.
This newer candidate failure supplies no LayoutAttr codec/cache evidence and
does not change this bug's OPEN P1 status or qualify Phase2/Phase3.
Cache isolation in that smoke attempt was incomplete: HIR artifacts used
`/tmp/simple-cache`, and the variable case skipped its HIR store below the
2 GiB free-disk reserve. Offline minidump analysis places Hello at
`MirToLlvm.translate_const+215` after MIR completion and the variable case at
`mir_expr_symbol_id_value+68` during MIR lowering. The latter function also
appeared in an earlier `47D8...` variable AV, but no source cause, shared cause,
or use-after-free claim is made. See
`doc/08_tracking/bug/phase2_candidate_native_smokes_access_violation_2026_11_02.md`.
