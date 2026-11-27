# Windows Phase 3/4 open verification inventory (2026-10-24)

Status: OPEN; finite repair and verification queue, not compiler qualification.

## Later terminal evidence: old producer and partial objects

The earlier live-collector observations below are historical. The original
Phase 3 collector subsequently terminated with log overflow (exit 125,
64 MiB cap): 873 HIR rows passed, 24 crashed, and 544 of 1,441 were
unattempted. Its terminal receipt is
`C:/dev/simple-phase34-resume-20261024/phase3/build.receipt`. It produced no
qualified Phase 3 compiler. The source checkout advanced during that diagnostic
run, so the run also lacks a consistent frozen-source admission.

Separate, isolated per-unit builds used the unchanged Phase 2 producer SHA256
`70ce821aa79dc190cb6fb206ce90651f5e93cef9e46a33963ab992a13e70e19b`,
with 24 threads and normal source/cache validation. The final 32-unit epoch
terminated with 29 passes and three failures. Together with nine earlier passes,
38 requested objects have clean process receipts, nonempty AMD64 COFF files,
positive symbol counts, and retained size/SHA256 evidence. The authoritative
summary and format proof are:

- `C:/dev/simple-phase34-resume-20261024/partial-objects/worker2/epoch3/summary.sdn`
- `C:/dev/simple-phase34-resume-20261024/partial-objects/worker2/epoch3/coff-proof.sdn`

These are partial diagnostic objects. Their individual entry/closure identities
do not establish reuse in the original full Phase 3 build or reduce its admitted
remaining-object count. No additional old-producer epoch is scheduled.

| Original entry | Observed terminal boundary | Result |
|---|---|---|
| `src/compiler/10.frontend/core/interpreter/value.spl` | MIR worker passed and requested 39,597-byte object was emitted; collector later timed out and reaped the job | FAIL, exit 124 |
| `src/lib/nogc_sync_mut/ptr/raw.spl` | MIR worker passed and emitted a 2,725-byte intermediate object; parent access violation prevented requested output publication | FAIL, normalized exit 139 (`0xC0000005`) |
| `src/lib/common/json/tokenizer.spl` | MIR worker passed and emitted a 23,997-byte intermediate object; parent access violation prevented requested output publication | FAIL, normalized exit 139 (`0xC0000005`) |

The first failing boundaries are process completion and parent output
publication; no retained crash stack proves their root causes. A worker PASS
or intermediate object cannot substitute for a successful parent receipt.
Per-row evidence is retained in epoch directories `06`, `16`, and `30` as
`failure-boundary.sdn`, alongside original arguments and collector receipts.
Exact regressions for all three are prepared in
`partial-objects/worker2/new_producer_regressions.py`; they have not run with
the repaired producer and require clean completion plus the requested object.

The repaired seed SHA256
`5d86a2e420d1be12d75ffcd50b41676ab3138b4e947770d0a834962b6f35660a`
passed five canonical preflight checks at frozen source `a3ea4530e3a`.
Its Phase 2 build was live when this evidence was recorded. This is seed
preflight evidence only, not Phase 2 admission or Phase 3/4 qualification.

Inventory source anchor: release/1.0.0 commit
`0275bb4815b` (merge of PR #4327). The audit inspected the last week's
Windows/bootstrap bug records and workaround markers in active compiler and
bootstrap-builder owners. It did not execute the regressions below. Historical
PASS records retain their original producer/source scope.

The campaign owner reports Phase 3 HIR access violations in the retained log
`C:/dev/simple-phase34-resume-20261024/phase3/.build.log.tmp.38652`. Collector
PID 38652 and compiler PID 36072 are still live at this handoff; independently
runnable rows continue. Queue
`C:/dev/simple-phase34-resume-20261024/phase3/cache/default/frontend/queue-36072-0`
contains three reported terminal `CRASH` rows (owner generation zero), for
`common/io/traits`, `common/binary_io`, and
`compiler/70.backend/feature_caps_types`. Individual terminal rows do not
make the live collector terminal. Phase 4 from this candidate remains blocked
pending a successfully produced compiler and its Hello compile-and-execute
gate; partial cached objects do not qualify it. These details record retained
campaign evidence and the owner's handoff, not a new crash reproduction or
a terminal Phase 3/4 verdict.

The queue makes the requested post-Phase-4 Windows/workaround pass finite and
reviewable. It does not narrow the user's broader objective or declare bugs
outside this queue resolved. Newly observed failures require their own retained
evidence and cause classification. Preserve live frozen builds and isolated
caches while independent repairs proceed.

## Execution and removal rules

Below, `P` denotes an explicitly identified, immutable, newly Hello-tested
compiler, with source/runtime/toolchain hashes recorded. `FULL` denotes a
qualified full CLI with a working executable test runner. Select the actual
Windows target consistently with the producer/runtime ABI; do not silently
switch GNU/MSVC or use a seed as full-CLI evidence. Use private output paths.
The user selected 24 jobs: pass `--threads 24` to native builds and use
24 build/test jobs where the selected runner supports them. Keep frontend
process admission separate from that backend thread count.

For a standalone native fixture, the route is
`P native-build <fixture>/main.spl --target <Windows triple> -o <private.exe>`,
followed by executing that exact output and checking its exit/output. A BDD
spec needs the executable-spec runner and positive assertion counts; a
successful compile alone does not execute its assertions. Native lowering
regressions must traverse native lowering, even if interpreter assertions pass.

Remove a workaround only after a producer carrying the owner repair accepts
the original, unmodified source form and its output behaves correctly. Then
verify the actual affected production target, remove the annotation and
workaround together, and rebuild the affected Phase 3/4 consumers. A typed or
rewritten control proves the workaround, not the underlying compiler repair.

## Finite queue

| Cause and current evidence | Exact next route and acceptance gate |
| --- | --- |
| Inferred MIR receivers: owner repair recorded, native verification missing. Active markers in codegen, linker and driver owners refer to `mir_unresolved_method_inferred_receiver_2026-10-24`. | `P compile test/01_unit/compiler/mir/inferred_receiver_method_resolution_spec.spl --format=smf` traverses the reported failing lowering boundary. Execute its assertions through the native/full-CLI test route as well. The companion compiler-fix document explicitly excludes Dict-index optional semantics, closure chains and several context-dependent linker cases; do not remove those markers based on this spec alone. |
| `Result.err()` enum payload: owner fix committed but rebuilt-producer execution missing; `backend_plugin/loader.spl` uses a direct-match workaround. | Native compile/run `test/fixtures/compiler/p3fix_mir/errunwrap/main.spl`; require stdout `err` and exit zero. Restore the original `validated.err().unwrap()` call only after this original-form fixture and the actual plugin-loader target pass. |
| Result-try record array provenance: `native-result-ok-record-inference-20261018` markers remain in grouped bootstrap owners. | Execute `test/01_unit/compiler/mir/result_try_record_array_workaround_spec.spl` with real assertions. Retrieve and bind the separate unannotated four-case root-fix candidate documented in `native_result_ok_record_inference_2026-10-18.md`; it is not silently present in this release package. Require that original case and the affected grouped target pass without explicit record-binding annotations before removal. |
| Windows expression-statement payload crash: owner repair authored; prior rejected producer also crashed the TCP dependency capsule. | Native compile/run `scripts/check/cert/redeploy_gate/fixtures/stage2_mir_retention.spl`; stdout must be `3`. Execute the controls in `test/01_unit/compiler/hir/expr_statement_payload_spec.spl` and native `expr_statement_payload_native.spl`. Native compile/run `test/fixtures/compiler_entrypoint/windows_tcp_owner/main.spl`; expected stdout is in its adjacent `expected.stdout` (`Windows TCP owner PASS`). |
| Windows public entry-object publication: read-only handles lack flush authority. Retained-writer capability has qualified native C subset evidence, but SPL fresh/grouped/reuse integration remains unrun. | Exercise the actual public `--emit-entry-object` route, including source and destination receipt/object/directory barriers, using each affected fresh/grouped/reuse path. Require successful immutable publication with retained authority and negative controls. `windows_entry_object_readonly_flush_authority_2026_10_18.md` and `windows_cache_retained_seal_authority_2026_10_18.md` retain the ownership constraints; another C-only capability PASS cannot close driver integration. |
| Four Windows AOT defects under an older producer: `[u8]` parameter copying, typed byte writes, struct-valued Result `?`, and isolated-thread lambda lowering. | Recreate the original minimal native comparisons described in `windows_producer_byte_array_aot_defects_2026-10-20.md`, bind them to `P`, and assert exact bytes, integer fields and nonzero thread handle plus actual worker completion. That record supplies no complete tracked regression command; fixture creation/recovery is still required. Workarounds in runtime-owner consumers cannot establish root-fix closure. |
| Windows smux memory and SOSIX qualification: old-producer attempts exceeded the enforced RSS cap; source boundary controls do not execute product behavior. | Build using the new exact producer, preserve original-form compiler regressions, and retain process-tree RSS/elapsed/terminal cleanup receipts. Native compile/run `test/fixtures/compiler_entrypoint/smux_sosix_host/main.spl`; expected stdout is `sosix-host-boundary-ok`. Execute `test/03_system/tools/smux_sosix_boundary_spec.spl`, `smux_windows_shared_clients_spec.spl`, and `smux_windows_owner_lifecycle_spec.spl` with the qualified runner. Do not attribute memory ownership from a terminated peak alone. |
| Phase 4 executable-spec runner: latest sanity follow-up reports an entry-only interpreter function map, rejecting imported `describe`/other functions after infrastructure repair. | Run actual compiler/library/tool BDD specs with `FULL`, positive executed assertion counts and imported functions. Diagnose `src/compiler/70.backend/backend/interpreter.spl` module registration against the actual failing spec. `phase4_full_cli_sanity_findings_2026-10-20.md` records the remaining layer; successful CLI version/help or linking is insufficient. |

## GNU prerequisites and downstream qualification

`windows_gnu_lane_blockers_2026_10_24.md` records seed-target/toolchain,
LLVM-provider and linker-runtime failures. Revalidate the actual GNU authority
before claiming them fixed. The LLVM environment-scrub explanation is unproven:
the detector re-reads host configuration, while the configured MSVC prefix
contains `LLVM-C.dll` and lacks the GNU import library. The newer
`windows_gnu_llvm_prefix_rejection_diagnostic_2026_10_24.md` distinguishes this
provider mismatch. Diagnostics alone do not install/admit a GNU provider.

Require explicit `x86_64-pc-windows-gnu` Hello compile/run after rebuilding the
hosted-target guard; arch-only target success proves only the recorded
workaround (`windows_gnu_hosted_c_plan_rejected_2026-10-24.md`). The Stage 4
five-root wrapper repair likewise needs actual full-CLI execution, beyond
the syntax-only evidence in `stage4_seven_source_roots_rejected_2026-10-24.md`.

The release-packaging record
`rc1_packaged_simple_is_bootstrap_cli_specs_fail_smf_compile_2026-10-20.md`
remains a downstream gate: the packaged Windows executable must be the
qualified full CLI and must execute specs, rather than accepting bootstrap
CLI degradation. Do not publish/tag as part of this inventory.

## Evidence reuse and final gate

Do not reopen already qualified capacity SDK/registration controls, async
stdio transport or SOSIX UTF-8 boundaries merely because an older paragraph
describes their prior failure. Their broader compiler integration may still
need new-producer evidence. The later sanity follow-up repairs the cold-entry
`run` gap; it must not be listed as the original unresolved failure. Linux-only
historical performance reports were not counted as current Windows failures.

Completion still requires the actual requested Windows and workaround repairs,
Hello-gated Phase 3 to Phase 4 execution, full-CLI tests, and the requested
post-repair Phase 3/4 pass, with reviewed fixes merged onto release/1.0.0.
This inventory supplies no PASS for any of those missing runtime gates.
