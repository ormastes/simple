# Target 6 tracked-move native ABI diagnostic

Status: OPEN. The V4 tracked-move fixture still has no executable cold or warm PASS.

The available no-stub pure-Simple Stage 2 compiler built the 66-module tracked-move fixture three times with bounded runs after source-only attempts to remove optional-trace forwarding and then optional Git-listing text. Each native build completed HIR and MIR and linked. All three executables exited 2 during the first cold inventory refresh, before publishing an inventory generation. The runtime reported `rejected invalid array handle before dereference`; the owner returned `cold-init-listed-no-sources`. The temporary fixture repository did contain the expected tracked source: `git ls-files` reported `H src/compiler/linker_lifecycle.spl`.

The opt-in trace run produced malformed numeric output instead of an ordinary trace record. Neither the trace boundary nor the Git-listing result rewrite improved the cold result, so both source candidates were removed. The three-cycle verification cap is reached. This evidence does not locate the exact ABI defect inside process output, text splitting, or trace formatting.

The next diagnostic is the focused `test/fixtures/compiler/target6_process_output_abi_probe.spl`. It distinguishes literal text splitting, Git process status, Git stdout, and splitting returned stdout without an SCV inventory. It is authored but unexecuted. After locating and repairing that boundary, rerun the V4 tracked-move fixture once and require cold, staged-intermediate, final-plugin, and unchanged warm admissions before any Item 6 cutover claim. Current-source Stage4 and matched compile time/RSS cohorts remain open.

Local logs: `build/mini_builds/target6_tracked_move_refresh_probe/build_v4_trace.log`, `build_v4_git_lines.log`, and `build_v4_concrete_trace.log`; linked probes and their temporary fixture repositories are diagnostic artifacts, not release receipts.

## Focused boundary and batch follow-up

The 44-module no-stub native process-output probe passed both ordinary
`git rev-parse` stdout splitting and the SCV cold path's exact `ls-files -t
--cached --others --exclude-standard -- src` request on the isolated worktree.
This narrows the earlier invalid-array result away from that direct process
facade call and text split in isolation; it does not prove the 66-module SCV
call graph correct.

The SCV Git-event handoff now has an explicit validity record instead of an
optional batch result. A bounded 66-module no-stub native build linked, but
its executable exited 139 before publication. `addr2line` maps the active
frames to `spl_str_slice` called from
`CompilerInventoryTraceV1.captured_pointer`, consistent with the previously
recorded optional-trace forwarding defect. The batch change is a source
candidate, not an executable V4 PASS. This turn's third build/run cycle is
complete; further repair and rerun belong to the next bounded cycle. The
new build log is `build/mini_builds/target6_tracked_move_refresh_probe/build_v4_batch_result.log`.
