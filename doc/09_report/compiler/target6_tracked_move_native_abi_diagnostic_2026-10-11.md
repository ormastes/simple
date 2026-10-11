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

## Open-tail slice attribution

The next bounded attempt used a fresh concrete diagnostic trace and an
explicit event-push result. The 66-module native fixture still refused cold
publication. GDB then identified the source-path loss: the cold parser's
`line[2:]` handed `compile_source_inventory_path_valid_v1` the 32-byte
`src/compiler/linker_lifecycle.sp`, while Git had listed the complete 33-byte
`.spl` path. The validator returned false, so event-push returned a valid
empty array and the batch had zero source events. The earlier explicit
event-push wrapper was removed because it added per-path work without
addressing this cause. The bridge now uses `substring(start)` at its four
open-tail text slices, and the path validator no longer allocates a split
array to reject `..` segments. These final source changes remain unexecuted
under the three-cycle cap. See
`doc/08_tracking/bug/native_text_open_tail_slice_truncates_final_byte_2026-10-11.md`.

## Membership publication and event payload follow-up

Three bounded no-stub Stage 2 native builds of the same 66-module fixture
linked successfully. With the open-tail `substring(start)` repair, execution
advanced to `untracked-membership-publish-failed`. GDB showed a valid encoded
membership record but a malformed digest path after `sha256_text`. The bridge
now hashes `value.bytes()` with `sha256_u8_hex`, preserving the encoded UTF-8
byte stream. The next executable had a valid 64-character digest path, but
`file_atomic_write` returned false, matching the separate native facade bug.

Membership records use immutable content-addressed paths. The bridge now
creates a missing record exclusively and verifies its readback before any
CURRENT pointer can name it. The third executable passed that publication
boundary and stopped at `observed-event-apply:event-entry-invalid`. GDB saw
the constructed event's `byte_count` as `-1`. The checked text read or its
optional default in the native event constructor is suspect, but the exact
ABI defect has not been isolated. See
`doc/08_tracking/bug/native_scv_event_content_length_invalid_2026-10-11.md`.

Build logs: `build/mini_builds/target6_tracked_move_refresh_probe/build_v4_substring.log`,
`build_v4_byte_hash.log`, and `build_v4_exclusive_membership.log`. Each linked;
each run exited 2 at the successive boundaries above. The three-cycle limit
is reached. There is still no cold or warm V4 admission PASS, current-source
worker, or matched time/RSS qualification.
