# Native open-tail text slice truncates the final byte

Status: OPEN. Found in the admitted pure-Simple Stage 2 native compiler while diagnosing Item 6 V4 inventory refresh; current-source compiler behavior is unverified.

In the 66-module tracked-move fixture, Git reports the full tracked path `src/compiler/linker_lifecycle.spl` (33 bytes). The cold parser takes `line[2:]` from the `H ` listing row. GDB at `compile_source_inventory_path_valid_v1` showed the received text had length 32 and value `src/compiler/linker_lifecycle.sp`. The validator correctly rejected that non-source suffix. The event-push function returned a valid empty array, the batch remained valid, and the owner refused cold publication with `cold-init-listed-no-sources`. The runtime also emitted an invalid-array-handle diagnostic during this path.

The focused native process-output probe passes the exact Git `ls-files` request and splitting its stdout, so the source row is present before the parser's tail slice. The candidate bridge uses `substring(start)` for its four open-tail text slices; this was not rebuilt after the three-cycle cap. A compiler fix and native/interpreter regression must prove `text[start:]` preserves the entire suffix, including the final byte. Then run the full tracked-move fixture through cold, staged, committed, and unchanged warm admissions.

Evidence binary: `build/mini_builds/target6_tracked_move_refresh_probe/probe_v4_path_valid` in the isolated worktree. GDB observed `rt_string_len(path)=32`, printed `src/compiler/linker_lifecycle.sp`, and saw the path validator return false. The source-only bridge workaround is not a runtime PASS.
