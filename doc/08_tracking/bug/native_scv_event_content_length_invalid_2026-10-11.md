# Native SCV event content length is invalid

Status: OPEN compiler/runtime boundary defect.

The 66-module no-stub Stage 2 tracked-move executable reaches observed-event
application after Git listing and membership publication. It rejects the
first cold event with `observed-event-apply:event-entry-invalid`. GDB at
`compile_source_inventory_apply_event_v1` shows the constructed event's
`byte_count` is `-1`; a valid event requires a nonnegative content length.
The event constructor in `src/app/compiler_entrypoint/inventory_scratch.spl`
passes `file_read_text_at_checked(absolute, 0, 1073741824) ?? ""` into
`compile_source_inventory_git_event_v1`. This checked read, its optional
default, or the resulting text handoff is suspect. The precise failing edge
has not been isolated, so no replacement read path is yet justified.

Reproduce with the existing
`build/mini_builds/target6_tracked_move_refresh_probe/probe_v4_exclusive_membership`
artifact. The build log is `build_v4_exclusive_membership.log` in the same
directory. Next: make a small ABI probe that reads a known source through the
checked facade and asserts text content and length, then inspect the event
constructor in the same native call graph. Repair the failing edge through
the app/SOSIX facade boundary and rerun the complete V4 fixture in a fresh
bounded cycle. Do not claim warm deletion or Item 6 cutover from this failure.
