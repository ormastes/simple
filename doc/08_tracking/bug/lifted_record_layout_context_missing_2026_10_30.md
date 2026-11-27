# Lifted bodies lose admitted record layout snapshots

Status: source repair prepared; focused compile/runtime verification pending.

The attempt14 replay subset failed MIR lowering with `array return record
element has no unique provider layout: lib.nogc_sync_mut.replay.event_kinds::ReplayEntry`.
The real log is `/tmp/sspec-subset14-replay-out/cache/native/diagnostics/native-build-stderr-1311251-2.log`.
That run also has unresolved `to_equal` and failed lambda-materialization
diagnostics. Its 82-module closure included `src/os`; it produced no artifact.
Those other failures must not be counted as resolved by this repair.

The lifted lowering inherits field maps and a snapshot of the provider leaves
already materialized. However, it inherited `composite_layout_digests` and
`composite_layout_owner_counts` only with a declaration repository, and never
inherited `result_err_layout_types`. Array record validation requires all three.
The inherited materialized set prevents lazy provider registration from
rebuilding already admitted rows. The trait-context repair in attempt15 does
not change these layout carriers.

Carry the three admitted snapshots into every lift. Preserve exact owner keys,
conflict counts and empty semantic-type conflict markers; do not weaken the
layout checks or infer a provider from a bare type name. Local state and builder
state remain fresh. Existing parent provider re-demand remains in place.

`test/fixtures/compiler/native_array_return_record_owner/plain.spl` provides
an ordinary-call control. Its sibling `lifted.spl` exercises the same imported
record with direct, nested and sibling closures and a conflicting consumer type
name, without SSpec or matcher dependencies. Successful native execution must
return zero and print its exact PASS marker; source inspection is not that proof.

The focused MIR spec parses and lowers real provider and consumer sources,
counts emitted provider calls, and requires rejection when the admitted
physical-layout or semantic-type snapshot is conflicting. It remains pending
the build owner's capacity and an admitted producer containing this repair.
