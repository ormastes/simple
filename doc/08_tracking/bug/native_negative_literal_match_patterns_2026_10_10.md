# Negative signed literal patterns collapse into wildcard arms

Status: OPEN; tagged source workaround, underlying compiler repair pending.

Producer aff317, source d7df6a50, normal AOT row13 rejects src/app/cli/native_build_exit_status.spl with MIR B5b: match has multiple wildcard arms. The source has seven distinct negative i64 literal patterns and exactly one wildcard. Receipt: /dev/shm/simple-phase3-aff317-normal-objects-20261010/epoch01/row-0013/evidence.json.

The workaround preserves the seven signed comparisons and labels in order using if/elif, returns empty text for every other value, and leaves the POSIX signal function unchanged. This does not claim parser or MIR correctness. Native prevention fixture covers all seven labels, unknown negative/zero values and POSIX boundaries -256/-255/-129/-128. Fixture runtime UNEXECUTED until a receipt is attached.
