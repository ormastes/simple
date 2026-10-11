# Negative signed literal patterns collapse into wildcard arms

Status: OPEN; tagged source workaround, underlying compiler repair pending.

Producer aff317, source d7df6a50, normal AOT row13 rejects src/app/cli/native_build_exit_status.spl with MIR B5b: match has multiple wildcard arms. The source has seven distinct negative i64 literal patterns and exactly one wildcard. Receipt: /dev/shm/simple-phase3-aff317-normal-objects-20261010/epoch01/row-0013/evidence.json.

The workaround preserves the seven signed comparisons and labels in order using if/elif, returns empty text for every other value, and leaves the POSIX signal function unchanged. This does not claim parser or MIR correctness. Native prevention fixture covers all seven labels, unknown negative/zero values and POSIX boundaries -256/-255/-129/-128. Fixture runtime UNEXECUTED until a receipt is attached.

Post-restart qualification (2026-10-10): the earlier tmpfs failure receipt is unavailable after WSL restart; its diagnostic remains recorded in the durable original aff317 ledger. The changed source now passes normal AOT with producer aff317: exit 0, object 2112 bytes, both expected functions defined. Durable receipt: `/mnt/c/Temp/simple-native-status-retry-20261011/evidence.json`.

The prevention fixture now executes successfully after linking with the exact Hello entry object and the durable runtime archive (all 40 member hashes match the Hello runtime receipt). Complete stdout is checked against all seven labels, unknown negative/zero/positive values, POSIX boundaries, and the Windows NTSTATUS non-POSIX control. Receipt: `/mnt/c/Temp/simple-native-status-retry-20261011/fixture/evidence.json`, status PASS_EXECUTION. This qualifies the workaround, not the underlying negative literal match lowering.
