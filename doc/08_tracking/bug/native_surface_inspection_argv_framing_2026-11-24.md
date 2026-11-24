# Inspection executable counted as a second entry

Actual read-only consumer run `45221270769`, artifact `14843081007`, executed
verified Phase 1 producer source `1d0351ba1a89517d6d9e8c0015b0344dda125659`.
Both default-empty and explicit-Linux queries exited 1 before creating any
private diagnostic directory. Retained argv has exactly one `--entry`; both
reported `multiple native-build entry points; specify one positional entry or
--entry`. Evidence is under
`build/verify/readonly-surface-consumer-45221270769`.

The inspection adapter constructed `[argv[0], "native-build", ...options]`.
`cli_native_build_option_error` consumes option tokens, skips a literal
`native-build`, and counts every other nonflag token as a positional entry.
Thus the executable path was entry one and the actual `--entry` was entry two.
The ordinary bootstrap route already strips both executable and command via
`bootstrap_native_build_worker_args`.

The repair passes only options to the existing native owners. The entry-count
validator remains unchanged. The focused regression uses the real three-root,
dynload, low-memory, threads/cache argv shape and separately rejects duplicate
`--entry` and a second positional entry. It is authored but not executed by an
admitted compiler in this repair session.

This fixes diagnostic request framing only. No configured surfaces were
captured in the failed run, so it supplies no SDK resolver or target-cfg cause.
No new producer/native job was started; final native cycle 6 remains reserved.
