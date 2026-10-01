# Bootstrap distributed builder detail design

Status: shared protocol implemented; native qualification pending.

## Shared interface

`std.common.build_manager.contracts` exports `BuildInputV1`, `BuildTaskV1`,
`BuildHostV1`, `BuildResultV1`, `BuildRunV1`. Schema fields are defined once in
that source. Validators return an empty error string on success:
`builder_validate_task_v1`, `builder_validate_host_v1`,
`builder_validate_run_v1`, `builder_validate_result_shape_v1`, and
`builder_validate_result_v1(task, result)`.

`builder_task_identity_v1` hashes unambiguous length-delimited scalar fields,
counts and ordered lists, including task attempt, all three input identities,
program/argv, cache key and timeout. Invalid tasks have no identity. Full-run
journal identity is SHA256 of `builder_encode_run_v1`, binding host configuration
and scheduling policy as well as tasks.

`std.common.build_manager.codec` provides matching
`builder_encode_{task,run,result}_v1` and
`builder_decode_{task,run,result}_v1`. Encoders reject invalid input with empty
payload; decoders return `Result<T,text>`. App adapter provides matching
`builder_read_*_v1` and `builder_write_*_v1` through bounded no-follow reads and
atomic file-write facades. Parent directories must already exist.

## Wire format

The first newline-terminated scalar is `SIMPLE-BUILD-TASK-1`,
`SIMPLE-BUILD-RUN-2` or `SIMPLE-BUILD-RESULT-1`. Ordered scalar fields follow;
arrays have an explicit canonical decimal count. Percent, tab, CR and LF encode
as `%25`, `%09`, `%0D`, `%0A`. Decode once. Unknown escapes, leading-zero
integers, negative zero, trailing fields, absent final newline, excess bounds
and truncated records reject. Arguments stay opaque data, never executable
shell fragments. Codec and identity framing are separate deliberate formats.

Task body order: id, attempt, phase, producer/source/toolchain digests, program,
cache key, timeout, dependency count and IDs, argc and arguments, input count
and path/digest pairs, output count and paths. Run prefix: keep-going 0/1,
max-attempts, host count, each host's id/transport/endpoint/workspace/worker-program/
worker-digest/slots, then task count and task bodies. Result: task id, attempt, identity,
host id, status, exit, cache hits/misses/stores, output count and path/digest pairs.

Task/input/output paths are portable relative paths; traversal, absolute paths,
Windows device aliases and overlapping writable declarations reject. Text can
contain Unicode; field lengths follow the language text length semantics. File
payload admission is separately bounded in bytes by the app reader. SHA256
identities are 64 lowercase hex characters.

Run wire version 2 requires `BuildHostV1.worker_digest`, the SHA256 of that
host's compiled worker executable. Empty/malformed digests reject at admission;
transport must compare actual executable bytes before executing. Task producer
identity and worker identity are separate. Every host constructor must supply
the worker digest; the stable source API names ending in `_v1` do not imply
acceptance of the obsolete run wire format. Run version 1 is deliberately
rejected, never silently upgraded or filled from the local manager image.

The current user ordering uses the permitted genuine Phase 1 seed to build
the native manager, then retains that qualified manager through Phase 4.
Scripts continue the cached bootstrap concurrently. Grouped isolated local
workers are the immediate priority; remote execution remains separately
tracked and may not be claimed from local protocol tests.

Terminal result statuses are `OK`, `ERROR`, `CRASHED`, `TIMEOUT`, `BLOCKED`,
`NOT_RUN`. OK requires exit zero and exactly all declared outputs. Other statuses
have nonzero exit and cannot carry admitted outputs. Actual file verification
belongs to parent orchestration, not this pure shape validator. Cache counters
allow `-1` for unobserved compiler telemetry; counts of stored files are not hits.

## Validation and tests

`test/01_unit/app/bootstrap_builder/contracts_codec_spec.spl` checks opaque argv,
literal percent escaping, invalid/truncated records, integer overflow, portable
paths, overlap, missing/cyclic dependencies, changed attempts, output completeness,
and unknown telemetry. It supplies protocol evidence only after execution.

Scenario helpers for lifecycle suites: `prepare_builder_fixture`,
`start_builder_run`, `interrupt_owned_worker`, `resume_builder_run`,
`assert_terminal_task_rows`, `assert_dependency_blocked`, `assert_cache_reused`,
`assert_stale_result_rejected`, `assert_remote_execution_receipt`.
Unimplemented helpers must fail explicitly; none may supply placeholder passes.
Native local/remote process checks and compiler integration belong to their
corresponding implementation lanes, with retained evidence and separate status.
