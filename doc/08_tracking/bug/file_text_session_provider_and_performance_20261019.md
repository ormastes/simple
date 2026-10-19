# OPEN: file text provider and performance qualification

Status: OPEN. Source-observed costs; runtime measurements and qualification UNRUN.

Strict io_runtime.file_read_nullable replaces a direct provider call with checked configuration, descriptor accumulation, validation/copies and Text materialization. Compiler/cache callers now encounter a 16 MiB logical default and additional allocations. FileHandle.read_line uses one managed one-byte read per input byte to preserve the following raw cursor. This is bounded but can be expensive for long lines.

Required evidence: exact admitted pure provider/link identity, class alias-close/native dispatch, realistic cold/warm compiler-read workloads, short/long-line latency and syscall counts, throughput, max RSS including overlapping growth/copies, and descriptor/allocation cleanup under injected read/write/seek/close/OOM failures. Final bytes_to_text allocation and generated packed-byte tagging remain inherited open boundaries. No timings, allocation-free behavior, or total resident bound is claimed.

A future buffered-line optimization needs explicit owner buffer/raw-read/seek design; an unbounded raw-text shortcut would bypass strict semantics. External positional helpers have 1 MiB foreign windows but no total-heap bound; session callers enforce logical budgets.

Current MIR marks classes as references, but actual alias/close/private enforcement remains unexecuted. @unsafe annotations do not prove affinity or thread isolation. Manual close is required and concurrent session access is unsupported.

The source packet launches no compiler/build/test attempt and changes no budget. Root owns the user-authorized six-attempt campaign with three original failures counted. All newly authored cases remain UNRUN.

Current source checks copied/appended lengths in positional and session accumulators. A silent array-growth failure must return a typed error and close the owner instead of retrying the same pread offset forever or accepting a shortened payload. This closes a source-visible failure path; allocator-injected execution and all broader OOM guarantees remain OPEN.
