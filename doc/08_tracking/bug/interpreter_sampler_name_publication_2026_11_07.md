# Interpreter sampler name publication and timer retirement

Owner: interpreter sampler maintenance. Source repair prepared; focused owner checks passed, full integration verification waiting.

PR #7500 head `95156319e2a68c8c6832ecda2551e994281e0717` enables a non-Unix sampling thread. The sampler originally published names as independent pointer and length atomics in stack slots and the current-expression marker. A writer changing a long name to a short name could be sampled between those stores. The resulting histogram entry reached `slot_name` and `from_raw_parts` with an out-of-allocation length. Interning/leaking the text protects its lifetime, not a mismatched length. This native Rust sampler is the owner of the concurrency defect; a pure-Simple caller cannot repair its atomic publication protocol.

## Reproduction

A bounded offline Rust harness compiles the exact original sampler module from the above commit. A test forces the actual `KindGuard::enter` preemption point by publishing the new pointer before its length, then invokes production `take_sample`. It checks the recorded histogram metadata without calling the unsafe renderer. The test fails with recorded length **35**, expected **1**, exit 101, one failed test. It does not perform an out-of-bounds read. Receipt: `/private/tmp/release100-sampler-unit-20261107/baseline-repro.log`; retained original module plus test: `baseline/sampler.rs` in that directory. One Cargo build job was used while the separate compiler producer remained active.

## Repair and adjacent controls

All stack, kind, and histogram publications now carry one pointer to immutable interned `SampleName` metadata. An old or new identity always includes its own text/length. Readers allocate and lock nothing during a sample. Per-thread kind-name caches avoid a global intern lock on each profiled expression. The existing interned-name lifetime is retained; this repair does not claim to bound the number of distinct names in a long-lived profiling session.

Single-owner initialization publishes the timer handle before reporting the sampler ON. The non-Unix timer uses a retained handle and interruptible parking; shutdown sets the stop flag, unparks, checks the flag after waking, and joins before rendering. This replaces the prior unjoined sleeping thread.

The actual repaired module was compiled through an isolated `#[path]` Cargo harness with only cached libc, `--offline --jobs 2`; five tests passed (6.33 s build, 0.49 s tests). Controls cover retained identity across a shorter publication, concurrent frame-slot reuse with both rows exercised, existing frame attribution, and waking/joining a long-interval timer. The module hash for that result is SHA256 `76295b4209debe943451115b333bf0a4093622425daa4abf344c524c4a9fec29`. Receipt: `/private/tmp/release100-sampler-unit-20261107/fixed-tests.log`.

These are real Rust owner tests, not a full compiler build or a replacement product interpreter. Full compiler integration, native Windows startup/exit, performance, and Simple runtime/SPipe qualification remain NOT_RUN. Resume with the admitted integration environment and at most two concurrent build jobs. PR #7500's separate RSS-gate failure and lexer byte-unit findings must also be resolved before the whole PR can land.
