# BUG-RT-BLACK-BOX-SHARED-SINK-001: shared C black-box sink races

Severity: P1. Status: source correction authored; native regression NOT_RUN.

The MSVC and generic fallback branches of `rt_black_box` in
`src/runtime/runtime_native.c` each declared one file-scope
`static volatile int64_t rt_black_box_sink`. Concurrent calls wrote that same
object and then read it back. For example, caller A could store zero, caller B
could store one, and caller A could return one. Unsynchronized non-atomic access
also makes the concurrent C execution a data race; `volatile` does not establish
inter-thread synchronization.

The primitive promises identity. Its comparison callers may interpret zero and
nonzero as different authentication outcomes, so cross-call contamination is a
correctness and security defect. This report does not claim an observed exploit
or reproduce it with executed native evidence.

Both affected branches now use invocation-local storage:
`volatile int64_t sink = value; return sink;`. Each invocation owns its object.
The GNU/Clang inline assembly, function signature, symbol binding and runtime
exports remain unchanged. No locking or runtime framework is introduced.

The new direct-primitive spec is
`test/01_unit/lib/crypto/rt_black_box_concurrent_identity_spec.spl`. It checks
present identity for zero, positive, negative, wide values and both signed i64
extremes. Two real OS workers rendezvous before repeatedly calling the primitive
with different input phases; their actual native thread identities must differ
from each other and the test thread. Worker results are joined and atomic
handles retired before assertions. Nil cannot be hidden by an identity fallback.

The concurrent scenario is bounded stress coverage. The old race is scheduling
dependent, so an old binary may pass a run. An actual data-race detector and
qualified MSVC/generic C-provider runs remain missing evidence. A Rust strong
override, interpreter dispatch or GNU asm-only run cannot qualify these changes.
No native/compiler/seed/build/test execution is authorized in this correction
campaign. Source correction cycle: 1 for this newly identified defect; existing
authentication and native campaign budgets are unchanged. No optimizer-opacity,
constant-time, or full authentication qualification is claimed.
