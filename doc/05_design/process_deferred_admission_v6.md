# Deferred admitted process launch V6

Status: implemented source checkpoint under review; all V6 tests NOT_RUN.

The existing ProcessObservationReservationV4 remains the sole mutable child owner. V6 adds Linux-only scalar launch progression without changing V4 observation bytes, static sealed-image pinning, V5 submission expiry, or synchronous entry points. It does not transfer a mutable Container or introduce a supervisor, worker pool, journal, or queued-success receipt.

## Public contract

`start_deferred_admitted_v6(request, expires_at_unix_ms)` consumes one reserved attempt and returns `Result<ProcessLaunchProgressV6,text>`. `poll_launch_v6(retire=false)` advances that same reservation. Progress is exactly NoChild=0, LaunchPending=1, ObservationAvailable=2. Unknown scalar values are errors. NoChild is available only from an attempted V6 reservation with actual no-child state3, never from an unused reservation or a legacy attempt. Negative native errors preserve the original reservation and pins.

Native leaves are `rt_process_observation_v6_reserved_start_deferred_admitted_value(token, executable, cwd, binding, expiry)` and `rt_process_observation_v6_reserved_poll_launch_value(token, retire)`. Non-Linux ports return unsupported before child effects. The exact two OS leaves use the existing reviewed C-only ownership policy; no ratchet baseline or extraction exemption changes.

## Ownership and transitions

The existing short reservation registry gate locates the token and checks busy state and submitting Linux TID plus immutable per-thread stamp. This precedes per-child owner locks and ptrace progression. V6 is parent-coordinator-only. Activated V6/reservation/ticket follow-up admission refuses a foreign fork process before owner gates; this is not general fork safety for every raw-owned API or a hard wait-free registry design. Every later API on that V6 reservation retains the TID restriction, including ordinary observation/acknowledgment and cleanup.

After fork, the same RtOwnedSlot retains the error pipe, trace phase, actual child identity, failure class, deadline and partial error bytes. Reservation state6 refuses legacy observe, ack and confirm-release. Post-fork clock/setpgid/pidfd/identity setup failure also enters this owner path rather than synchronous cleanup. A failed pidfd acquisition can leave cleanup uncertain: V6 never falls back to bare-PID signaling.

Each pending poll advances at most one waitpid(WNOHANG), ptrace, error-pipe read or exact pidfd signal step, with clock observations. It never runs the older exec confirmation/deadline/reconcile loops. The actual PTRACE_EVENT_EXEC is observed before sampling its proof timestamp. Detach must succeed before ordinary Running observation is exposed. CLOEXEC error-pipe EOF alone is not exec proof.

Cancel and timeout request termination but retain state6 through actual terminal wait/reap and complete error-pipe interpretation. A signal request is not reap or tree proof. Fatal ptrace progression, ECHILD, partial-report EOF and uncertain IO remain retained errors. EINTR and EAGAIN preserve the exact phase and descriptor. The exec descriptor closes once after resolved detach or error interpretation; no close retry can target a reused descriptor. ObservationAvailable hands control to the unchanged V4 durable-observe-before-ack lifecycle; retire on an already materialized launch does not replace normal V4 cancellation.

## Limits and scheduling integration

This checkpoint removes synchronous exec-confirmation waiting, not all latency. Request encoding, validation, executable hashing/pinning, fork/setup, existing native registry locks, normal V4 observe/group reconciliation and provider WAL/CLI preparation retain their existing behavior. Ordinary observation can still scan or reconcile with existing loops. Linux enforcement remains LeaderOnly with None/RLIMIT_AS policy; no CPU or descendant enforcement is claimed. Dynamic Podman requires a separate explicitly trusted original-FD image policy: the current static sealed pin still rejects dynamic ELF.

Persistent HostServiceDomain scheduling, immutable provider tickets/revision commit, reserved health/cancel capacity and bootstrap-qualified dynamic pins remain dependent work. Health handling must use cached owner/domain state, never synchronous provider probe/execute/wait. No full daemon responsiveness or perf PASS is claimed.

## Verification source

`test/01_unit/lib/io/process_deferred_launch_v6_spec.spl` covers strict progress decoding. `src/runtime/test/runtime_process_deferred_admission_v6_selfcheck.c` uses the production owner and normal CoreC array/pin providers, a real static helper, actual ptrace stop/exec/cancel/expiry/timeout and wrong-thread refusal. It must include runtime_process_owned.c exactly once and link runtime_process.c for actual sealed executable pins; fake pin/array providers are forbidden. The test harness alone uses finite sleeps/deadlines and terminates on failure.

The native fixture also links test-only wrappers for setpgid/read/rt_array_new: one real parent setup syscall failure leaves state6 and the actual error FD retained; unavailable observation allocation preserves reservation authority; the actual child errno report is consumed one byte at a time with one injected EAGAIN. These wrappers never fabricate child identity, exec success or reap facts. The setup-failure test harness alone kills/reaps its known actual child after proving production refusal; it does not mint a V6 receipt/release. Tests also assert poll_launch(retire=true) after materialization remains observational and normal V4 cancellation is still required.

No test has run. Fatal ptrace and lost-child/partial-EOF uncertainty need further negative qualification. The authored wrappers are not proof of kernel resource exhaustion or all allocator failures. No native producer/build has been allocated for this checkpoint.

The positive native exec case observes without retirement and requires frozen exit0 plus exact stdout `exec-v6\n` before acknowledgment. The pending-timeout case uses a one-second workload budget and a real 1.1-second stopped delay, avoiding preparation-dependent expiry. The final uncertain setup-failure reservation retains its original executable/directory pins through isolated fixture process exit; the harness reaps only its actual known child, and process exit reclaims the retained test capabilities.

## Cycle 2 origin and thread-incarnation repair

Before new V6 admission touches any owner gate, it invokes canonical `simple_local_unix_origin_v1`. Successful admission publishes a nonclearable lock-free process-private V6-active latch before any V6 reservation mutation. Once active, existing reserve/reservation acquisition and public V4 ticket follow-ups check that same origin before inherited mutexes, ticket decoding or result allocation. Foreign calls return scalar error or NULL with authority retained. A legacy-only process with the latch unset retains existing behavior. No new origin registry is introduced.

A lock-free checked monotonic unsigned sequence issues a process-private TLS stamp only after origin admission. Zero is unissued, exhaustion fails closed and stamps never reset/reuse. A V6 reservation binds both actual Linux TID and that stamp. Thus a later thread with a reused integer TID cannot inherit admission. Existing short registry lookup remains necessary; no parallel lock-free owner registry exists.

The public V4 ticket selector already excludes `reservation_token` slots, and V6 never exposes its private core token. Raw-owned adapters are unchanged; the checkpoint does not claim arbitrary private-core-token forgery, inherited raw-owned APIs, native fork during an operation or all runtime allocator fork safety. Internal unlock remains unconditional.

The focused native fixture now forks while actual reservation, V4 slot, raw-owner and child locks are held. Its child calls both new ports, every reservation route and all four public ticket follow-ups, with unreadable ticket addresses and an armed allocator-failure sentinel; prompt error/NULL must precede both decoding and allocation. Parent then progresses its actual child normally. A separate actual-thread stamp test substitutes only a foreign issued stamp to exercise refusal despite matching actual TID; it does not claim forced kernel TID recycling. Both additions remain NOT_RUN; no new native build is allocated.

The four public V4 ticket externs now declare nullable tuple results. All five actual lease call sites (poll, cancel, collect, acknowledge and acknowledge_cleanup) match absence before tuple destructuring/decoding and return an error without changing lease authority. Foreign native refusal allocates no diagnostic tuple. TLS stamp issuance is bounded to 16 CAS attempts; exhaustion returns EOVERFLOW and contention returns EBUSY without reusing a stamp. This source contract remains NOT_RUN.
