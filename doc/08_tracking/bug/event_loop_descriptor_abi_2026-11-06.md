# Event-loop descriptor ABI gap — OPEN

Native Linux epoll and macOS/FreeBSD kqueue poll return an i64 count and expose
FDs through process-global scratch getters. They discard direction, error/HUP
flags and tokens; syscall errors become count zero. Other hosts, IOCP and event
ports are unsupported. Native register/deregister return 1 success; close returns
0 success. The Simple facade now matches those scalar signatures and comparisons.

`PlatformEvent.poll_descriptors(handle,max,timeout_ms)` copies at most 256 FDs
under a process-wide canonical mutex, with a nonblocking lock attempt and bounded
0..25ms wait. Result status `observed` reports only a descriptor notification;
`no_observation` deliberately cannot distinguish idle, timeout or native error.
A sole reader registering only Read can attempt bounded incremental input work.
No caller may infer ReadWrite readiness or token identity. Direct foreign users
of the legacy native poll/getter ABI bypass this lock and must not run concurrently.
Legacy EventLoop.poll returns an explicit error; PlatformEvent's legacy poll now returns Result with an explicit error instead of
interpreting an integer as a heap array. Bounded production source inventory found
no direct PlatformEvent.poll consumers beyond EventLoop (now explicit Err);
native_driver imports completion-driver aliases only.

Full readiness/error qualification remains OPEN. A future native ABI must return
an owner-local immutable bounded snapshot including fd, actual OS flags, token,
count and syscall status, without process-global scratch, on each admitted host.
Search found no existing poll/select/kevent POSIX SFFI record provider. Terminal
poll/read-timeout declarations have no corresponding native C implementation in
the inspected runtime; they cannot justify a replacement transport.

Focused spec: test/01_unit/lib/nogc_async_mut/io/event_descriptor_abi_spec.spl.
Status: AUTHORED / NOT_RUN. Synthetic receipt tests establish classification only;
native ABI, contention, real readable pipe, errors and all hosts remain NOT_RUN.
No C/runtime provider changes were made.

Static evidence: pointer/reference map PASS (265 edges, no new findings), host
map PASS (868 edges, no new gaps; SimpleOS UNKNOWN). SFFI backlog failed its
inventory dependency (source_variants 402/399, migration 3761/3546), not a runtime
qualification. Logs: /tmp/check-rt-pointer-ref-map.py.event-descriptor.log,
/tmp/check-rt-host-map.py.event-descriptor.log,
/tmp/sffi-unsafe-backlog.shs.event-descriptor.log.

The C contract checker ignored `--help` and unexpectedly executed its full matrix
once: 510 PASS / 157 FAIL / 35 UNTESTED, link UNTESTED, Darwin arm64 clang17.
Its output was returned through the tool and truncated; no complete standalone
log was retained. It was not repeated. This broad matrix is not exact-scope or
runtime qualification and its failures are not classified as new regressions.

Gate failure: failed try-lock returns an error before any native poll, acquires
no ownership and leaves the caller's event handle untouched for retry/close.
After acquired lock, all validation outcomes go through checked unlock; immutable
FD snapshots escape only after successful unlock. A failed unlock fails closed.

Cycle 2 static review repaired the cross-module return-only generic try-lock
call using `mutex_try_lock_gate` in the existing canonical mutex owner, alongside
its scalar create/lock/unlock siblings. No new raw mutex owner or extern added.
Stale EventLoop.poll documentation now describes explicit failure.

Inventory attribution: source inspection identifies three newly divergent
signatures (rt_event_loop_register/deregister/close corrected to i64 here but
legacy driver.spl and sffi/host.spl still declare bool) and one removed divergence
(rt_event_loop_poll array corrected to i64). Those are attributable to this repair;
the complete 402 versus399 and migration3761 versus3546 totals cannot be partitioned
from the captured aggregate alone, especially with concurrent source work. No
claim is made that all inventory failure predates this patch. The legacy driver
also calls raw native poll outside the canonical gate; concurrent use is excluded
until its call path is migrated. Full native readiness/error ABI remains OPEN.

Cycle 2 integration follow-up resolves the attributable divergences: canonical
`io/driver.spl` and `sffi/host.spl` now declare register/deregister/close with the
same scalar native ABI and explicit success comparisons. Driver polling routes
through PlatformEvent.poll_descriptors and returns failure on rejected observation;
it no longer accesses process-global scratch independently. Unused host split
poll/getter wrappers now return explicit Result errors, with their raw declarations
removed. In-tree native poll/scratch access is therefore confined to the snapshot
owner; direct external C/native users still cannot participate in its mutex.
Full inventory totals were not rerun or inferred from these scoped fixes.

The existing driver's completion interpretation is not qualified by this ABI
repair: descriptors still do not identify read versus write when both interests
are registered. Native error/flag support remains necessary for the full legacy
multi-interest event contract. No new native direction claim is made.

Cycle 3 containment: descriptor-only notification cannot authorize blocking
TCP read/send or UDP recvfrom. IoDriver.poll_count now rejects any pending
network operation with ERR_UNSUPPORTED (-38) before accept fast path, native
polling, callbacks, or data I/O. The array poll API explicitly fails on this
negative admission result. Pending operations remain reachable for cancellation.
The separate LSP single Read fd descriptor path remains available.

Exact unresolved regression: a socket registered ReadWrite is writable while its
peer sends no bytes; queue receive and send, then poll. Previously the FD-only
notification allowed blocking read (or, with O_NONBLOCK, EAGAIN became nil and
permanently failed receive). Required oracle: no read/send/recvfrom before
capability admission, unsupported result within budget, retained cancellable queue.
Authored adjacent queue rejection control uses a borrowed descriptor and performs
no data I/O. Real socketpair writable-only/EAGAIN native regression is NOT_RUN,
not simulated as a pass. Full driver direction/nonblocking/error ABI remains OPEN.
