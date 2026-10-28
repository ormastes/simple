# Fiber scheduler

Admission accounting lives in `src/lib/common/task_runner/fiber_scheduler.spl`;
FileFiber host integration lives in `src/compiler/80.driver/driver_build/file_fiber_v1.spl`.
Compare estimates against remaining budget, and check forced admission against
the i64 limit before adding. On overflow preserve pending work and reservations,
latch the scheduler error, and allow admitted work to drain. The carrier must
count IO, parse requests, pending/ready async results, and queued fills before
deciding that forced admission or terminal cleanup is safe.

Focused Phase 1 execution: scheduler 14/14, FileFiber 12/12. This is not native
qualification. Existing failed read/close submission descriptor leaks remain
separate. Evidence: `doc/08_tracking/bug/fiber_scheduler_reservation_overflow_2026_10_28.md`.
