# SimpleOS heap payload clearing and deferred guest verification

The reclaimed-heap follow-ups indexed free holes and bounded metadata work,
but cleared whole allocations while holding the global allocator lock with
local interrupts masked. A large allocation therefore delayed device service
in proportion to payload size. Allocation now reserves metadata under the
lock, restores the incoming interrupt state and clears the exclusively owned
payload before returning it. Both in-place realloc growth paths follow the
same rule. Moving realloc copies the old payload and clears only the extension
outside the lock. `calloc` uses the already-zeroing allocator once.

The host regression compiles the extracted production allocator at `-O2
-ffreestanding`, with allocator symbol names isolated from host libc. A
test-only thread-local ownership probe observes every production payload clear;
it requires zero calls while the calling thread owns the allocator lock.
It covers 100 MiB allocation, 10 MiB in-place growth, free-neighbor growth,
moving realloc, realloc from null, recycled contents, overflow and concurrent
allocation. Metadata is reserved before publication, so another allocator
cannot reclaim a payload while its owner clears it.

2026-09-23 focused host result: PASS, 1.02 seconds, 138,540 KiB peak RSS;
72,342 clear calls, zero lock-owned calls, largest clear 104,857,600 bytes.
The 20,000-operation small-allocation probes measured 497 CPU ticks with 8 live
blocks, 500 with 4,096 live blocks and 489 with the fragmented fixture. The
oracle is the lock-ownership invariant; host scheduling noise is not used to
infer guest interrupt latency. A mutation that reacquires the heap lock around
malloc payload clearing exits 35, proving the new regression rejects that bug.

The first resource-capped compile could not link because the host-default mold
requested an 8 GiB virtual reservation. The bounded rerun used `-fuse-ld=bfd`
under a 512 MiB virtual-memory limit; no full compiler or QEMU build ran.

Astra source review accepts the exclusive-owner clearing sequence and constant
test-only instrumentation; production has no new retained payload/copy. The
existing free-list search remains proportional to the number of free holes,
so the change makes no constant-time allocation claim for arbitrary workloads.

TODO (SimpleOS QEMU owner, after Linux bootstrap and admitted target compiler):
run `test/01_unit/os/port/host_bug_a09_bump_heap_churn_spec.spl`, rebuild the x86_64
SimpleOS image and repeat interactive allocation/resize/free churn in QEMU.
Retain input/device responsiveness, interrupt-latency and heap high-water
measurements, serial fault output, compiler hash and elapsed/RSS evidence.
Verify the full runtime header layouts and reference-count ownership against
the reclaimed allocator. Keep the original memory bug OPEN pending guest proof.
