<!-- codex-research -->

# Domain Research — Simple Ring and Async Base

Date: 2026-08-26
Parent synthesis: `doc/01_research/runtime/simple_ring_first_async_first_architecture_2026-08-26.md`

## Verified precedents

### Queue-oriented I/O and protected data planes

- Linux queue interfaces demonstrate the value of registered entries, per-core queues, and explicit submission/completion ownership. The exact native ABI remains provider-private; Simple should preserve those queue semantics without encoding Linux descriptors in the common contract. See the [Linux kernel FUSE-over-io_uring design](https://kernel.org/doc/html/latest/filesystems/fuse/fuse-io-uring.html).
- Arrakis separates a protected OS control plane from application-owned virtualized-device data paths. That supports the selected split: SOSIX owns capability, setup, lifecycle, and isolation policy while steady-state typed rings carry operations and completions. See the [USENIX Arrakis overview](https://www.usenix.org/publications/login/august-2013-volume-38-number-4/arrakis-operating-system-control-plane) and [OSDI paper](https://www.usenix.org/sites/default/files/osdi14_full_proceedings.pdf).
- Demikernel provides a uniform asynchronous LibOS/datapath API over heterogeneous kernel-bypass and compatibility backends. This supports explicit `direct`, `translated`, `software`, and `emulated` provider grades rather than separate public APIs. See the [Demikernel SOSP paper](https://doi.org/10.1145/3477132.3483569) and [project repository](https://github.com/microsoft/demikernel).

### Polling, typed state machines, and exact wakeup

- Rust defines Future progress as a nonblocking `poll` with a task `Context`; pending work registers the current Waker and is polled again only after wakeup. Simple should preserve the nonblocking/exact-wake invariant while carrying an explicit wait token in `Pending`. See the [Rust Future reference](https://doc.rust-lang.org/core/future/trait.Future.html) and [async trait explanation](https://doc.rust-lang.org/book/ch17-05-traits-for-async.html).
- Rust lowers async source to compiler-managed state machines holding state across await points. That supports typed `AsyncTaskFrame` values containing only live-across-suspension data rather than generic byte arrays. See [Futures and async syntax](https://doc.rust-lang.org/book/ch17-01-futures-and-syntax.html) and the [Rust await-expression lowering](https://doc.rust-lang.org/nightly/reference/expressions/await-expr.html).
- Embassy demonstrates no-heap embedded execution with statically allocated exact-size task storage, targeted polling of only the woken task, and CPU sleep instead of busy scanning. This directly informs `mission_pool`, compiler-known frame bounds, exact wake keys, and idle sleep. See the [Embassy executor documentation](https://docs.embassy.dev/struct.Forever.html).

### Structured and mission concurrency

- Swift task groups make parent/child lifetime explicit, propagate cancellation, and prevent parents from forgetting child completion. Simple should make structured task ownership the default and require an explicit supervisor capability for detached services. See the [Swift concurrency guide](https://docs.swift.org/swift-book/LanguageGuide/Concurrency.html).
- High-assurance concurrency patterns such as Ravenscar motivate fixed task sets, bounded queues, deterministic scheduling, and constrained dynamic behavior. Simple’s mission profiles should apply those restrictions to async rather than prohibit async itself.

## Synthesis for Simple

The common denominator is not one native descriptor. It is a typed lifecycle:

```text
bounded reserve -> explicit commit -> provider progress
-> one terminal completion -> exact task wake -> nonblocking poll
```

Native queues remain intact behind providers where their security and ownership model permits. Compatibility providers are honest about translation, blocking pools, and fallback. Compiler-generated task frames and structured ownership sit above the provider boundary. Mission profiles add admission proofs, static/fixed storage, deterministic scheduling, and fail-closed fallback without creating a separate async language.

## Risks confirmed by the literature

- Kernel bypass without a protected control plane expands the trusted computing base.
- A uniform API can hide materially different fallback costs unless provider grade and reason are explicit.
- Polling becomes busy waiting if wake registration and exact ready selection are missing.
- Static capacity claims are false if backing storage grows dynamically or task frames have unknown size.
- Mechanical conversion to async is not automatically faster; every migration needs comparable latency, throughput, allocation, and RSS evidence.

These risks are therefore requirements, not implementation notes: capability enforcement, provider honesty, exact wakeup, fixed bounds, and benchmark-gated migration are mandatory parts of the V1 design.
