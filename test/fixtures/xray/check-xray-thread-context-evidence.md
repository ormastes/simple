# XRay thread-context fixture evidence

Date: 2026-11-14

## Scope

This fixture compiles and runs the production thread-context and resident
admission headers. It checks selected pin and TLS-slot behavior, including two
pthread attachments, distinct arenas, same-pool idempotence, cross-pool
rejection, no-reuse exhaustion, malformed extent/schema rejection, bounded
unattached-loss accounting, and close/drain behavior.

`runtime_thread.c` now contains opt-in hook source and scheduler task-root
refresh calls at direct/isolated entry and the native runtime-thread pool's
outer task dispatch. Synchronous fallback work keeps the caller's existing
session attachment; it does not migrate from inside a user frame. This fixture
does not compile that object or verify hook/link activation. The alternate
`runtime_pool.c` owner is not covered. The fixture also does not verify event
production or retention, a concurrent close/acquire race, Windows behavior,
automatic attachment of foreign threads, forced termination, or asynchronous
cancellation cleanup.

## Source provenance

`src/runtime/xray/xray_resident_admission_v1.h` is byte-identical to provider
commit `496aa866383`; SHA-256:

```text
ee59909ceb6ce691e60963ea6642b8440ed46678a1d4485629029eaaba95eb2d
```

The context table implementation is
`src/runtime/xray/xray_thread_context_v1.h` in this branch.

## Run record

Compiler: GCC 13.3.0 (`cc (Ubuntu 13.3.0-6ubuntu2~24.04) 13.3.0`).

The first attempt incorrectly imposed `ulimit -v 262144`. `mold` could not
reserve its 8 GiB virtual address range, so linking failed before an executable
was produced. This was a harness-limit mistake, not a fixture or product
failure. No retry used that command.

The first corrected attempt ran under the required process-tree cgroup cap:

```sh
CAP_MEM_MAX=256M CAP_REQUIRE=1 scripts/resource/run_capped.shs timeout 30s sh -c \
  'cc -std=c11 -D_XOPEN_SOURCE=700 -pthread -Wall -Wextra -Werror \
    test/fixtures/xray/check-xray-thread-context.c \
    -o /tmp/simple-check-xray-thread-context && \
   /tmp/simple-check-xray-thread-context'
```

Result: exit 0, `PASS xray thread context and resident admission`. The fixture
completed in under one second. `CAP_REQUIRE=1` ensures the runner fails rather
than silently falling back when the systemd cgroup cap is unavailable. The
compiler and fixture ran sequentially as one compiler worker.

After Astra-approved accounting assertions were added, one targeted rerun used
the same cgroup cap and command. It passed the sticky inexact-counter behavior:
`UINT64_MAX-1` transitions to the `UINT64_MAX` unknown-total sentinel, and later
increments leave the sentinel unchanged. The eight-CAS-failure fallback was
reviewed but not deterministically exercised.

Current thread-context header SHA-256:
`7d105c7ec09af9593c57a7d6b19a40ac785969ef3806d3a1b25e6c488db75303`.
Current fixture source SHA-256:
`0940d91f030e136a9fe12c379a0d56a091c543fc0ebadd160541fa605f980f50`.
Final executable SHA-256:
`61cb34e0786a734f70547fc669597b10544bd6aa68e0a0da98f2a63e6f7e0f0b`.
