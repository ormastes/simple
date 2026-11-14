# XRay thread-context fixture evidence

Date: 2026-11-14

## Scope

This fixture compiles and runs the production thread-context and resident
admission headers. It checks selected pin and TLS-slot behavior, including two
pthread attachments, distinct arenas, same-pool idempotence, cross-pool
rejection, no-reuse exhaustion, malformed extent/schema rejection, bounded
unattached-loss accounting, and close/drain behavior.

It does not verify `runtime_thread.c` opt-in hooks, event production or
retention, a concurrent close/acquire race, Windows behavior, external-thread
automatic attachment, or forced termination cleanup.

## Source provenance

`src/runtime/xray/xray_resident_admission_v1.h` is byte-identical to provider
commit `496aa866383`; SHA-256:

```text
ee59909ceb6ce691e60963ea6642b8440ed46678a1d4485629029eaaba95eb2d
```

The context table implementation is
`src/runtime/xray/xray_thread_context_v1.h` in this branch. Fixture source
SHA-256: `00f4b0d4102be8f4aad7d0ce709d672a79705148fd95b017a9f927194034a9f3`.

## Run record

Compiler: GCC 13.3.0 (`cc (Ubuntu 13.3.0-6ubuntu2~24.04) 13.3.0`).

The first attempt incorrectly imposed `ulimit -v 262144`. `mold` could not
reserve its 8 GiB virtual address range, so linking failed before an executable
was produced. This was a harness-limit mistake, not a fixture or product
failure. No retry used that command.

The corrected single attempt ran under the required process-tree cgroup cap:

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

Executable SHA-256: `63961d97fe439000549f969d926c4dd23501db8daa5d32b141b15cb8f32139ce`.
