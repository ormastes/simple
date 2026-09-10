# LLM Build Progress Surface Architecture

```text
native-build/bootstrap manager
  -> typed progress call
      -> append-only event evidence
      -> BuildProgressSnapshot materialization
          -> monotonic/stale-writer admission
          -> atomic current.sdn replacement
              -> reader API / simple build-progress
```

The wire-neutral model lives in `std.common.build_progress`. Atomic filesystem publication and reading live in `std.nogc_sync_mut.build_progress`. The compiler supplies already-known progress facts. Bootstrap owns root/path/build-id configuration. The CLI reads only the snapshot. No product API derives status by scanning logs.

The current snapshot is generation-like: updates from one build must increase sequence and elapsed time. A different build ID is never admitted by a writer. The manager initializes ownership before launching workers; old workers then fail closed instead of overwriting the current build.
