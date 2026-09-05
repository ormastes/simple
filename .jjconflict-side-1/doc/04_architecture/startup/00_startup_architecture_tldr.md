# Startup Architecture TLDR

Startup turns a path or launcher request into the correct execution mode using
metadata, not guessing.

```text
CLI / WM / package runner
  -> artifact kind
  -> launch metadata
  -> StartupLaunchPlan
       |-- argv parser?
       |-- mmap/read-ahead?
       |-- native dynlibs?
       |-- SMF dynlibs?
  -> interpreter / SMF loader / native entry / SimpleOS process
```

Main rules:

- Keep policy pure and mechanism-specific work in adapters.
- Preserve one-time argv normalization for direct script launch.
- Treat SimpleOS hover prefetch as non-executing byte warmup.
- Require metadata evidence for startup-sensitive optimizations.

Open next:

- `00_startup_architecture.md`
- `simple_app_startup.md`
- `simple_app_startup_tldr.md`

