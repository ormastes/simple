# Target-neutral DAP session: debug + profile

The DAP session in `src/app/dap/target_session.spl` (`TargetDapSession`) speaks
one protocol over any `DebugTarget`/`ProfileTarget` implementation — host today,
GPU backends once a lowering path exists.

Companion: [`lsp_dap.md`](lsp_dap.md) (the general LSP/DAP surface),
[capability-library authoring guide](../../language/capability_library_authoring.md)
(how to make a backend attachable at all — **read its hazards section before
writing an implementation**).

## Entry points

```simple
target_dap_session_host(program)                                  # host lane, no probe
target_dap_session_launch(launch_json, config, probe)             # testable: caller supplies config + probe
target_dap_session_launch_with_opts(launch_json, config, probe, opts)   # + AttachOpts
```

`config`/`probe` are injected rather than discovered so the whole routing matrix
is exercisable with **no hardware present**. The host lane uses `NeverProbe`,
which returns `skip:host-lane-must-not-probe-<backend>` if it is ever called —
a host-tagged launch that probes is a routing bug, and it says so instead of
returning a plausible-looking skip.

Profiling is **armed at attach** through `AttachOpts.profile`. There is no
"enable profiling later": GPU PROF-1 cannot be turned on after upload, so the
host lane matches that constraint deliberately.

## Standard requests

`initialize`, `setBreakpoints`, `threads`, `stackTrace`, `next`/`stepIn`/
`stepOut`, `continue`, `disconnect`/`terminate`.

Two behaviours worth knowing:

- Every request other than `initialize`, the profile pair, and
  `disconnect`/`terminate` is refused with `not_ready_reason()` until the
  session has launched.
- An unknown command gets a DAP **error** response — never a silent success.

## Custom profile requests

| Command | Body |
|---|---|
| `simple/profileBegin` | arms/starts the profile window on the attached target |
| `simple/profileEnd` | `profile_report_json(report)` |

The report JSON mirrors `ProfileReport`: `level` (lowercase — `"native"`,
`"emulated"`, `"unavailable"`), `wall_ns`, `device_ns`, `steps`, `detail`.

**`-1` means "not measured", not "zero".** `PROFILE_ABSENT = -1` is the only
honest absent value; a client must not chart it as 0. Use the same test the
library uses: `device_ns >= 0` / `steps >= 0`. A landed `profile_end` was fixed
by P7 for reporting `0` where it meant absent.

## Target selection

The launch config carries a lane tag. An **absent** tag resolves to the host
lane without consulting the probe at all; a GPU tag routes through the resolver
and the injected `GpuBackendProbe`. The resolver and the `debug-doctor` CLI
(`src/app/debug_doctor/main.spl`,
`src/lib/nogc_sync_mut/debug_doctor/matrix.spl`) share that routing, so
`debug-doctor` is the way to see what a given host would resolve to before you
launch.

## GPU attach is ROUTING-ONLY

> The DAP session can *route* a launch to a GPU backend. It cannot debug your
> program there.

There is no `.spl` → SVM-G compilation path. `lower_svmg_program`
(`src/compiler/70.backend/svmg_lowering.spl:683`) is scoped to HIR test bodies
and has **no caller outside `70.backend`**. So GPU attach resolves, probes, and
reports — and then has no program to load.

Filed:
`doc/08_tracking/bug/no_general_spl_to_svmg_path_blocks_dap_gpu_attach_2026-08-09.md`.

Do not read the GPU routing specs as evidence that GPU debugging works. They
prove the routing. The device-side debug/profile evidence that *is* real comes
from the CUDA and Vulkan lane executors driven directly (20 launches each,
field diffs clean) — not through DAP.

## Lab HTTP surface

The notebook/Lab server exposes the same capability over HTTP
(`src/app/simple_lab/lab_server.spl`):

```
POST /api/lab/sessions/:id/debug
POST /api/lab/sessions/:id/debug/step
POST /api/lab/sessions/:id/debug/resume
POST /api/lab/sessions/:id/debug/break
GET  /api/lab/sessions/:id/debug/state
POST /api/lab/sessions/:id/debug/profile/begin
POST /api/lab/sessions/:id/debug/profile/end
POST /api/lab/sessions/:id/profile          # the %profile cell magic
```

`%profile` is recognised by `lab_profile_magic_matches` and executed by
`lab_profile_cell(body, budget)` (`src/app/simple_lab/lab_debug.spl`). The same
`PROFILE_ABSENT` rule applies to `lab_profile_report_json`.

## Honesty note

Every result above was measured under the **Rust seed**; none of it is
self-hosted evidence. Metal's device path is entirely unverified — see the
authoring guide's honesty preamble.
