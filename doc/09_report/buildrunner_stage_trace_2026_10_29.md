# BuildRunner stage trace and direct Phase 2 comparison — 2026-10-29

## Result

The new opt-in `--trace-stages` CLI exposes the different paths without changing compiler selection, V4 admission, or resource limits. The retained direct Hello succeeded through the LLVM positional driver. A fresh actual BuildRunner run reached the shared worker's V4 capability check and refused before starting the same pinned Phase 2 compiler. It did not execute its requested Cranelift coordinator route. Therefore these receipts do not establish a backend performance or correctness comparison.

| Fact | Retained direct Hello | Actual traced BuildRunner |
|---|---|---|
| Phase compiler SHA-256 | `0d6f2e4720845195c9f91de292056fac4c57cabef81390507c78d95e51133a28` | Same |
| Requested route | positional `native-build FILE`, LLVM, low-memory | `--source/--entry/--entry-closure`, Cranelift coordinator |
| Observed progress | load sources, parse, HIR/typecheck, monomorphize, mode dispatch, linked executable | root/source/database/scheduler, input admission, worker dispatch, memory admission, V4 capability check, refusal/result collection |
| Build exit | 0 | 2 |
| Compiler started | yes | no; exact no-child-started receipt retained |
| Output execution | exact `Hello\n`, exit 0 | no output published |
| Sampled process-tree peak | 54,784 KiB | 1,142,192 KiB (P1-interpreted manager and worker, not P2 compiler RSS) |
| Compiler rebuilt | no | no |

The new run retained `worker.error = exact process observation V4 unavailable` and its matching no-child-started receipt. The watchdog recorded `quiescent=1`, `observer_errors=0`, under the requested 60-second/2-GiB bounds. `v4-start/owned` never appeared. The manager returned infrastructure failure, not compiler failure or successful qualification. An initial setup attempt refused missing state/output directories at root admission; those logs were retained, directories created, and the bounded rerun reached the existing V4 refusal.

## Implementation

The Hello matrix writes per-command SDN begin/end files, with phase/backend/route/compiler identity and exit status. The option explicitly reapplies only the five existing compiler diagnostic settings after environment sanitization, within the existing bounded compiler logs. Managed Hello forwards the option to its manager and its pinned Python lane driver.

The canonical manager and shared worker emit SDN records for real lifecycle boundaries. Local and SSH transports forward the flag. Standalone Linux/Windows workers also emit their native owner admission/start/result events. The canonical flag does not mutate task/compiler environment or identity; arbitrary argv, paths, environment values and free-form errors are excluded from the new structured records. Diagnostic events do not substitute for receipts or authority.

## Validation and limitations

- Python TDD: two new tests initially failed because trace/environment helpers were absent; all 28 Hello tests then passed after implementation, including provider flag forwarding and opt-in/redaction behavior.
- Pinned P1 interpreter diagnostics: CLI parser 7/7; trace encoder 3/3, including equals-form CLI arguments and secret-value omission. These are bootstrap-seed diagnostics, not self-hosted compiler qualification.
- One actual fresh manager run demonstrated propagated manager/worker traces and the unchanged V4 refusal. The already-green direct build was inspected, not rerun.
- Astra source review found that standalone Linux/Windows workers ignored the option. Their entrypoint forwarding and real owner-boundary logs were added and reviewed; native Linux/Windows execution remains unverified on this macOS host.
- No Phase 2 compiler rebuild, no V4 bypass, and no successful managed build claim.

## Evidence

- Retained direct: `/Users/ormastes/simple/build/verify/runner-debug-logs-20261029/p2-hello-logged/run.0ymgybzj` (`command.txt`, `receipt.txt`, `build.stdout`, `build.stderr`).
- Prior manager refusal: `/private/tmp/real-buildrunner-retry-20261029-vg0rlds8`.
- New manager: `/var/folders/94/j3lc49d93bx148gqls5kx5d40000gn/T/buildrunner-stage-trace-20261029-ijjfxg59` (`manager-run.stdout`, `manager-run.status`, `manager-run.rss.env`, `state/attempts/hello/1/local/compiler.not-started.sdn`).
- Focused diagnostic test logs: `build/verify/trace-stages-20261029`.
- Usage: [BuildRunner stage trace guide](../07_guide/tooling/buildrunner_stage_trace.md).
