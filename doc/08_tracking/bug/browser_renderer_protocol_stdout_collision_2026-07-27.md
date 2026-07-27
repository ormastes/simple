# Browser renderer protocol shares ordinary stdout

Status: release blocker

The sandbox renderer currently writes SBR1 on stdout. Renderer/layout code can
also print diagnostics, so hostile or merely degenerate page input can inject
bytes ahead of a valid frame and force a protocol failure.

The 2026-07-27 bounded fix attempt routed SBR1 through child fd 3 while sending
stdout/stderr to `/dev/null`. The live sandbox transport check still failed to
observe `sandbox-ok` after three fix/verify cycles, so the unproven change was
reverted.

Acceptance:

- ordinary stdout and stderr cannot reach the broker protocol stream;
- one dedicated protocol descriptor survives exec, Landlock, seccomp, and the
  `RLIMIT_NOFILE` policy;
- the live child writes noise to stdout/stderr and the broker receives exactly
  one valid SBR1 frame;
- Linux passes the existing containment test and MinGW still compiles with
  `-Werror`;
- production entry wiring remains disabled until this check passes.
