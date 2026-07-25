# Logging Feature Expert

## Role

Own feature-specific process knowledge for probe-gated logging across the 
codebase. Covers log-level conventions, retention policies for traces and 
diagnostics, probe-gate idioms in freestanding kernel code, and integration 
with infra tooling that consumes structured logs.

## Pipeline Links

- [verify skill](../../../../.claude/skills/verify/SKILL.md)

## Feature Links

- Log-retention policy: [doc/07_guide/infra/logging/log_retention_policy.md](../../../../doc/07_guide/infra/logging/log_retention_policy.md)
  — level-gated output, never delete historical logs, gate verbosity only.
- Testing guide: [doc/07_guide/app/testing/logging.md](../../../../doc/07_guide/app/testing/logging.md)
- Related layer experts:
  [bootstrap](../../layer_expert/bootstrap/skill.md) (redeploy diagnostics),
  [os_compositor](../../layer_expert/os_compositor/skill.md) (frame provenance logging)

## Probe-Gate Convention (2026-07-18)

**Baremetal kernel code:** per-file `fn _probe_debug() -> bool: false` (or 
`_probe_perf()`, etc.) in freestanding modules; module-global `val` 
initializers are unreliable on baremetal lanes, so use function-scoped probes 
with compile-time false defaults. Example:
```
fn _probe_debug() -> bool: false

fn render_frame():
  if _probe_debug():
    print("render: starting frame")
```

**Userland/hosted code:** can use module-level `val` probes if needed, but 
prefer per-function declarations for consistency.

## Log Retention (2026-07-18)

Never delete historical logs based on date or size alone. Instead:
- Gate verbosity by level (DEBUG, TRACE, PERF).
- Keep INFO and above permanently.
- Use log rotation (time-based or size-based) with archival, not deletion.
- Diagnostics for faults must be archived permanently (bug-tracking ref).

See [doc/07_guide/infra/logging/log_retention_policy.md](../../../../doc/07_guide/infra/logging/log_retention_policy.md) 
for full contract.

## Update Rule

After logging-infrastructure changes, probe-convention updates, or retention 
policy shifts, refresh this skill with new links and concrete patterns.

Template: `.spipe/spipe/doc/00_llm_process/template/feature_skill.md`
