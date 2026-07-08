# SimpleOS Memory Leveling Agent Tasks

Status: selected.

## Scope

Implement selected `A + 1 + 1B`: profile-configured policy model plus model and
profile-footprint evidence.

## Lanes

- Main lane: Codex implements docs, policy module, SSpec, and generated manual.
- Sidecar lanes: N/A for this slice; the policy surface is small and local.
- Merge owner: Codex current session.
- Final reviewer: best available normal/highest-capability reviewer before
  release or done marking.

## Shared Names

- Module: `os.kernel.memory.memory_leveling`
- Spec: `simpleos_memory_leveling_spec.spl`
- Manual-facing flow helper names:
  - `profile_summary_line`
  - `movement_decision_line`

## Done Criteria

- Final requirements exist and option docs are deleted.
- Architecture, design, test plan, agent tasks, and guide exist.
- Policy module compiles.
- Focused SSpec passes once.
- Generated manual exists under `doc/06_spec/03_system/os/`.
- No executable `.spl` files exist under `doc/06_spec`.
