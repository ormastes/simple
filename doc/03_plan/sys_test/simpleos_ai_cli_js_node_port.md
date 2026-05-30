<!-- codex-plan -->
# System Test Plan: SimpleOS AI CLI JS/Node Port

Status: selected contract-first slice implemented for manifest hardening. Full
QEMU runtime smoke remains pending Node-compatible runtime provisioning.

## Scenario Families

1. Manifest hardening:
   - Given a Codex/Claude/Gemini manifest without file grants, workspace reads
     are denied.
   - Given a manifest without process grants, child process spawn is denied.
   - Given a manifest without network grants, API connection attempts are
     denied.
   - Given a manifest without credential grants, ambient secret reads are
     denied.

2. Runtime smoke:
   - Boot SimpleOS in QEMU.
   - Start the selected JS/Node-compatible runtime.
   - Run a non-authenticated CLI smoke command such as version/help/status.
   - Capture guest-side serial markers.

3. Multi-arch evidence:
   - x86 lane emits the runtime and AI CLI smoke markers.
   - RISC-V lane emits the runtime and AI CLI smoke markers or a documented
     blocker marker.
   - ARM lane emits the runtime and AI CLI smoke markers or a documented
     blocker marker.

4. Negative evidence:
   - Host-side command success without guest serial markers fails the scenario.
   - Placeholder-style success markers are rejected unless the scenario is
     explicitly a negative test.

## Expected SPipe Matcher Set

Use only built-in matchers: `to_equal`, `to_be`, `to_be_nil`, `to_contain`,
`to_start_with`, `to_end_with`, `to_be_greater_than`, and `to_be_less_than`.

## Candidate Spec Location

`test/system/os/simpleos_ai_cli_js_node_port_spec.spl`

Mirrored manual: `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md`

## Evidence To Capture

- Manifest id, runtime kind, and declared grants.
- QEMU architecture, machine, CPU, timeout, and serial log path.
- Guest-side marker for runtime start.
- Guest-side marker for CLI command start.
- Guest-side marker for each hardening denial.
- Explicit blocker marker if a target cannot run the selected runtime yet.

## Current Coverage

- REQ-001 through REQ-003: built-in manifest fields, package pins,
  deterministic summary, and marker data.
- REQ-004 and REQ-005: invalid manifests and undeclared grant denials.
- REQ-006: `x85` target normalization to x86.
- REQ-007: explicit full Node/V8/libuv later-layer blocker.
