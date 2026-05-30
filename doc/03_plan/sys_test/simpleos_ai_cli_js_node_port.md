<!-- codex-plan-draft -->
# System Test Plan Draft: SimpleOS AI CLI JS/Node Port

Status: draft only. Final SPipe specs wait for selected requirements.

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
   - Placeholder markers containing dummy/fake/stub/synthetic pass are rejected
     unless the scenario is explicitly a negative test.

## Expected SPipe Matcher Set

Use only built-in matchers: `to_equal`, `to_be`, `to_be_nil`, `to_contain`,
`to_start_with`, `to_end_with`, `to_be_greater_than`, and `to_be_less_than`.

## Candidate Spec Location

`test/system/os/simpleos_ai_cli_js_node_port_spec.spl`

## Evidence To Capture

- Manifest id, runtime kind, and declared grants.
- QEMU architecture, machine, CPU, timeout, and serial log path.
- Guest-side marker for runtime start.
- Guest-side marker for CLI command start.
- Guest-side marker for each hardening denial.
- Explicit blocker marker if a target cannot run the selected runtime yet.
