<!-- codex-plan-draft -->
# Traceability Scaffold: SimpleOS AI CLI JS/Node Port

Status: pending user option selection. This is not final requirements.

## Selection Gate

Final requirements cannot be written until the user selects:

- Feature option: A, B, C, or D from
  `doc/02_requirements/feature/simpleos_ai_cli_js_node_port_options.md`.
- NFR option: 1, 2, or 3 from
  `doc/02_requirements/nfr/simpleos_ai_cli_js_node_port_options.md`.

Recommended pending selection: Feature A, NFR 1+3.

## Acceptance Criteria Trace

| AC | Pending requirement family | Evidence needed |
|---|---|---|
| AC-1 | JS/Node-compatible API subset | Final feature requirements list supported `fs`, process, terminal, network/TLS, timers, module loading, package, and credential behavior |
| AC-2 | SimpleOS OS service exposure | Design maps each selected Node API to SimpleOS VFS, process, terminal, network/TLS, async, and capability modules |
| AC-3 | Codex/Claude/Gemini manifests | Manifest artifact declares runtime, entrypoint, args, grants, unsupported features, and package/source pins for all three CLIs |
| AC-4 | QEMU lanes | Spec or runner metadata covers RISC-V, x86, and ARM guest-side runtime plus AI CLI smoke markers |
| AC-5 | Hardening denials | Focused tests deny host escape, ambient credentials, undeclared process spawn, undeclared file access, and undeclared network access |
| AC-6 | SPipe specs/manuals | `test/system/..._spec.spl` and generated `doc/06_spec/...` scenario manual contain real assertions and no placeholder passes |
| AC-7 | Blocker evidence | Tracker/state records blocked targets with exact missing runtime, syscall, package, or QEMU evidence |

## First Agent Task Queue After Selection

1. Write final feature requirements:
   `doc/02_requirements/feature/simpleos_ai_cli_js_node_port.md`.
2. Write final NFR requirements:
   `doc/02_requirements/nfr/simpleos_ai_cli_js_node_port.md`.
3. Promote or replace the draft contract:
   `doc/05_design/simpleos_ai_cli_js_node_port_contract_draft.md`.
4. Add architecture:
   `doc/04_architecture/simpleos_ai_cli_js_node_port.md`.
5. Add detail design:
   `doc/05_design/simpleos_ai_cli_js_node_port.md`.
6. Add SPipe system spec:
   `test/system/os/simpleos_ai_cli_js_node_port_spec.spl`.
7. Generate scenario manual:
   `doc/06_spec/system/os/simpleos_ai_cli_js_node_port_spec.md` or the repo
   canonical output path from `bin/simple spipe-docgen`.
8. Implement the selected first code seam.

## First Code Seam Candidates

- Manifest-to-capability adapter for AI CLI apps.
- QEMU marker contract for JS runtime and AI CLI smoke.
- SimpleOS Node compatibility API matrix module.
- Negative-test harness for denied file/process/network/credential access.

## Current Non-Selected Blocker

The SPipe flow is intentionally stopped before final requirements because no
explicit feature/NFR option selection has been received yet.
