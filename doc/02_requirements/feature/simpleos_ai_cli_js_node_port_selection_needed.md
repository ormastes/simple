<!-- codex-research -->
# Selection Needed: SimpleOS AI CLI JS/Node Port

Final requirements are intentionally not written yet. The repo workflow requires
the user to select requirement options before `doc/02_requirements/feature/*.md`
and `doc/02_requirements/nfr/*.md` are finalized.

## Required User Choices

1. Feature option from
   `doc/02_requirements/feature/simpleos_ai_cli_js_node_port_options.md`:
   - Option A: Contract-first compatibility layer.
   - Option B: Bundled Node binary first.
   - Option C: Minimal JS agent runtime.
   - Option D: SEA/bundle-oriented port.

2. NFR option from
   `doc/02_requirements/nfr/simpleos_ai_cli_js_node_port_options.md`:
   - Option 1: Security-first gate.
   - Option 2: Portability-first gate.
   - Option 3: Reproducibility-first gate.

## Current Recommendation

Choose Feature Option A and NFR Option 1, carrying forward the pinned-artifact
and deterministic-log requirements from NFR Option 3.

## Why This Is The Recommended Path

- It aligns with the existing SimpleOS capability model before broad Node
  compatibility is attempted.
- It lets Codex, Claude, and Gemini CLI manifests declare exact file, process,
  terminal, network, and credential grants.
- It produces QEMU evidence that rejects host-only success and ambient authority
  before a V8/libuv/Node binary port can hide those problems.

## Reply Format

Use one short line:

```text
Feature A, NFR 1+3
```

or replace the letters/numbers with the preferred options.
