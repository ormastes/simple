<!-- codex-plan -->
# System Test Plan: SimpleOS AI CLI JS/Node Port

Status: selected contract-first slice implemented for manifest hardening, and
Node-compatible runtime grant conformance is covered by
`test/feature/js/node_api_conformance_spec.spl`. Full QEMU runtime smoke remains
pending Node-compatible runtime provisioning.

Current QEMU harness:

- `scripts/check-ai-cli-qemu-lanes.shs --contract-only` materializes the
  selected Codex/Claude/Gemini by x86/RISC-V/ARM lane marker contract and exits
  successfully without claiming guest evidence.
- `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package` materializes the
  selected host-side smoke package tree and reports
  `ai_cli_qemu_lanes_status=stage-smoke-package` with reason
  `host-package-materialized-no-guest-validation`; it does not read serial logs
  or claim QEMU validation.
- The same stage mode writes a disk-import manifest at
  `build/ai-cli-qemu-lanes/reports/ai-cli-disk-import.tsv` by default. Each row
  records app, target, guest path, host path, byte count, and digest for later
  FAT32 image ingestion.
- `scripts/check-ai-cli-qemu-lanes.shs --stage-smoke-package
  --populate-fat32-image <img>` mirrors the selected staged tree into an
  existing formatted FAT32 image and reports
  `fat32_populate_status=host-image-populated` only when the host populator
  succeeds. This is host-side image evidence, not guest serial validation.
- Default mode checks staged runtime artifacts under
  `build/os/ai-cli-runtime-staging/sys/runtime/node-compatible/<target>/runtime.smf`,
  CLI bundles under `build/os/ai-cli-runtime-staging/sys/apps/<app>/<app>.js`,
  and guest serial logs under `build/os/ai-cli-*.serial.log`.
- The harness must fail until real guest serial logs contain every required
  marker. This preserves the Phase 6 blocker instead of treating host-side
  package generation as QEMU validation.

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
- Runtime conformance: `node_api_conformance_spec.spl` covers explicit positive
  and denial behavior for credential env, file, network, and process grants.
- QEMU lane harness: `scripts/check-ai-cli-qemu-lanes.shs` records expected
  runtime artifact paths, serial log paths, lane scenarios, and required marker
  files for the 3x3 app/target matrix.
- Host provisioning: `--stage-smoke-package` writes `AI_MANIFEST.SDN`,
  `launch.spl`, `qemu_markers.txt`, the short-name package manifest, generated
  `<app>.js` smoke entry, and `runtime.smf` under the FAT32-like staging tree.
- Disk ingestion bridge: the generated TSV import manifest makes the staged
  tree consumable by a later image-builder slice without treating manifest
  generation as guest execution.
- Host FAT32 ingestion readiness:
  `test/unit/os/port/host_fat32_tree_populator_spec.spl` now proves the generic
  host tree populator can mirror the AI CLI staging layout, including
  `sys/runtime/node-compatible/x86/runtime.smf` and `sys/apps/codex/codex.js`,
  into a formatted FAT32 image and preserve payload bytes.
- Harness image population: `--populate-fat32-image <img>` connects the staged
  AI CLI tree to the host FAT32 populator and fails the harness if the image
  mirror fails.
- Still pending: guest QEMU runtime smoke and kernel/OS-layer VFS, socket, and
  process boundary evidence.
