# macOS GPU Agent Plan - 2026-07-10

## Objective

Produce deployment-grade Metal evidence and close the remaining self-hosted
GPU queue verification gap.

## Lanes

| Lane | Agent | Work | Evidence |
|---|---|---|---|
| Metal readback | Mac agent A | Run generated Metal 2D, Engine2D framebuffer, and CPU/Metal parity checks with Xcode tools. | Three dated reports; submit/readback true; zero mismatches. |
| Self-host deploy | Mac agent B | Build the pure-Simple self-hosted binary, run redeploy gate, then run queue and GPU evidence checks. | Gate log; post-swap `-c` smoke; production queue report. |
| Review | Higher-model reviewer | Check reports, platform assumptions, stale-artifact provenance, and requirement coverage. | PASS/FAIL review with exact missing evidence. |

## Commands

```sh
sh scripts/check/check-metal-generated-2d-readback.shs
sh scripts/check/check-metal-engine2d-framebuffer-readback-evidence.shs
sh scripts/check/check-engine2d-cpu-metal-parity-evidence.shs
sh scripts/check/cert/redeploy_gate/redeploy_gate.shs build/bootstrap/full/x86_64-unknown-linux-gnu/simple
SIMPLE_BIN=bin/simple SIMPLE_LIB=src sh scripts/check/check-production-gui-web-host-gpu-queue-readback-evidence.shs
```

## Merge and Done Rules

- Merge owner: main workspace owner.
- Do not treat Linux Metal-unavailable output as Metal PASS.
- Do not accept evidence from a stale binary; record binary path and timestamp.
- Reviewer must approve before closing the TODO.
