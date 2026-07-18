# LLM Runtime vLLM/Torch Feature Requests

Tracker for host-dependent runtime work discovered while hardening the local
LLM dashboard, vLLM control surface, svLLM/NVFS streaming path, and Torch
interface.

Id scheme: `FR-LLM-RUNTIME-####`, monotonic, no reuse.
Lifecycle: `Open` -> `Accepted` -> `Implemented` or `Rejected`.

---

## Open Requests

### FR-LLM-RUNTIME-0001 - Prove live local vLLM serving

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Target:** vLLM runtime control and dashboard evidence
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Replace intent-only vLLM request planning with live
  host evidence against an installed local `vllm` endpoint before claiming
  serving readiness.
- **Acceptance-criteria:**
  - [ ] Runtime control starts or attaches to a local vLLM-compatible endpoint
        and probes `/v1/models` through the runtime-owned HTTP facade.
  - [ ] Dashboard `/api/vllm/control` start, poll, probe, and stop actions emit
        JSONL that distinguishes live process/HTTP success from unavailable
        host dependencies.
  - [ ] Operator docs and SPipe manuals show the live evidence keys and the
        unavailable-host classification.

### FR-LLM-RUNTIME-0002 - Complete svLLM NVFS streaming adapters

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Target:** svLLM model streaming over NVFS
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Implement the native adapters required for true
  streaming model loads instead of local file-backed byte-read readiness only.
- **Acceptance-criteria:**
  - [ ] svLLM streaming supports async scheduling, pinned buffer registration,
        and device staging through owner-layer facades.
  - [ ] Readiness evidence reports true streaming support separately from
        `local_read_bytes` fallback evidence.
  - [ ] Tests cover unavailable adapter paths and at least one real streaming
        adapter path without hiding unsupported pointer-write behavior.

### FR-LLM-RUNTIME-0003 - Prove live CUDA Torch optimizer execution

- **Filed-on:** 2026-06-28
- **Filed-by:** Codex
- **Target:** Torch interface and optimizer device placement
- **Priority:** P1
- **Status:** Open
- **Requested-semantics:** Move beyond source-contract readiness by executing a
  real optimizer step against a live libtorch CUDA installation.
- **Acceptance-criteria:**
  - [ ] A host-gated Torch evidence command records CUDA availability, tensor
        device placement, optimizer state device placement, and optimizer step
        success.
  - [ ] CPU-only or missing-libtorch hosts report an explicit unavailable
        classification rather than PASS.
  - [ ] The architecture, design, dashboard, and SPipe manuals identify which
        checks are source-contract proof and which checks are live CUDA proof.
