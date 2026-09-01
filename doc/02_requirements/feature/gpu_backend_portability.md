# Feature: GPU backend portability and the CUDA tutorial curriculum

Write once, run on any GPU backend the host can actually provide — and teach it
with a tutorial that is itself executable. This document is the requirement
source for the two acceptance specs under `test/03_system/acceptance/`.

Related: `doc/03_plan/lib/gpu/gpu_cuda_hardening_plan_2026-08-25.md`,
`examples/08_gpu/backends/README.md`,
`examples/08_gpu/simple_cuda_example/README.md`.

## Portability

| id | requirement | verified by |
|----|-------------|-------------|
| REQ-GPU-PORT-001 | One GPU program runs unchanged on cuda, vulkan and metal; the program source is identical for every backend. | `gpu_backend_portability_acceptance_spec.spl` |
| REQ-GPU-PORT-002 | The backend is selected by the `gpu:` section of `simple.sdn` alone — no source edit, no environment variable, no CLI flag. | same |
| REQ-GPU-PORT-003 | Each checked-in manifest under `examples/08_gpu/backends/{cuda,vulkan,metal}/` selects exactly its own backend, and the parse is device-free. | same |
| REQ-GPU-PORT-004 | A manifest with no `gpu:` section defaults to backend `auto`, submode `interpreter`, arch `auto`. | same |
| REQ-GPU-PORT-005 | `backend: auto` probes `cuda -> vulkan -> metal` and takes the first lane whose probe does not answer `skip:`. | same |
| REQ-GPU-PORT-006 | A backend that is unusable on the host yields an explicit `skip:<reason>` naming the backend; it never reports a fake pass and never silently substitutes another backend. | same |
| REQ-GPU-PORT-007 | On a live backend the shared SVM-G program produces the same observable result on every backend: `ok`, one RESULT record with value 9, exit code 3. | same |

## Tutorial curriculum

| id | requirement | verified by |
|----|-------------|-------------|
| REQ-GPU-PORT-008 | Every tutorial module directory ships a `README.md`. | `gpu_tutorial_curriculum_acceptance_spec.spl` |
| REQ-GPU-PORT-009 | Every module `README.md` contains at least one runnable ```sdoctest``` fence, so the teaching text is fail-closed rather than prose that can rot. | same |
| REQ-GPU-PORT-010 | Every module that ships a `main.spl` also ships a `spec.spl` — a runnable example is a tested example. | same |
| REQ-GPU-PORT-011 | The curriculum covers the workbook's tiers in full; the expected module set (11..19, 21..27, 31..38, 61..66, 71..73, 81..82) is asserted so a silently dropped module fails. | same |
| REQ-GPU-PORT-012 | If the tutorial submodule is not checked out, the spec reports an explicit skip naming the missing root — never a silent pass. | same |
