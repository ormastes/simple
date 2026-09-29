<!-- codex-research -->
# SOSIX runtime unification: feature requirement options

**Status:** awaiting user selection, 2026-09-26. These choices refine the full [proposal](../../01_research/runtime/sosix_unification/simple_sosix_runtime_unification_design_plan_2026-09-05.md); they do not remove its compiler, interpreter, loader, rendering, GPU, or SimpleOS endpoint. The [current local evidence](../../01_research/local/sosix_runtime_unification.md) and [domain constraints](../../01_research/domain/sosix_runtime_unification.md) explain the gaps. Do not write the final requirement file or delete unchosen options until selection.

## F1: integration order for the first admitted release

All choices require a versioned RU-001 route census, the canonical task/ring and retirement contract, and the proposal's three distinct release boundaries. “First” only decides where the first complete vertical acceptance path runs. Later host, renderer/GPU, and SimpleOS rows remain required.

| Choice | First acceptance path | Pros | Cons | Effort |
|---|---|---|---|---|
| **A. Contract and hosted path first (recommended)** | Finish RU-001, common registry, exact/typed FS paths, canonical Future, hosted provider, then compiler/interpreter/loader and SimpleOS. | Gives every later provider one tested contract and a real host oracle; aligns with the proposal's dependency order. | SimpleOS release evidence arrives later; hosted provider work may need adaptation to embedded limits. | Large: about 35–70 source/spec files before core admission; entire objective is much larger. |
| **B. SimpleOS path first** | After RU-001 and shared contracts, admit positioned FS through x86 trap, owner installation, QEMU, and physical release evidence before broad hosted migration. | Exposes kernel ABI and no-allocation failures early; directly advances SimpleOS. | A guest-only slice does not prove compiler/host convergence; unavailable pure-Simple compiler or hardware can stall first admission. | Large: about 25–55 source/spec files for the first admitted slice, plus QEMU/hardware infrastructure. |
| **C. Compiler and loader path first** | After RU-001 and registry, migrate interpreter dispatch, driver host injection, and loader generation lifecycle before broader service providers. | Resolves parser/runtime bootstrap coupling early; makes one dispatch source usable across engines. | Bootstrap and ABI risk is high while provider semantics remain incomplete; does not itself validate native host or SimpleOS effects. | Very large: about 40–80 source/spec files for the first admitted slice. |

## F2: raw positioned-write contract on Linux `O_APPEND`

POSIX specifies offset-positioned `pwrite`; Linux documents append behavior for `pwrite` on an `O_APPEND` descriptor. The choice must be explicit. All choices still require object-code checks for any promised direct alias, separate typed/capability validation, and native host tests.

| Choice | Contract | Pros | Cons | Effort |
|---|---|---|---|---|
| **A. Native raw alias plus strict typed route (recommended)** | Raw `sosix.posix.pwrite` inherits host behavior and names the Linux exception; a distinct checked typed service promises offset semantics or rejects an incompatible descriptor. | Keeps the zero-wrapper raw alias claim honest and gives portable callers a reliable contract. | Two clearly named surfaces and compatibility tests are needed; typed strict path may require descriptor control or reject. | Medium: about 6–12 source/spec files across lowering, façade and provider tests. |
| **B. Strict POSIX semantics on all public routes** | Every public `pwrite` honors the requested offset, including Linux `O_APPEND`; use a controlled descriptor/provider path when raw libc cannot do so. | One portable result contract for users. | An arbitrary-descriptor direct-libc alias cannot meet this claim on Linux; zero-wrapper promise must be narrowed. | Large: about 10–20 files plus descriptor ownership and concurrency tests. |
| **C. Native semantics on all routes** | All `pwrite` routes document Linux `O_APPEND` behavior as a platform exception. | Smallest implementation and simplest direct alias. | Weakens portable positioned-write semantics for typed SOSIX and may surprise cross-platform users. | Small to medium: about 4–8 files, but compatibility documentation remains permanent. |

## Required invariants across every choice

- D08: admission, logical completion, and physical retirement are distinct; cancellation/timeout never releases a live buffer, slot, DMA mapping, or provider generation.
- Preserve `SimpleRing` and the canonical task/Future contract; no second scheduler, ring ABI, renderer submit owner, or loader.
- Preserve the compiler driver ABI, lazy loader startup, compatibility window, and separate native host, QEMU, hardware, GPU-proxy, and direct-device evidence rows.
- Do not claim a runtime release from source presence, model tests, or a source-only trap guard. Existing AC-3b and provider gaps remain release blockers until admitted execution evidence exists.

**Selection needed:** one F1 choice and one F2 choice. Record the selected contract in `doc/02_requirements/feature/sosix_runtime_unification.md`; delete this options file only after that final file is accepted.
