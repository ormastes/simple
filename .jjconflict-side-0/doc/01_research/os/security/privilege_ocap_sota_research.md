# State-of-the-Art Privilege Architectures for an Object-Capability OS

Research date: 2026-07-13. Scope: deep external research (mechanism, not marketing) on
privilege/capability architectures across six systems, for a brand-new OS that (a) owns
its own compiler, (b) targets RISC-V + x86 + ARM, and (c) refuses to trade security for
performance. Every claim below is attributed to a source; numbers pulled second-hand
through search snippets rather than a directly-fetched primary PDF are flagged
"(unverified — re-check primary source)".

> **Tooling note**: this research environment does not have the `ctx_*` context-mode MCP
> tools (blocked/redirected per this repo's CLAUDE.md) actually registered, and `WebFetch`
> was hook-blocked in the sub-agent sessions that did this research. All findings below
> come from `WebSearch`, most of which returned direct quotes/paraphrases of primary
> sources (official manuals, ACM/USENIX/arXiv PDFs, project docs). Where a specific
> numeric table could not be confirmed against the primary PDF, it is flagged inline —
> re-verify before using in a citation-sensitive document (e.g. an ADR).

---

## 1. seL4 — the gold standard

### Capability model: CNode / CSpace / CDT
- A **CSpace** is built from **CNode** objects, each with 2^k slots (k = the CNode's
  "radix"). Capabilities live in slots.
- **CSpace lookup** is a guarded radix-tree walk (not a flat table): a capability address
  (`CPtr`) is resolved by walking CNodes. Each CNode capability carries a **guard** (bits
  that must match) and a **radix** (bits consumed to index into the CNode). On a guard
  match, the kernel indexes using the radix bits and recurses if the target slot holds
  another CNode — e.g. a 4-bit guard + 8-bit radix per level terminates after 24 bits in
  the manual's worked example. Depth semantics vary: fault-handling lookups resolve with
  the full CPtr; explicit operations like `seL4_CNode_Copy` take a caller-supplied depth
  and fail with a depth-mismatch error if bits remain unconsumed
  (`lookupSlotForCNodeOp` → `resolveAddressBits`).
- **Capability Derivation Tree (CDT)**: every Copy/Mint/derivation is tracked in a global
  provenance tree. `seL4_CNode_Revoke` walks the CDT from a chosen capability and deletes
  every capability transitively derived from it, across every CSpace in the system — this
  is how a server reclaims sole authority over an object it lent out, or how an untyped
  memory manager reclaims/retypes memory it handed out.

### Minting, delegation, revocation
- **Retype** (`seL4_Untyped_Retype`) is the *only* operation on an Untyped capability. It
  converts a region of untyped memory into smaller untyped caps or new typed kernel
  objects (TCBs, CNodes, Endpoints, page tables, ...). The kernel has **no internal
  allocator** — all object creation is explicit, capability-mediated, and driven from
  userspace, which owns all initial Untyped memory from boot.
  New objects from Retype start with full rights.
- **Copy** derives a new capability to the same object, optionally with a rights mask
  applied (rights only ever shrink through Copy/Mint/Move — never grow; this monotonicity
  underlies the integrity proof).
  **Mint** is like Copy but can also set type-specific data, notably **badges** on
  Endpoint/Notification caps so a server can distinguish which client-derived capability
  was used without trusting the client.

### IPC: Endpoints vs Notifications
- seL4 IPC is **always synchronous**. **Endpoints** are rendezvous points: `Send`/`Call`
  block until a matching `Recv` — no kernel-buffered messages (unlike Mach ports), which
  bounds kernel-side state and complexity.
- **Notifications** replaced the old "asynchronous IPC": word-sized arrays of binary
  semaphore flags, not message passing.

### IPC fastpath — concrete numbers
- A dedicated **fastpath** exists for `seL4_Call`/`seL4_ReplyRecv` under specific
  conditions, reported as **2–4x faster** than the slowpath.
- "Correct, Fast, Maintainable — Choose Any Three!" (NICTA/Elphinstone et al.) reports a
  **35% fastpath speedup** purely from restructuring C for the optimizing compiler, and
  found hand-tuned assembly gained **no further benefit** — evidence the tuned-C fastpath
  is already at the hardware floor.
- **x64 (Kaby Lake)**: fastpath client→server IPC ≈ **600 cycles**; slowpath client→server
  **>1,100 cycles**. A corrected round-trip figure (after a `sel4bench` timer-measurement
  bug fix) is **≈720 cycles**.
- **ARM11**: one-way fastpath IPC measured ~10% faster than the fastest IPC of any other
  kernel benchmarked on the same hardware (comparative, not an absolute figure from this
  pass).
- **Cross-kernel comparison (x86, intra-core round trip, cited via the seL4 whitepaper and
  corroborated by "Harmonizing Performance and Isolation in Microkernels," USENIX ATC
  2020)**: **seL4 = 986 cycles, Fiasco.OC = 2,717 cycles, Zircon = 8,157 cycles.**
- **RISC-V**: Hesham Almatary/Data61's original RV port (HiFive Unleashed U500,
  BOOM/VC707 FPGA), benchmarked via `sel4bench`: "can compete with ARM and x86" on IPC
  cycles even as an early prototype (exact table unverified — re-check primary source).
- seL4 on RV64 is verified **to the level of the executable binary** — called out as the
  **first 64-bit architecture** to reach that milestone.

### Formal verification — what's proven, what's assumed
- First general-purpose OS kernel with full **functional correctness** proof from
  abstract spec down through the C implementation (Klein et al., SOSP 2009, ~10 KLOC
  kernel).
- Extended (Klein et al., TOCS 2014) to correctness **down to binary machine code**, plus
  **integrity** (no write without an authorizing capability), **authority confinement**
  (authority changes only via explicit capability transfer, never silently), and later
  **information-flow / confidentiality (noninterference)** ("seL4 Enforces Integrity";
  "seL4: from General Purpose to a Proof of Information Flow Enforcement," IEEE S&P 2013).
- **Proof cost**: ~200,000 lines of Isabelle/HOL for ~10,000 lines of C; ~20–30
  person-years total (roughly 9 on tooling/automation, 11 on the seL4-specific proof); a
  from-scratch redo with today's toolchain is estimated at ~10 person-years.
- **Assumptions baked into the proof**: no post-boot kernel memory allocation (no heap,
  bounded stack, all free memory handed to the root task as Untyped); hardware behaves per
  spec and isn't tampered with; TLB/cache management correctness assumed; **DMA must be
  disabled or trusted** (no IOMMU proof); **no timing-side-channel guarantee** in the base
  proof (separate line of work: time protection); the original proof assumed
  **single-core** execution — multicore is deployed engineering-wise but full proof
  coverage under concurrency is still maturing.
- **MCS (Mixed Criticality System) kernel**: reworks scheduling to give userspace
  capability-authorized control over processor time (temporal isolation for
  mixed-criticality workloads). Mature on single core; MCS's security-property proof
  coverage is still catching up to the classic kernel.

### Verdict
**Adopt the mechanism wholesale.** Guarded radix-tree CSpace + CDT-based revocation +
Retype-from-Untyped object creation is mature, cross-architecture-proven (binary-verified
on RISC-V, mature on ARM/x86) — the design a new OS should not reinvent. Known open seams
to inherit *knowingly*, not blindly: multicore proof coverage and the DMA/IOMMU trust
assumption are still weak; don't assume seL4's guarantees extend to SMP or untrusted DMA
without doing that verification work yourself.

**Sources**: [seL4 Reference Manual](https://sel4.systems/Info/Docs/seL4-manual-latest.pdf) ·
[seL4 cspace.tex](https://github.com/seL4/seL4/blob/master/manual/parts/cspace.tex) ·
[seL4 Capability System slides (CHERI workshop, Cambridge)](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/workshops/pdfs/20160423-sel4-capabilities.pdf) ·
[seL4 Whitepaper](https://sel4.systems/About/seL4-whitepaper.pdf) ·
[seL4: Formal Verification of an OS Kernel, SOSP 2009](https://www.sigops.org/s/conferences/sosp/2009/papers/klein-sosp09.pdf) ·
[Comprehensive Formal Verification of an OS Microkernel, TOCS 2014](https://sel4.systems/Research/pdfs/comprehensive-formal-verification-os-microkernel.pdf) ·
[seL4 Enforces Integrity](https://trustworthy.systems/publications/nicta_full_text/4709.pdf) ·
[seL4: from General Purpose to a Proof of Information Flow Enforcement, IEEE S&P 2013](https://www.ieee-security.org/TC/SP2013/papers/4977a415.pdf) ·
[What is Proved and What is Assumed (FAQ)](https://sel4.systems/Info/FAQ/proof.pml) ·
[seL4 Proofs](https://sel4.systems/Verification/proofs.html) ·
[Correct, Fast, Maintainable — Choose Any Three!](https://trustworthy.systems/publications/nicta_full_text/5858.pdf) ·
[From L3 to seL4](https://flint.cs.yale.edu/cs428/doc/L3toseL4.pdf) ·
[MCS kernel — seL4 Discourse](https://sel4.discourse.group/t/mcs-mixed-criticality-systems-kernel/19) ·
[seL4 verified on RISC-V (RISC-V International)](https://riscv.org/blog/sel4-is-verified-on-risc-v/) ·
[seL4 on RISC-V Verified to Binary Code](https://microkerneldude.org/2021/05/05/sel4-on-risc-v-verified-to-binary-code/) ·
[IPC Performance of seL4 on RISC-V Platforms](http://heshamelmatary.blogspot.com/2018/06/ipc-perfoamnce-of-sel4-microkernel-on.html) ·
[seL4 Performance page](https://sel4.systems/performance.html) ·
[Harmonizing Performance and Isolation in Microkernels, USENIX ATC 2020](https://www.usenix.org/system/files/atc20-gu.pdf)

---

## 2. CHERI / CHERI-RISC-V / Arm Morello

### Hardware capability format ("CHERI Concentrate")
- A CHERI capability is **2x the native pointer width**: 128 bits on 64-bit platforms
  (64 bits on 32-bit platforms, e.g. CHERI-RISC-V RV32 / CHERIoT), **plus one out-of-band
  validity tag bit** that is not part of the addressable 128/64 bits.
- **Fields**: full-width address/cursor, compressed bounds (base + top, derived from a
  shared floating-point-style exponent + two mantissas), a permissions bitfield, an
  object-type (otype) field for sealing, plus the out-of-band tag.
- **Bounds compression**: exploits redundancy between the address and the two bound
  values. An **internal-exponent (IE) bit** selects between two encodings; when IE=1, a
  3-bit exponent is stored in the low bits of the base/top fields, trading precision for
  range. Mantissa width in CHERI ISAv9's 128-bit format is **14 bits**, which determines
  the "representable range" property: small/precise objects get exact bounds, large ones
  get bounds rounded outward.
- Exact Morello field-width breakdowns (address/bounds/otype/permission bit counts) were
  **contradictory across secondary sources during this research pass — re-check the
  primary Arm Morello Architecture Reference Manual Supplement (DDI0606) directly** before
  citing exact numbers. Morello's capability register is confirmed at **129 bits total**
  (128-bit capability + 1 tag bit), in dedicated capability registers alongside/overlapping
  the integer register file.
- **CHERI-RISC-V (RV64)**: 128-bit capabilities, same Concentrate-style compression.
  **CHERIoT (RV32, micro-capabilities — see §8)**: capabilities are **64 bits + 1 tag bit**
  (65 bits total); permissions compressed 16→**6 bits** (primary + dependent sets); otype
  shrinks to **3 bits** of hardware sealing space (extended via software-virtualized
  sealing); bounds still use the shared-exponent scheme, giving exact byte-granularity
  bounds for objects up to 510 bytes.

### Tag memory
- One tag bit per capability-sized, capability-aligned memory granule (128 bits on 64-bit
  CHERI, 64 bits on CHERIoT) and per capability-width register.
- Tags are **hardware-managed, stored out-of-band** from addressable memory; software
  cannot directly address/write tag bits — only capability-aware load/store instructions
  can set them (when storing a well-formed, valid capability), or hardware clears them.
- **Invalidation rule** (the anti-forgery core mechanism): any store to a tagged granule
  via a *non-capability* instruction, or any partial/misaligned overwrite, **clears the
  tag** — you cannot synthesize a capability by writing raw bytes.
- **Propagation**: capability-aware load/store/move instructions preserve the tag as long
  as the value and its provenance/monotonicity are preserved intact; a violating
  instruction zeroes the tag rather than erroring.
- **Overhead**: tag storage is <1% memory in principle (1 bit / 128–256 bits of data).
  Measured DRAM/tag-table overhead was **<3%** for working sets that fit the tag cache's
  reach, per "Efficient Tagged Memory" (ICCD 2017), with tag-table compression shrinking
  cache footprint further by exploiting adjacency.

### Monotonicity
- Core invariant: capability-manipulating instructions can only **narrow** the derived
  capability relative to its source, never widen. Violating instructions either fault, are
  disallowed by encoding, or clear the tag on the result.
- Enforcing instructions: **CSetBounds** (shrink base/length to a subrange; if the request
  can't be represented exactly, bounds round outward to the nearest representable
  superset, and the tag clears if that would exceed the source's own bounds);
  **CAndPerm** (bitwise-AND the permission mask — can only remove bits); **CSeal/CUnseal**
  (CSeal, using a capability holding `permit-seal`, writes the sealing capability's value
  into the otype field, making the result non-dereferenceable/non-executable until
  unsealed; CUnseal is the sole path back, gated on holding `permit-unseal` — this is what
  makes sealed capabilities usable as unforgeable object handles / entry points).
- Provenance is architecturally enforced: a capability is valid only if derived from
  another valid, in-bounds capability via a capability-aware instruction; an
  integer-to-pointer cast cannot regain a tag without going through such derivation.

### Sentries and domain crossing
- A **sentry** is a sealed *executable* capability used as a controlled entry point: it
  cannot be jumped into as ordinary data, and executing through it triggers an implicit
  unseal as part of the control-transfer instruction — the newer, lighter-weight
  replacement for the original exception-based `CCall`/`CInvoke` domain-crossing model.
- **Original model (CHERI Oakland 2015)**: `CCall`/`CReturn` pair a sealed code capability
  with a sealed data capability (callee compartment state) to cross domains
  *in-address-space*, without a syscall; originally exception-based (slow), later replaced
  by exception-less `CCallFast`.
- **CHERIoT model**: cross-compartment calls route through a small (**~300-instruction**),
  highly-privileged **switcher** that: unseals the callee's export-table capability;
  clears/zeroes unused argument registers; pushes a return frame onto a **trusted stack**
  (protects state so a corrupted callee still can't break the caller's return); narrows and
  zeroes the caller's stack capability portion handed to the callee; and on return, zeroes
  the stack and unused return registers before restoring caller state.

### Compartmentalization model
- **Library-based (CheriBSD "c18n")**: each dynamically-linked library gets its own
  protection domain — code execution inside a compromised library is confined to what's
  reachable via that library's *static* import/export table, not the whole process.
  Shipping since CheriBSD 22.12.
- **Process-based / "co-processes"**: an experimental CheriBSD branch colocates multiple
  logical UNIX processes in one address space, using CHERI capabilities instead of
  separate page-table contexts, to accelerate IPC/context-switching while preserving
  process integrity/confidentiality/availability — but requires eliminating `fork()` for
  co-process creation and is not in mainline releases.
- **CHERIoT/CompartOS (embedded)**: compartments are the RTOS isolation unit; switches
  piggyback on the register-capability model instead of an MPU/MMU reload.
- The library-vs-process-vs-colocated spectrum is explicitly framed in the literature as a
  security/performance/granularity trade-off surface, not a single right answer
  ("Software Compartmentalization Trade-Offs with Hardware Capabilities," arXiv
  2309.11332).

### Concrete performance numbers
- **Domain-crossing cost**: CHERIoT inter-compartment call ≈ **~400 cycles** (dominated by
  register/stack zeroing for confidentiality); a call to a *shared library* function
  (no compartment crossing) costs only **2–3 extra instructions**. CHERIoT RTOS context
  switch: **+22 cycles** vs a non-CHERI RTOS switch (saving 8 user + 3 kernel capability
  registers). CompartOS: protection-domain crossing **~95% faster than MPU-based IPC**
  and **~26.6–52% faster** than task-based MPU compartmentalization (figures varied across
  extracts; treat as "same order, roughly 2–20x faster than MPU IPC"), **~15% overhead vs
  a fully unprotected system**, with >99.9% of switches "hot" (cheap) and a small tail
  "cold" (cache-miss-heavy). Original 2015 `CCall`/`CReturn`: object-type validation cost
  **~44 cycles (5.5% overhead)**; adding `CClearRegs` register scrubbing cost
  **~172 cycles (21% overhead)** — both far cheaper than the pipe-RPC IPC baseline
  compared against in the same paper.
- For scale: generic process context switches run ~1,000–2,000+ cycles / low
  microseconds, and plain syscalls ~100ns or less — CHERI in-address-space domain
  crossings (tens to low hundreds of cycles) land well below a process context switch and
  are competitive with or cheaper than a syscall.
- **Bounds-check/memory-safety overhead**: Morello SPECint2006, pure-capability code:
  **15.17% geomean** on the initial unmodified FPGA prototype, dropping to **7.72%** after
  working around a data-dependent capability-store exception stall, and **6.28%** after
  also enlarging the store queue — i.e., most of the overhead was a fixable
  microarchitectural artifact of the first-gen prototype, not an inherent tax.
  **CHERIvoke** (temporal safety / use-after-free revocation): **~4.7% average** on SPEC
  CPU2006 at 25% heap-size overhead. **Cornucopia** (concurrent revocation, the
  production-shaped successor): **<2% average, 8.9% worst case** on SPEC CPU2006,
  multicore CHERI FPGA.

### CHERI-RISC-V specifics
- Spec structure: **Zcheri_purecap** is the mandatory base extension; **Zcheri_legacy**,
  **Zcheri_mode**, **Zcheri_pte** are optional (hybrid/legacy-pointer coexistence, mode
  switching, page-table-entry capability semantics).
- Status: actively-maintained **draft** under `riscv/riscv-cheri`, not yet ratified by
  RISC-V International as of this research; an open issue proposes **dropping RV32
  support from the v1 Zcheri standard**, which would push CHERIoT-style 32-bit work
  outside the mainline spec track.
- Silicon/FPGA: **CHERIoT-Ibex** (Microsoft, open-sourced RTL fork of lowRISC's Ibex RV32
  core implementing CHERIoT); the CTSRD/CHERI-RISC-V reference design targets RV64 on
  FPGA (Morello is the flagship, fabbed, Arm-specific — not RISC-V — prototype).
- Encoding: same Concentrate-family shared-exponent/mantissa compression, but the RISC-V
  spec ties mantissa width to XLEN (RV64 gets more mantissa bits / better bounds precision
  than RV32).

### Micro-capabilities for constrained ISAs (§8)
- **CHERIoT** (Microsoft, MICRO'23) is a green-field co-design of a 32-bit compressed
  CHERI ISA extension **with** a purpose-built RTOS, targeting IoT/embedded cost/power/area
  budgets. Deterministic (not probabilistic) full spatial + temporal + inter-compartment
  memory safety, claimed source-compatible with existing embedded C/C++, without breaking
  real-time guarantees — achieved by compressing permissions 16→6 bits, otype to 3 bits,
  fitting the whole capability in 64 bits + tag (vs 128+tag for RV64/Morello).
- No other genuinely distinct micro-capability scheme for constrained ISAs surfaced in
  this research — CHERIoT appears to be the dominant/only mature published design in this
  niche; RISC-V International hosts it as a case study.

### Verdict
**Adapt.** CHERI-RISC-V (full 128-bit) is directly reusable on the RISC-V target, and
CHERIoT-style 64-bit compression is a proven template for anything memory/area-constrained
— but there is no equivalent hardware-capability substrate on mainstream x86/ARM silicon
(Morello is a research prototype, not shipping production hardware). Design the
capability/object model to CHERI's semantics (monotonic derivation, sealed sentries,
tagged provenance) so it runs natively-accelerated on CHERI-RISC-V while falling back to
software-enforced (MMU/MPU + language-level) equivalents on x86/ARM until/unless
capability hardware ships there.

**Sources**: [CHERI Concentrate, IEEE TC 2019](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/2019tc-cheri-concentrate.pdf) ·
[An Introduction to CHERI, UCAM-CL-TR-941](https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-941.pdf) ·
[RISC-V Specification for CHERI Extensions](https://riscv.github.io/riscv-cheri/) ·
[riscv/riscv-cheri GitHub](https://github.com/riscv/riscv-cheri) ·
[riscv-cheri Issue #294 — drop RV32](https://github.com/riscv/riscv-cheri/issues/294) ·
[Arm Architecture Reference Manual Supplement — Morello](https://documentation-service.arm.com/static/61e577e1b691546d37bd38a0) ·
[Morello Prototype Architecture Overview v1.0](https://documentation-service.arm.com/static/62822220f7d9d84d9a3a8c44) ·
[Early performance results from the Morello prototype](https://ctsrd-cheri.github.io/morello-early-performance-results/headline-results/initial-measured-performance.html) ·
[Cornucopia, Oakland 2020](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/2020oakland-cornucopia.pdf) ·
[CHERIvoke, MICRO 2019](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201910micro-cheri-temporal-safety.pdf) ·
[CheriABI, ASPLOS 2019](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201904-asplos-cheriabi.pdf) ·
[CHERI: A Hybrid Capability-System Architecture, Oakland 2015](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201505-oakland2015-cheri-compartmentalization.pdf) ·
[CHERIoT, MICRO 2023](https://dl.acm.org/doi/10.1145/3613424.3614266) ·
[CHERIoT uarch/perf paper](https://cheriot.org/papers/2023-micro-cheriot-uarch.pdf) ·
[CHERIoT: Rethinking security for low-cost embedded systems, MSR-TR-2023-6](https://www.microsoft.com/en-us/research/wp-content/uploads/2023/02/cheriot-63e11a4f1e629.pdf) ·
[What's the smallest variety of CHERI? (MSRC)](https://msrc.microsoft.com/blog/2022/09/whats-the-smallest-variety-of-cheri) ·
[CHERI FAQ](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/cheri-faq.html) ·
[CheriBSD c18n docs](https://ctsrd-cheri.github.io/cheribsd-getting-started/features/c18n.html) ·
[CHERI Software Compartmentalization overview](https://www.cl.cam.ac.uk/research/security/ctsrd/cheri/cheri-compartmentalization.html) ·
[Software Compartmentalization Trade-Offs with Hardware Capabilities, arXiv 2309.11332](https://arxiv.org/pdf/2309.11332) ·
[CompartOS, arXiv 2206.02852](https://arxiv.org/abs/2206.02852) ·
[Efficient Tagged Memory, ICCD 2017](https://www.cl.cam.ac.uk/research/security/ctsrd/pdfs/201711-iccd2017-efficient-tags.pdf) ·
[RISC-V International — CHERIoT: A Study in CHERI](https://riscv.org/blog/2024/08/cheriot-a-study-in-cheri/) ·
[microsoft/cheriot-ibex](https://github.com/Microsoft/cheriot-ibex)

---

## 3. Fuchsia / Zircon — handle-based object capabilities (shipping OS)

### Handles and kernel objects
- A **handle** lets user-mode code reference a kernel object — "a session or connection to
  a particular kernel object." Handles are **process-local** (per-process handle table,
  not a global namespace) and **unforgeable**: a process can't synthesize a valid handle
  value; it's opaque to userspace and only meaningful via kernel-mediated syscalls. Two
  handles can reference the *same* object with *different* rights — rights are a property
  of the handle, not the object.

### Rights (ZX_RIGHT_* bitmask)
- Every handle carries a rights bitmask: `ZX_RIGHT_READ`, `ZX_RIGHT_WRITE`,
  `ZX_RIGHT_DUPLICATE`, `ZX_RIGHT_TRANSFER`, `ZX_RIGHT_WAIT`, `ZX_RIGHT_INSPECT`, plus
  type-specific rights (execute, map, ...). The kernel enforces both object-type
  correctness and rights-sufficiency on every syscall.
- **Monotonic-decrease invariant**: `zx_handle_duplicate()`/`zx_handle_replace()` can only
  produce a handle whose rights are a *subset* of the source's — rights never amplify
  through duplication/transfer, only narrow (e.g. stripping `ZX_RIGHT_WRITE` before
  handing a read-only view to a less-trusted process). `zx_channel_write_etc` similarly
  allows stripping `ZX_RIGHT_TRANSFER` so a receiver can't re-forward what it receives.

### Handle transfer over channels — the only capability-grant mechanism
- `zx_channel_write`/`zx_channel_read` (and `channel_call`) move handles as payload
  between processes; sending a handle **transfers** it out of the sender's table into the
  receiver's. This is explicitly the sole non-bootstrap mechanism for propagating a
  capability between processes.
- **No ambient authority**, stated directly by the project: *"You can only access objects
  that are reachable from the ones you already have access to. There is no ambient
  authority."*
- A process can be started with **zero handles**: `zx_process_start()` is the only way to
  transfer a handle into a process that doesn't already have one to bootstrap with; the
  startup handle can even be `ZX_HANDLE_INVALID`, meaning the process starts with no
  handles and can never acquire any beyond what's explicitly given.

### Process spawn — the C-Space analogue
- `fuchsia.process.Launcher` (commonly wrapped by `fdio_spawn_etc`) creates a process from
  an ELF **plus an explicit set of kernel-object handles**; it sets up the address space
  and sends a startup message with argv, environ, the initial handle set, and the
  process's **namespace** (a table of `absolute-path → handle` mappings).
- Component Framework layers capability **routing** on top: a parent declares exactly
  which capabilities (services, directories, protocols) flow into a child's namespace —
  "when a program is initially created, it does not have the ability to do anything — not
  even to allocate memory" until its creator hands it capabilities. Because every
  namespace is parent-constructed, there is **no global root filesystem**; every component
  effectively has its own private root. This is precisely the "same binary, different
  capability set depending on what's passed at spawn" pattern — the initial handle table
  *is* the process's C-Space, built entirely by the parent/launcher at spawn, with no way
  to later acquire more than what was routed in (short of another process voluntarily
  handing over a handle it already holds via a channel).

### Performance numbers
- Zircon channels are non-blocking, bidirectional, created in connected pairs; reads/writes
  return immediately without waiting on peer state.
- **Cross-kernel IPC benchmark** (x86, intra-core fastpath round trip, via the seL4
  whitepaper and USENIX ATC 2020): **seL4 = 986 cycles, Fiasco.OC = 2,717 cycles,
  Zircon = 8,157 cycles** — Zircon's channel IPC costs roughly **8x seL4's** round trip,
  attributed mainly to domain-switch cost (context save/restore, rights checking) plus
  message copying on the general path (Zircon channels copy small messages rather than
  using a seL4-style register-passed fastpath).

### Verdict
**Adopt the model, not the IPC mechanism.** The handle+rights+channel-transfer model
(unforgeable, process-local, monotonically-narrowable capabilities; zero ambient
authority; capability set fixed entirely at spawn via an explicit initial handle table) is
exactly the right architectural contract for an object-capability kernel and composes
cleanly with MMU/PMP isolation on any of RISC-V/x86/ARM — but its channel-copy IPC path
(~8,157 cycles vs seL4's 986) is not the implementation to copy; use a seL4-style
register-fastpath or shared-buffer channel instead of Zircon's copy-based one.

**Sources**: [Zircon Kernel Concepts](https://fuchsia.dev/fuchsia-src/concepts/kernel/concepts) ·
[Zircon Handles](https://fuchsia.dev/fuchsia-src/concepts/kernel/handles) ·
[Rights | Fuchsia](https://fuchsia.dev/fuchsia-src/concepts/kernel/rights) ·
[Zircon Kernel objects](https://fuchsia.dev/fuchsia-src/reference/kernel_objects/objects) ·
[Process Creation | Fuchsia](https://fuchsia.dev/fuchsia-src/concepts/process/process_creation) ·
[Fuchsia Namespaces](https://fuchsia.dev/fuchsia-src/concepts/process/namespaces) ·
[Software isolation model | Fuchsia](https://fuchsia.dev/fuchsia-src/get-started/learn/intro/sandboxing) ·
[Capabilities | Fuchsia (Component Framework v2)](https://fuchsia.dev/fuchsia-src/concepts/components/v2/capabilities) ·
[Original Principles | Fuchsia](https://fuchsia.dev/fuchsia-src/contribute/contributing-to-cf/original_principles) ·
[zx_process_start](https://fuchsia.dev/reference/syscalls/process_start) ·
[zx_channel_write_etc](https://fuchsia.dev/reference/syscalls/channel_write_etc) ·
[zx_channel_call](https://fuchsia.dev/fuchsia-src/zircon/syscalls/channel_call) ·
[Understanding Fuchsia Security, arXiv 2108.04183](https://arxiv.org/pdf/2108.04183) ·
[seL4 whitepaper](https://sel4.systems/About/seL4-whitepaper.pdf) ·
[Harmonizing Performance and Isolation in Microkernels, USENIX ATC 2020](https://www.usenix.org/system/files/atc20-gu.pdf)

---

## 4. Singularity / Midori — Language-Based OS (LBOS)

### Software-Isolated Processes (SIPs)
- Singularity (Microsoft Research, started 2003) establishes process boundaries via
  **language safety rules and static type checking**, not MMU page-table domains. SIPs can
  run in **ring 0**, sharing an address space, because the *compiler* guarantees no
  unauthorized cross-SIP pointers, no unsafe pointer arithmetic, and no shared mutable
  state outside designated channel structures.
- Kernel and SIPs are implemented mainly in **Sing#**, a type-safe C# extension with
  contract enforcement and no dynamic code loading; MSR describes the kernel as >90%
  verifiably safe code.
- Because SIPs can coexist in the same address space, switching between them need not
  flush the TLB or perform a hardware address-space switch — isolation cost becomes a
  cheaper *software* check instead of a hardware domain crossing.

### The exchange heap and zero-copy IPC
- The **exchange heap** holds objects passed between SIPs. Sing# adds **linear types**: at
  any moment at most one SIP holds a pointer to a given exchange-heap object. Sending a
  message with an exchange-heap pointer **transfers exclusive ownership** — the sender's
  reference is statically invalidated by the type checker, so no copy is needed and no
  cross-SIP aliasing is possible even accidentally. This is compile-time-enforced
  unique/linear ownership, not a runtime check — large buffers move as a single pointer
  plus a static ownership transfer, not a memcpy.

### Contract-based channels
- Channel **contracts** (declared in Sing#) specify legal messages and a named-state
  protocol machine per channel type. The compiler **statically verifies** that send/receive
  sequences never violate the protocol's state ordering — protocol conformance is a
  compile-time proof, not a runtime assertion (formalized/model-checked further in
  follow-up academic work).

### Cost model / numbers
- With no ring transition and (often) no MMU domain crossing for a SIP-to-SIP call, the
  architectural cost collapses toward a plain function call/jump.
- Best available figure: **hardware-based process isolation costs 25–33% overhead** on
  Singularity's benchmark suite vs **under 5% overhead for software isolation** — roughly
  a 5–7x reduction in isolation tax by moving the boundary from hardware to the compiler
  (unverified — re-check the OSR 2007 paper's Table 1 directly for exact
  process-creation/IPC-latency figures on their AMD Athlon 64 3000+ testbed).

### Midori (2008–2015): the industrial follow-up
- Midori (led in part by Joe Duffy, 2009–2014) continued the SIP model but generalized
  deployment: native hardware, Hyper-V guest, or hosted inside a Windows process — beyond
  Singularity's "must be the whole OS."
- Kept and extended exchange-heap/zero-copy design (`SharedData`: ref-counted immutable
  pointer into an OS-kernel-managed cross-process heap, reclaimed at zero refcount);
  "zero-copy" became a fabric-wide philosophy, not just an IPC optimization.
- Made **capability-based security** — object references *as* capabilities, elimination of
  ambient authority — a first-class OS design principle, citing direct lineage from
  **KeyKOS, EROS, and Coyotos** (see §6).
- Duffy's core lesson: the safety-vs-performance dichotomy is false — modern compiler
  technology can drive safety overhead toward zero for most real programs, and safety
  properties (e.g. type-tracked immutability) *enabled* new optimizations (aggressive
  cross-process page sharing) that would have been unsound without them.
- **Cancellation**: no single documented technical cause. Duffy attributes it to
  non-technical, non-purely-business organizational dynamics; Microsoft's official framing
  was a strategic pivot. Duffy's biggest stated regrets: not open-sourcing it from the
  start (denying external peer scrutiny), and not publishing more papers along the way.

### The LBOS trade, generalized
- **Buys**: near-zero-cost domain crossings (IPC ≈ function call, no ring transition, no
  TLB flush), enabling isolation granularity far finer than a hardware-process boundary
  makes practical (one SIP per component/feature, not per-application), plus compile-time
  proofs of protocol/ownership properties no C-level OS gets for free.
- **Requires**: the compiler/runtime become part of the TCB *for isolation itself*, not
  just correctness — any unsound compiler bug or pocket of unsafe code breaks isolation
  for the whole system, not one process. Forces a closed-world/whole-system-recompilation
  model; legacy/unverified native code needs a fallback (hardware isolation or a costly
  SFI shim) it otherwise can't run under.

### Verdict
**Adapt, don't adopt wholesale.** Since this new OS already owns its own compiler, the
exchange-heap-style linear/unique-ownership transfer for zero-copy messages, and
compiler-verified channel-protocol contracts, are high-value low-risk wins to layer onto a
hardware-capability kernel. But running SIPs in ring 0 / one shared address space with *no*
MMU/PMP backstop should be avoided given this project's "never compromise security"
mandate — it makes every isolation guarantee hostage to compiler soundness with no
hardware fallback, precisely the risk Midori's own team never fully de-risked. Prefer
defense in depth: keep hardware address-space/PMP isolation as the enforcement layer, and
use language-based guarantees to make cross-domain calls cheap and eliminate accidental
sharing bugs *within* a domain — not to replace the domain boundary itself.

**Sources**: [Singularity: Rethinking the Software Stack, OSR 2007](https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/osr2007_rethinkingsoftwarestack.pdf) ·
[An Overview of the Singularity Project, MSR-TR-2005-135](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/10/tr-2005-135.pdf) ·
[Deconstructing Process Isolation](https://www.microsoft.com/en-us/research/publication/deconstructing-process-isolation/) ·
[Analyzing Singularity Channel Contracts, ISSTA 2009](https://sites.cs.ucsb.edu/~bultan/publications/issta09.pdf) ·
[CS 261 Notes on Singularity](https://www.read.seas.harvard.edu/~kohler/class/cs261-f11/singularity.html) ·
[Joe Duffy — Blogging about Midori](https://joeduffyblog.com/2015/11/03/blogging-about-midori/) ·
[Joe Duffy — Objects as Secure Capabilities](https://joeduffyblog.com/2015/11/10/objects-as-secure-capabilities/) ·
[Joe Duffy — A Tale of Three Safeties](https://joeduffyblog.com/2015/11/03/a-tale-of-three-safeties/) ·
[Midori (operating system) — Wikipedia](https://en.wikipedia.org/wiki/Midori_(operating_system))

---

## 5. Unikernels — MirageOS, Unikraft

### The model
- A unikernel merges low-level OS code and application code into a **single kernel,
  single address space** image: no process/user-kernel split, no VM separation of OS vs
  app. MirageOS "does not contain any process management, neither virtual memory — the
  entire unikernel is executed in single address space."
- **Compile-time specialization**: applications are compile-time-specialized into
  standalone kernels, sealed against modification — you link exactly the libraries the app
  needs, producing a single deployable VM image (originally Xen; later KVM/Firecracker/
  Solo5/bare metal).
- **Memory safety substitutes for hardware isolation**: since there's no MMU boundary
  between "kernel" and "app" inside the image, MirageOS leans on OCaml's type/memory
  safety as the substitute — without it, a bug in one library could access all memory of
  every other library in the image. **Unikraft** is mostly C (for perf/compatibility) and
  is explicit that this reintroduces memory-safety risk vs MirageOS; it is exploring
  safe-language components (Rust network stack, Dafny-verified scheduler) to trade
  security vs performance per-component.

### Attack surface reduction
- MirageOS: link only the libraries an app needs → "at least an order-of-magnitude
  reduction in code size and a correspondingly much smaller attack surface"; a concrete
  example: an HTTPS unikernel service at **4% of the LOC** of an equivalent Unix-based
  service, with attack surface reduced roughly two orders of magnitude.
- Structural, not incidental: a unikernel image cannot exec a shell or spawn a second
  process — there is no process abstraction, so whatever isn't statically linked in does
  not exist in the image.
- Unikraft's Kconfig-gated micro-libraries (network stack, libc, drivers, scheduler) are
  independently selected; unused components are compiled out entirely, not merely disabled
  at runtime, so the shipped binary carries no dead/unreachable driver code.

### Zero-copy NIC-to-application datapath
- **MirageOS is not fully zero-copy on Xen**: on the netfront/netback path, both transmit
  and receive require a full copy of packet data to/from a shared grant-table page — the
  classic Xen copy, not true zero-copy. MirageOS's TCP/IP stack is pure OCaml, decoupled
  from transport via a module signature, so the same app code runs over Xen netfront,
  Solo5 (KVM/hvt, muen, virtio), or Unix sockets — portability was prioritized over
  datapath zero-copy.
- **Unikraft's `uknetdev`** decouples the device-driver side from the network-stack/app
  side specifically to support cross-platform driver reuse, and "leaves memory management
  to the application, all the while supporting... zero-copy I/O and packet batching." Even
  here, zero-copy-with-refcounting is not supported for drivers that modify the packet for
  transmission (e.g. virtio-net) — true zero-copy is mainly achieved on DPDK-class polling
  paths; the default KVM config uses standard virtio-net + tap/vhost-net, with a
  higher-performance option offloading the datapath to vhost-user (DPDK-based, host
  userspace) at the cost of host-side polling.

### Modular micro-library vs single-language purism
- **Unikraft**: pluggable C-ish micro-libraries (musl, lwIP, etc.), each with its own
  Makefile + Kconfig, composed per app — unmodified POSIX-ish C/C++ apps can often be
  linked with comparatively little porting.
- **MirageOS**: single-language, clean-slate philosophy — TCP/IP, TLS, filesystem, device
  drivers all reimplemented from scratch in OCaml as composable functors, avoiding a C
  POSIX layer to get whole-stack type safety. Produces "very lean images with great
  performance and small boot times," but porting effort is large and largely repeated per
  application/language, and general-workload throughput trails Unikraft.

### Boot time and throughput numbers
- **Unikraft**: guest-only boot (QEMU/Solo5, excluding VMM startup) is tens to hundreds of
  microseconds; on Firecracker, guest-side boot doesn't exceed ~1ms, full boot-to-ready
  (incl. VMM) in the 3–40ms range depending on platform. Unikraft Cloud production cold
  starts: ~4ms for early instances, rising to ~14ms at the 5,000th concurrent VM.
- Comparative figures from the EuroSys'21 paper (unverified — re-check primary PDF):
  MirageOS ~1–2ms on Solo5; OSv ~4–5ms on Firecracker; Rump ~14–15ms on Solo5; HermiTux
  ~30–32ms on uHyve; Lupine ~70ms on Firecracker.
- Edge-orchestration comparison: Unikraft boot 232.25ms vs Docker 977.5ms (~4x faster,
  though an order of magnitude slower than bare Unikraft-on-KVM, reflecting a heavier
  edge-orchestration harness).
- **Throughput**: nginx/SQLite/Redis on Unikraft show **1.7x–2.7x** improvement over
  equivalent Linux guests; images ~1MB, <10MB RAM to run; network throughput in the
  **10–40 Gb/s** range depending on config/NIC path.

### When right vs wrong
- **Right**: single-purpose network appliances/middleboxes (firewalls, DNS, load
  balancers, VPN endpoints — MirageOS's original target); serverless/FaaS where cold-start
  latency dominates and each invocation is naturally single-tenant-per-VM; embedded/edge
  nodes with tight RAM/flash and a fixed workload; trusted single-tenant workloads where
  the hypervisor, not the guest, is the real isolation boundary.
- **Wrong**: general-purpose multi-tenant systems — a unikernel has **no intra-image
  isolation** ("due to the use of a single unprotected address space, there is no
  isolation guarantee within a unikernel itself"); a memory-safety bug in the app can
  corrupt/leak across what would be a hard boundary in a normal OS (real enough that
  Intel-MPK-based intra-unikernel isolation mitigations exist as their own research line).
  Also wrong for workloads needing POSIX fidelity, dynamic loading, or many concurrent
  untrusted processes on one image — MirageOS sacrifices POSIX/mainstream-app
  compatibility outright for its safety story.

### Verdict
**Adapt, don't adopt.** The single-address-space/no-isolation deployment model is wrong
for a general-purpose multi-tenant OS and should be rejected outright — but steal three
mechanisms as build-time/runtime techniques *within* a properly isolated (paged,
capability-checked) kernel: (1) Unikraft's Kconfig-style compile-time module selection to
produce minimal, specialized images per deployment target without shipping dead driver
code; (2) the `uknetdev`-style decoupled zero-copy datapath (driver↔stack separation,
app-owned buffers, optional polling mode) as the NIC-to-userspace fast path, gated behind
the capability system rather than replacing it; (3) MirageOS's bet that a memory/type-safe
implementation language shrinks the *trusted* code without losing isolation — use that
safety as defense-in-depth inside each isolation domain, not as a substitute for
hardware/MMU isolation between domains.

**Sources**: [Unikernels: Library Operating Systems for the Cloud, ASPLOS'13](https://anil.recoil.org/papers/2013-asplos-mirage.pdf) ·
[Unikernels: Rise of the Virtual Library OS — ACM Queue](https://queue.acm.org/detail.cfm?id=2566628) ·
[Unikraft: Fast, Specialized Unikernels the Easy Way, EuroSys'21](https://arxiv.org/pdf/2104.12721) ·
[Unikraft EuroSys'21 artifacts](https://github.com/unikraft/eurosys21-artifacts) ·
[Unikraft — Performance docs](https://unikraft.org/docs/concepts/performance) ·
[Unikraft — Architecture docs](https://unikraft.org/docs/internals/architecture) ·
[Unikraft — Security docs](https://unikraft.org/docs/concepts/security) ·
[Unikraft ASPLOS'22 Tutorial — High Performance Applications](https://asplos22.unikraft.org/high-performance/) ·
[Unikraft meets DPDK](https://static.sched.com/hosted_files/dpdkna2019/b6/Unikraft_dpdk_NA.pdf) ·
[Unikraft and the Coming of Age of Unikernels — USENIX ;login:](https://www.usenix.org/publications/loginonline/unikraft-and-coming-age-unikernels) ·
[Networking in MirageOS, TUM NET 2019-06-1](https://www.net.in.tum.de/fileadmin/TUM/NET/NET-2019-06-1/NET-2019-06-1_10.pdf) ·
[MirageOS operator manual](https://mirage.github.io/operator-handbook/index.html) ·
[Size matters: how Mirage got smaller and less magical](https://mirage.io/blog/mirage-3-smaller) ·
[The Dark Side of Unikernels for Machine Learning, arXiv 2004.13081](https://arxiv.org/pdf/2004.13081) ·
[Intra-Unikernel Isolation with Intel MPK, VEE'20](https://www.ssrg.ece.vt.edu/papers/vee20-mpk.pdf) ·
[Are Unikernels Ready for Serverless on the Edge?, arXiv 2403.00515](https://arxiv.org/html/2403.00515v1) ·
[How Unikraft Cloud reduces serverless cold starts to milliseconds](https://shivangsnewsletter.com/p/how-unikraft-cloud-reduces-serverless) ·
[Exploring the Viability of Unikernels for ARM-powered Edge Computing, arXiv 2412.03030](https://arxiv.org/pdf/2412.03030) ·
[Shrinking the Kernel Attack Surface, arXiv 2510.03720](https://arxiv.org/html/2510.03720v1) ·
[unikernel.org — NFV Platforms with MirageOS](http://unikernel.org/blog/2016/unikernel-nfv-platform)

---

## 6. KeyKOS / EROS / Coyotos — the classic OCap lineage

*(Kept tight per scope — feeds a sibling agent's revocation deep-dive.)*

### KeyKOS: orthogonal persistence via checkpointing
- KeyKOS (Key Logic, production since 1983 on IBM System/370 hosting Tymnet, later ported
  to 680x0/88x00) achieves **orthogonal persistence** through whole-system checkpointing:
  all processes are briefly frozen, a fast in-memory sweep finds dirty pages, processes
  resume immediately, dirty pages are written to disk asynchronously *after* resume (no
  I/O during the freeze). Individual **page journaling** supplements checkpoints for
  higher-frequency durability. Consequence: no save/load file model — process/object state
  is simply always there across reboots/crashes. Nanokernel: ~20,000 lines of C, as little
  as 100KB, includes capability + checkpoint + VM logic in-kernel.

### Confinement
- KeyKOS/EROS implement Norm Hardy's **confinement property**: a subsystem can be given
  capabilities to do work while being provably prevented from leaking information through
  capabilities it wasn't explicitly granted. Enforced via a factory/constructor pattern —
  KeyKOS's **factory** and EROS's **constructor** build a confined subsystem from a
  "program" capability plus a "cargo" capability, certifying the built instance holds no
  capability it wasn't explicitly given.

### Revocation lineage
- Both implement revocation through **indirection** (Redell's classic technique): a
  revocable capability points through an indirection object; revoking flips/destroys the
  indirection, invalidating all downstream capabilities in one operation without walking
  every holder.
- EROS: "a subject that created a given e-capability referencing an object is in a
  position to revoke the access permissions granted by every e-capability referencing this
  object" — revocation scoped to a lineage rooted at the creator, a conceptual precursor to
  seL4's CDT (seL4 makes lineage a first-class, walkable kernel structure instead of an
  indirection-object convention).
- **Coyotos** (Shapiro's planned EROS successor, halted before completion) refined the
  model with first-class **endpoints**, a redesigned process object, and **GPTs (Guarded
  Page Tables)** generalizing memory-mapping capabilities, allowing persistence to be
  expressed uniformly in terms of pages (EROS/KeyKOS required separate node/page
  allocation on disk). Per Shapiro's own notes, the EROS→Coyotos changes were "conceptually
  minor and not particularly controversial." Motivation for the transition: "very
  challenging security issues... intrinsic to any system architecture based on synchronous
  IPC primitives (notably including EROS and L4)" were discovered — a notable parallel
  since seL4 also uses synchronous IPC and had to separately address
  denial-of-service/covert-channel concerns via its own confinement/integrity proofs.

### Performance and why it never shipped widely
- EROS's "Measured Performance of a Fast Local IPC" (1996) reports IPC cost approaching
  "the cost of raw memory copy plus a small overhead" on a 400MHz Pentium II, roughly
  matching L4-class IPC performance of that era (exact cycle table not confirmed — treat
  as directional).
- EROS was always a research system (Penn → Johns Hopkins → The EROS Group LLC), funded by
  DARPA/AFRL; prototyped a trusted window system, a hardened network stack, an early
  secure-browser effort — never productized. Development halted in 2005 in favor of two
  successor lines, **CapROS** (community continuation) and **Coyotos** (Shapiro's
  redesign, itself never completed) — small-team research funding ran out before either
  reached production maturity. This is the direct historical ancestor of seL4's team's
  decision to invest in machine-checked proof rather than an informal security argument:
  EROS-style "trust the design, verify by testing/argument" never produced a deployable,
  certifiable artifact.

### Verdict
**Adapt the ideas, not the artifacts.** Confinement-via-constructor and
indirection-based revocation are conceptually sound and directly inform seL4's CDT
(already adopted, §1) and CHERI's revocation thinking (Cornucopia/CHERIvoke use a
shadow-bitmap sweep, a distant cousin of indirection-based bulk revocation) — but
KeyKOS's checkpoint-everything orthogonal persistence is a heavyweight,
single-machine-image assumption that conflicts with a modern multi-core/multi-ISA,
crash-isolated design. Treat it as a design lesson (revocation must be O(1)-ish and
lineage-aware) rather than a subsystem to port.

**Sources**: [The KeyKOS Nanokernel Architecture](https://css.csail.mit.edu/6.566/2018/readings/keykos.pdf) ·
[The Checkpoint Mechanism in KeyKOS](http://cap-lore.com/CapTheory/upenn/Checkpoint.html) ·
[KeyKOS — A Secure, High-Performance Environment for S/370](http://cap-lore.com/CapTheory/upenn/Key370/Key370.html) ·
[Verifying the EROS Confinement Mechanism](https://flint.cs.yale.edu/cs428/doc/eros-verify.pdf) ·
[EROS: A Fast Capability System, SOSP '99](https://flint.cs.yale.edu/cs428/doc/eros.pdf) ·
[EROS (microkernel) — Wikipedia](https://en.wikipedia.org/wiki/EROS_(microkernel)) ·
[Coyotos Microkernel Specification](https://hydra-www.ietfng.org/capbib/cache/shapiro:coyotosspec.html) ·
[Differences Between Coyotos and EROS](http://www.cap-lore.com/CapTheory/KK/Shap/eros-comparison.html) ·
[The Measured Performance of a Fast Local IPC (1996)](https://www.researchgate.net/publication/3670759_The_measured_performance_of_a_fast_local_IPC)

---

## Synthesis: a three-path hybrid capability architecture

The six systems above converge on one architectural fact: **every mature capability OS
separates the capability *abstraction* (unforgeable reference + monotonically-narrowable
rights + explicit, no-ambient-authority delegation) from the *enforcement mechanism*
(what actually stops a violation).** seL4 and Fuchsia enforce in a software kernel backed
by the MMU. CHERI enforces in hardware, in-address-space, via tagged registers. Singularity/
Midori enforce via the compiler, with no hardware boundary at all. KeyKOS/EROS/Coyotos
pioneered the abstraction itself, before any of today's enforcement substrates existed.

A new OS that (a) owns its own compiler, (b) must run well on RISC-V, x86, and ARM, and
(c) refuses to trade security for performance should **not pick one enforcement
mechanism** — it should define **one capability abstraction with three interchangeable
enforcement backends**, selected per-architecture at build/boot time, never visible to
application code above the ABI boundary.

### The one abstraction (borrowed mostly from seL4 + Fuchsia)
- A capability is: **(object reference, rights mask, badge/type tag)** — unforgeable,
  held in a per-domain capability space (seL4's CSpace / Fuchsia's handle table), never
  directly addressable by the holder.
- Rights only ever **narrow** on delegation (seL4 Copy/Mint, Zircon
  duplicate/replace, CHERI CSetBounds/CAndPerm — all three ecosystems independently
  converged on strict monotonicity; this is not a stylistic choice, it's the property that
  makes revocation and confinement tractable to reason about, formally or informally).
- Provenance is tracked (seL4's CDT is the fullest expression of this — adopt it as the
  cross-cutting revocation substrate regardless of which enforcement backend is active for
  a given domain).
- A process/domain's capability set is fixed **entirely at spawn** (Fuchsia's
  Launcher-constructed initial handle table / namespace) — "same binary, different
  capabilities" is a first-class deployment primitive, not a bolt-on sandboxing feature.

### The three enforcement backends behind that one abstraction

| Backend | When active | What enforces the boundary | Domain-crossing cost | Source system |
|---|---|---|---|---|
| **Hardware-capability (CHERI)** | CHERI-RISC-V targets | Tagged 128-bit fat pointers + CSeal/sentries, checked by the CPU on every load/store/jump | Tens–low hundreds of cycles (CHERIoT ~400 cyc/call; CompartOS 2–20x faster than MPU IPC) | CHERI, CHERIoT |
| **Language-capability (compiler-verified)** | Any target, for code the OS's own compiler compiled and can prove safe (kernel-adjacent services, same-vendor userland) | Type/ownership/linearity proofs at compile time — no runtime check at the boundary at all | ≈ direct call/jump (Singularity: <5% overhead vs 25–33% for hardware isolation) | Singularity/Midori |
| **MMU/PMP-capability (page-table)** | x86, ARM, and any RISC-V core without CHERI | Page tables / PMP regions switched on domain crossing, gated by the seL4-style CSpace/CDT capability check | ~600–1,000+ cycles (seL4 fastpath: ~600–986 cyc x86; contrast Zircon's un-optimized ~8,157 cyc — proves the backend can be made nearly as cheap as CHERI if the fastpath is disciplined) | seL4, Fuchsia/Zircon |

### Why this is coherent, not three unrelated systems bolted together
- **The capability struct is backend-agnostic.** Whether "narrow the rights and derive a
  child capability" is implemented as a CHERI `CSetBounds` instruction, a compile-time
  linear-type check that erases to nothing at runtime, or a seL4-style CNode `Mint` that
  installs a new page-table mapping, the *caller-visible* operation and its rights algebra
  are identical. Application/service code written against the capability API does not know
  or care which backend is under it — this is what "same OS runs securely on commodity x86
  and blazing-fast on CHERI-RISC-V with the same API" requires structurally.
- **Revocation is unified through the CDT**, regardless of backend: CHERI capabilities get
  swept via a Cornucopia-style concurrent revocation pass; MMU-backed capabilities get
  swept via seL4-style CDT walk + page-table unmap; language-backed capabilities get
  revoked by the compiler simply refusing to link/load code that still references a freed
  linear handle. All three are different *implementations* of "walk the CDT from this node
  and invalidate everything derived from it."
- **Fallback direction is fixed, not symmetric**: CHERI-RISC-V is the performance ceiling
  (hardware-checked, near-zero-overhead compartmentalization); compiler-verified is the
  zero-overhead ceiling for code this OS's own toolchain fully owns and can prove safe;
  MMU/PMP is the universal floor every architecture has. A domain's backend is chosen by
  what's available and how much of its code is compiler-verified — untrusted or
  dynamically-loaded code always gets MMU (or CHERI, where present) enforcement; only
  code built and proven by this OS's own compiler is eligible for the zero-check
  language-capability path, and even then only as an additional inner layer on top of an
  outer hardware boundary (per the Midori-cancellation lesson in §4: never let language
  proof be the *only* backstop for a security-critical boundary).
- **Confinement and persistence lessons (§6) apply uniformly**: the
  factory/constructor-style confinement check ("this subsystem holds no capability it
  wasn't explicitly given") is a build-time/spawn-time audit independent of backend, and
  should gate every domain's initial capability set the same way regardless of whether
  that domain ends up CHERI-, MMU-, or language-enforced.
- **Unikernel-style specialization (§5) becomes the build-time knob**, not a separate OS
  mode: a deployment target (embedded RISC-V node vs. general x86 server) selects, at
  compile time, which backend each domain gets and which modules are linked in at all —
  giving unikernel-grade attack-surface reduction and zero-copy datapaths (Unikraft's
  `uknetdev` pattern) as a *configuration* of the one kernel, not a fork of it.

### Net recommendation
Build the capability kernel around seL4's CSpace/CDT/Retype-from-Untyped object model as
the reference semantics (it's the only one of the six with a machine-checked proof, and
its semantics are backend-neutral enough to retarget). Implement three backends against
that same semantics: a CHERI-RISC-V backend that lowers capability operations directly to
CHERI instructions (near-zero-cost, use aggressively wherever CHERI silicon/FPGA is
present); an MMU/PMP backend for x86/ARM/non-CHERI RISC-V that ports seL4's fastpath
discipline (not Zircon's copy-heavy channel design) to hit sub-1,000-cycle domain
crossings; and an optional compiler-verified fast lane, in the Midori sense, for
same-toolchain code, always nested *inside* one of the other two boundaries rather than
replacing it. Revocation, confinement auditing, and capability delegation semantics are
defined once, at the CDT level, and compiled down to whichever backend a given domain
runs under.
