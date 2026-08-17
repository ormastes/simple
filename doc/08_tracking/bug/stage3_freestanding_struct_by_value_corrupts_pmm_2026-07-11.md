# Stage3 Freestanding Struct-by-Value Corrupts PMM

**Status (2026-07-17):** Likely fixed by commits `ca1e18c1744a` and `7c30ce49d04f` per triage evidence (see note below).

The stage3 Cranelift x86_64 freestanding build passed `PhysMemManager` by value
to `_bitmap_clear`. The callee read a corrupted `bitmap_addr` and repeatedly
wrote to address `-122`, producing recovered page faults instead of initializing
the PMM bitmap.

The PMM hot path now passes the scalar bitmap address across helper boundaries;
compatibility wrappers remain for existing callers. The compiler needs an ABI
regression covering a four-field `u64` struct passed by value between modules
and must either lower it correctly or reject the build.

A later production run proved the corruption also occurs when the aggregate is
an unused parameter: `vmm_init(pmm_get_manager(), 0)` entered VMM but failed in
its first `_alloc_table_page`, even though `vmm_init` never reads the manager.
The production desktop now calls scalar-only
`vmm_init_from_global_pmm(hhdm_offset)`. The compatibility API delegates to the
same body for callers built with a correct aggregate ABI.

The defect also affects enum payloads. Stage3 lowered `pmm_alloc_page()` as a
`PageFrame?` that passed `rt_is_some`, while `rt_enum_payload` returned zero;
VMM then trapped on the nil `PageFrame` payload. `pmm_alloc_page_raw()` now
owns scalar bitmap allocation directly, and VMM table allocation consumes that
raw physical address. This removed a 578 KB repeated-fault serial storm.

Direct QEMU boot also cannot safely parse module-global Limine request structs
and optional response payloads under this ABI. The direct production desktop
therefore uses `arch_x86_64_direct_boot_init()`, which retains fault-hook,
per-CPU, CPUID-topology, and syscall initialization without pretending the
multiboot wrapper supplied Limine aggregates.

## Triage note (2026-07-17)

Commits `ca1e18c1744a` and `7c30ce49d04f` likely address the aggregate ABI and enum-payload defects described above. The workarounds (scalar-only APIs, direct-boot path) are confirmed in production use. Pending runtime verification: fresh stage3 freestanding build must compile and boot with zero PMM/VMM faults.

---

## Triage re-verification 2026-08-17 (c_mir lane, classified by CONTENT not SHA)

**Governing fact for every 50.mir-attributed row:** nothing runnable on this
host executes `src/compiler/50.mir/**.spl`. `bin/simple` resolves to
`bin/release/x86_64-unknown-linux-gnu/simple` (59536728 bytes, mtime
2026-08-16 22:59), whose own `--version` banner states it is a Rust
**bootstrap seed**; it has its own Rust MIR/JIT/native pipeline and never reads
`src/compiler/**.spl` for compilation logic. `bin/release/simple` is the
2181-byte refusing production-guard wrapper, and no stage2/stage3 self-hosted
binary exists under `build/bootstrap/`. Therefore any evidence in this doc
phrased as "reproduced on `bin/simple`" is evidence about the **seed**, not
about 50.mir, and the runtime claim here can only be closed by a full
self-hosted bootstrap (not run: the user's bootstrap is live and
`build/bootstrap/**` is off-limits). Rows were therefore classified by
grepping current source.

**Verdict: MIS-ATTRIBUTED — no 50.mir claim to verify; runtime claim UNVERIFIED.**

This doc names no 50.mir function; all repairs it cites are OS-side scalar APIs
(`pmm_alloc_page_raw`, `vmm_init_from_global_pmm`,
`arch_x86_64_direct_boot_init`). Grepping
`src/compiler/50.mir/_MirLowering/function_lowering.spl` for aggregate/byval/sret
ABI lowering yields only comment lines 81 and 282 — no aggregate-ABI fix exists
there. The 2026-07-17 triage note's pending freestanding boot verification is
unchanged.

---

## Not re-measured 2026-08-17 (W4 bug-fixing wave)

The 2026-07-17 triage note's pending item is unchanged and was not dischargeable
here: it requires a fresh stage-3 *freestanding* build that compiles and boots
under QEMU with zero PMM/VMM faults. That needs a stage-binary rebuild (the
staged binaries in this checkout are pre-fix artifacts — 169 `call 0` sites each,
measured 2026-08-17) plus a QEMU boot lane, both out of scope for this wave.

Left **OPEN, unverified**. Note for the next lane: the workarounds this doc
describes (`pmm_alloc_page_raw`, `vmm_init_from_global_pmm`,
`arch_x86_64_direct_boot_init`) are scalar-only APIs that deliberately AVOID the
aggregate ABI, so a green boot through those paths does **not** verify the
aggregate ABI fix. The acceptance test must pass a four-field `u64` struct by
value across a module boundary directly, as this doc's own "Required Fix"
paragraph asks — including the unused-parameter case, which is the variant that
was proven to corrupt even when the callee never reads the aggregate.
