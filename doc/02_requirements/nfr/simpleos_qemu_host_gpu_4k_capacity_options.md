<!-- codex-research -->
# SimpleOS QEMU Host-GPU 4K Capacity — NFR Options

Select one target set subject to the compatibility matrix below.

| NFR option | Compatible feature options |
|---|---|
| N1 | F1, F2 |
| N2 | F1, F2 |
| N3 | F3 only |

## Option N1 — Current-production 4K bound (recommended)

**Description:** Require exact 3840x2160 ARGB, complete checksum before scanout,
strict overflow/capacity rejection, no crop/downscale, and all three guest ISAs.
Native prepared-host warm render/readback target remains <=16.7 ms; incremental
daemon plus shared-region RSS remains <=256 MiB. TCG is correctness-only.

**Pros:** Matches the production desktop and existing NFRs; preserves honest
native performance and cross-ISA classification.

**Cons:** Demands strong native hardware evidence that TODO 548 currently blocks;
the latency target may require later profiling/optimization.

**Effort:** M evidence work across approximately 6–9 test/doc surfaces.

## Option N2 — Relaxed 4K bring-up bound

**Description:** Require exact 3840x2160 correctness and <=33.3 ms warm native
render/readback on prepared Linux hosts for x86_64, AArch64, and RISC-V guests,
with <=256 MiB incremental RSS. Keep all security and fallback requirements
unchanged; TCG is correctness-only.

**Pros:** Easier first production bring-up while retaining exact pixels and
bounded memory.

**Cons:** Does not meet a 60 Hz frame budget; likely creates a second performance
upgrade phase.

**Effort:** S–M evidence work across approximately 5–7 surfaces.

## Option N3 — Low-memory tiled bound

**Description:** Keep the shared arena at 8 MiB and cap incremental RSS at
128 MiB for x86_64, AArch64, and RISC-V guests; accept <=100 ms native
whole-frame latency while requiring exact final checksum and zero scanout writes
before complete validation. TCG is correctness-only.

**Pros:** Strongest memory ceiling and smallest BAR footprint.

**Cons:** Performance is unsuitable for interactive production; verification
and recovery complexity are much higher despite the lower memory bound.

**Effort:** L–XL evidence work across approximately 10–15 surfaces.
