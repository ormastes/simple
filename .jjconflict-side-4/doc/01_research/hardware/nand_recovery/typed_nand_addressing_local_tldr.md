# Typed NAND addressing (TL;DR)

Proposes `Nd*` newtype structs (channel/way/bank/plane/block/wordline/page;
`ctypes.spl` shape: 1-field struct + `impl`, field `idx` not `val` —
reserved) to replace raw `i64` address math. Found **23 address-arithmetic
sites**; the block/page split is independently reimplemented **4×**
(`nvme_types` canonical, `rain.spl`, raw in `ftl.spl:442/466`, raw again in
`fil_nand_emu.spl:78-85`) — that drift is the bug class this prevents (cf. the
already-fixed S-profile fold collision, `geometry.spl:101-108`,
"291 & 527 = 3"). Only channel/block/page are LIVE today; way/bank/plane/
wordline are declared-but-decorative or unmodeled — ship those 3 first, land
the rest only when a real caller (8-way board, v2 MLC/plane, wordline STRAW)
exists. Placement: new peer leaf beside `nvme_types.spl`/`rel_types.spl`
(both ban `impl`, both sit below `fil`), NOT folded in. Migration: adapters
at 5 ranked seams, not a rewrite; FW↔emu conversion lands at the existing
`fil_nand_emu.spl` fold functions. Full doc: §1 convention, §2 sites, §3
topology + `rel_*` keying, §4 types + placement + migration + honest costs.

<!-- sdn-diagram:id=nd_dimension_hierarchy -->
```
SSD-controller (fw/, multi-chip)    single chip (nand_emu/, Ne*)
 NdChannel[LIVE:rain]                NdPlane [datasheet-only, v2]
  └NdWay[declared,decorative]         └NdBlock[LIVE:ppn_block]
    └NdBank[not modeled]                └NdWordline[v2 STRAW gap]
                                            └NdPage[LIVE:ppn_page]
SLC v1: NdWordline==NdPage numerically but stays distinct — MLC/TLC v2 packs
2-3 NdPage/NdWordline; an alias breaks silently at v2. keying: rel_vref/
rel_wear->block | rel_disturb(STRAW)->block(v1)/wordline(v2) | RAIN->channel
```
