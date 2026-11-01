# HIR-variant object keys (lane generic-rr-hir-variant-obj)

> One target-neutral HIR (a list of `HirCfgDeclV1`) is projected per MIR target: plain `@cfg` items and numbered cfg groups (with an else arm) select the kept declarations, which seal a per-target `variant_digest`. The object key, RR partition, RR producer and sidecar path all derive from that projection, so a windows-only edit moves only the windows key.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# HIR-variant object keys (lane generic-rr-hir-variant-obj)

One target-neutral HIR (a list of `HirCfgDeclV1`) is projected per MIR target: plain `@cfg` items and numbered cfg groups (with an else arm) select the kept declarations, which seal a per-target `variant_digest`. The object key, RR partition, RR producer and sidecar path all derive from that projection, so a windows-only edit moves only the windows key.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Requirements | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009) |
| Plan | doc/03_plan/sys_test/generic_rr_hir_variant_obj.md |
| Design | doc/05_design/generic_rr_hir_variant_obj.md |
| Research | doc/01_research/local/generic_rr_hir_variant_obj.md |
| Source | `test/01_unit/compiler/driver/hir_variant_object_key_spec.spl` |
| Updated | 2026-11-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

One target-neutral HIR (a list of `HirCfgDeclV1`) is projected per MIR
target: plain `@cfg` items and numbered cfg groups (with an else arm) select
the kept declarations, which seal a per-target `variant_digest`. The object
key, RR partition, RR producer and sidecar path all derive from that
projection, so a windows-only edit moves only the windows key.

Evidence: Rust-seed interpreter runs only (attributed to the seed); no self-hosted
binary exists on the authoring host. Owner: hir_variant_object_key_v1.spl.

## Scenarios

### HIR variant projection

#### keeps the linux arms only for the linux target (REQ-GRR-005, REQ-GRR-009)

- Project the shared decl list for x86_64-linux (REQ-GRR-005, REQ-GRR-009)
   - Expected: p.ok is true
   - Expected: p.error equals ``
   - Expected: p.kept equals `["fn:a", "fn:l", "fn:g_else"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project the shared decl list for x86_64-linux (REQ-GRR-005, REQ-GRR-009)")
val p = proj(decls(), linux())
expect(p.ok).to_equal(true)
expect(p.error).to_equal("")
expect(p.kept).to_equal(["fn:a", "fn:l", "fn:g_else"])
```

</details>

#### keeps the windows arms only for the windows target (REQ-GRR-005, REQ-GRR-009)

- Project the shared decl list for x86_64-windows (REQ-GRR-005, REQ-GRR-009)
   - Expected: p.ok is true
   - Expected: p.kept equals `["fn:a", "fn:w", "fn:g_win"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project the shared decl list for x86_64-windows (REQ-GRR-005, REQ-GRR-009)")
val p = proj(decls(), windows())
expect(p.ok).to_equal(true)
expect(p.kept).to_equal(["fn:a", "fn:w", "fn:g_win"])
```

</details>

#### variant digests differ per target and are stable (REQ-GRR-009)

- Project twice per target and compare digests (REQ-GRR-009)
   - Expected: l1.len() equals `64`
   - Expected: l1 == w1 is false
   - Expected: proj(decls(), linux()).variant_digest equals `l1`
   - Expected: proj(decls(), windows()).variant_digest equals `w1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project twice per target and compare digests (REQ-GRR-009)")
val l1 = proj(decls(), linux()).variant_digest
val w1 = proj(decls(), windows()).variant_digest
expect(l1.len()).to_equal(64)
expect(l1 == w1).to_equal(false)
expect(proj(decls(), linux()).variant_digest).to_equal(l1)
expect(proj(decls(), windows()).variant_digest).to_equal(w1)
```

</details>

#### a windows-only edit changes only the windows digest (REQ-GRR-005)

- Edit w's content digest and reproject both targets (REQ-GRR-005)
   - Expected: proj(edited, linux()).variant_digest equals `proj(decls(), linux()).variant_digest`
   - Expected: proj(edited, windows()).variant_digest == proj(decls(), windows()).variant_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit w's content digest and reproject both targets (REQ-GRR-005)")
val edited = decls_with("w-v2", "a-v1")
expect(proj(edited, linux()).variant_digest).to_equal(proj(decls(), linux()).variant_digest)
expect(proj(edited, windows()).variant_digest == proj(decls(), windows()).variant_digest).to_equal(false)
```

</details>

#### a shared edit changes both digests (REQ-GRR-005)

- Edit a's content digest and reproject both targets (REQ-GRR-005)
   - Expected: proj(edited, linux()).variant_digest == proj(decls(), linux()).variant_digest is false
   - Expected: proj(edited, windows()).variant_digest == proj(decls(), windows()).variant_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Edit a's content digest and reproject both targets (REQ-GRR-005)")
val edited = decls_with("w-v1", "a-v2")
expect(proj(edited, linux()).variant_digest == proj(decls(), linux()).variant_digest).to_equal(false)
expect(proj(edited, windows()).variant_digest == proj(decls(), windows()).variant_digest).to_equal(false)
```

</details>

#### a group with no matching arm and no else arm drops every arm

- Project a group whose only arm is aarch64 on x86_64
   - Expected: p.ok is true
   - Expected: p.kept equals `["fn:a"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a group whose only arm is aarch64 on x86_64")
val p = proj([d("a", [], 0, 0, "a-v1"), d("g_arm", ["aarch64"], 3, 0, "g_arm-v1")], linux())
expect(p.ok).to_equal(true)
expect(p.kept).to_equal(["fn:a"])
```

</details>

### HIR variant projection: fail-closed inputs

#### rejects a malformed cfg condition

- Project a decl whose cfg is the incomplete atom os =
   - Expected: p.ok is false
   - Expected: p.error equals `malformed_cfg`
   - Expected: p.variant_digest equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a decl whose cfg is the incomplete atom os =")
val p = proj([d("bad", ["os ="], 0, 0, "bad-v1")], linux())
expect(p.ok).to_equal(false)
expect(p.error).to_equal("malformed_cfg")
expect(p.variant_digest).to_equal("")
```

</details>

#### rejects an invalid content digest

- Project a decl whose content digest is not 64-hex
   - Expected: p.ok is false
   - Expected: p.error equals `invalid_decl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a decl whose content digest is not 64-hex")
val p = proj([HirCfgDeclV1(name: "x", kind: "fn", cfg: [], cfg_group: 0, cfg_arm: 0,
    content_digest: "zz")], linux())
expect(p.ok).to_equal(false)
expect(p.error).to_equal("invalid_decl")
```

</details>

#### rejects a numbered group arm with an empty cfg

- Project a group whose numbered arm has no condition
   - Expected: p.ok is false
   - Expected: p.error equals `malformed_cfg_group`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a group whose numbered arm has no condition")
val p = proj([d("g0", [], 5, 0, "g0-v1"), d("g1", ["linux"], 5, 1, "g1-v1")], linux())
expect(p.ok).to_equal(false)
expect(p.error).to_equal("malformed_cfg_group")
```

</details>

#### rejects two records of one group arm that disagree on the condition

- Project a group whose arm 0 is declared with two different conditions
   - Expected: p.ok is false
   - Expected: p.error equals `malformed_cfg_group`
   - Expected: agree.ok is true
   - Expected: agree.kept equals `["fn:z"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Project a group whose arm 0 is declared with two different conditions")
val p = proj([d("x", ["windows"], 6, 0, "x-v1"), d("y", ["linux"], 6, 0, "y-v1"),
    d("z", [], 6, -1, "z-v1")], linux())
expect(p.ok).to_equal(false)
expect(p.error).to_equal("malformed_cfg_group")
val agree = proj([d("x", ["windows"], 6, 0, "x-v1"), d("y", ["windows"], 6, 0, "y-v1"),
    d("z", [], 6, -1, "z-v1")], linux())
expect(agree.ok).to_equal(true)
expect(agree.kept).to_equal(["fn:z"])
```

</details>

#### seals build-context inputs that are not part of the target id (REQ-GRR-009)

- Change features and collection policy and compare variant digests (REQ-GRR-009)
   - Expected: with_feature.target_id equals `base.target_id`
   - Expected: with_feature.variant_digest == base.variant_digest is false
   - Expected: hir_variant_projection_v1(decls(), linux(), ["simd"]).variant_digest equals `with_feature.variant_digest`
   - Expected: with_policy.target_id equals `base.target_id`
   - Expected: with_policy.variant_digest == base.variant_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Change features and collection policy and compare variant digests (REQ-GRR-009)")
val base = hir_variant_projection_v1(decls(), linux(), [])
val with_feature = hir_variant_projection_v1(decls(), linux(), ["simd"])
expect(with_feature.target_id).to_equal(base.target_id)
expect(with_feature.variant_digest == base.variant_digest).to_equal(false)
expect(hir_variant_projection_v1(decls(), linux(), ["simd"]).variant_digest).to_equal(with_feature.variant_digest)
val strict = MirTargetContext(arch: "x86_64", os: "linux", abi: "gnu", backend: "llvm",
    collection_policy: "strict", version: 1)
val with_policy = hir_variant_projection_v1(decls(), strict, [])
expect(with_policy.target_id).to_equal(base.target_id)
expect(with_policy.variant_digest == base.variant_digest).to_equal(false)
```

</details>

### HIR variant object key, partition, producer and sidecar

#### formats the target id

- Format the linux and windows target ids
   - Expected: hir_variant_target_id_v1(linux()) equals `x86_64-linux-gnu-llvm/debug/baseline`
   - Expected: hir_variant_target_id_v1(windows()) equals `x86_64-windows-msvc-llvm/debug/baseline`
   - Expected: proj(decls(), linux()).target_id equals `x86_64-linux-gnu-llvm/debug/baseline`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Format the linux and windows target ids")
expect(hir_variant_target_id_v1(linux())).to_equal("x86_64-linux-gnu-llvm/debug/baseline")
expect(hir_variant_target_id_v1(windows())).to_equal("x86_64-windows-msvc-llvm/debug/baseline")
expect(proj(decls(), linux()).target_id).to_equal("x86_64-linux-gnu-llvm/debug/baseline")
```

</details>

#### separates sub-arch variants of one arch (REQ-GRR-009)

- Derive ids and keys for armv7 and thumbv7em contexts sharing arch arm (REQ-GRR-009)
   - Expected: hir_variant_target_id_v1(armv7) equals `arm.armv7-none-eabi-llvm/debug/baseline`
   - Expected: hir_variant_target_id_v1(thumb) equals `arm.thumbv7em-none-eabi-llvm/debug/baseline`
   - Expected: pa.ok is true
   - Expected: pt.ok is true
   - Expected: pa.variant_digest == pt.variant_digest is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive ids and keys for armv7 and thumbv7em contexts sharing arch arm (REQ-GRR-009)")
val armv7 = MirTargetContext(arch: "arm", os: "none", abi: "eabi", backend: "llvm",
    subarch: "armv7", version: 1)
val thumb = MirTargetContext(arch: "arm", os: "none", abi: "eabi", backend: "llvm",
    subarch: "thumbv7em", version: 1)
expect(hir_variant_target_id_v1(armv7)).to_equal("arm.armv7-none-eabi-llvm/debug/baseline")
expect(hir_variant_target_id_v1(thumb)).to_equal("arm.thumbv7em-none-eabi-llvm/debug/baseline")
val pa = proj(decls(), armv7)
val pt = proj(decls(), thumb)
expect(pa.ok).to_equal(true)
expect(pt.ok).to_equal(true)
expect(pa.variant_digest == pt.variant_digest).to_equal(false)
expect(hir_variant_object_key_v1("pkg_v.main", pa, "tc") ==
    hir_variant_object_key_v1("pkg_v.main", pt, "tc")).to_equal(false)
expect(hir_variant_object_sidecar_path_v1("q", "pkg_v.main", pa.target_id) ==
    hir_variant_object_sidecar_path_v1("q", "pkg_v.main", pt.target_id)).to_equal(false)
```

</details>

#### derives one object key per target and is deterministic (REQ-GRR-009)

- Key the same module for linux and windows twice (REQ-GRR-009)
   - Expected: kl.len() equals `64`
   - Expected: kl == kw is false
   - Expected: hir_variant_object_key_v1(MODULE, proj(decls(), linux()), TOOLCHAIN) equals `kl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Key the same module for linux and windows twice (REQ-GRR-009)")
val kl = hir_variant_object_key_v1(MODULE, proj(decls(), linux()), TOOLCHAIN)
val kw = hir_variant_object_key_v1(MODULE, proj(decls(), windows()), TOOLCHAIN)
expect(kl.len()).to_equal(64)
expect(kl == kw).to_equal(false)
expect(hir_variant_object_key_v1(MODULE, proj(decls(), linux()), TOOLCHAIN)).to_equal(kl)
```

</details>

#### returns an empty key for a bad projection, module path or toolchain

- Key a not-ok projection, an empty module path and an empty toolchain
   - Expected: hir_variant_object_key_v1(MODULE, bad, TOOLCHAIN) equals ``
   - Expected: hir_variant_object_key_v1("", proj(decls(), linux()), TOOLCHAIN) equals ``
   - Expected: hir_variant_object_key_v1(MODULE, proj(decls(), linux()), "") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Key a not-ok projection, an empty module path and an empty toolchain")
val bad = proj([d("bad", ["os ="], 0, 0, "bad-v1")], linux())
expect(hir_variant_object_key_v1(MODULE, bad, TOOLCHAIN)).to_equal("")
expect(hir_variant_object_key_v1("", proj(decls(), linux()), TOOLCHAIN)).to_equal("")
expect(hir_variant_object_key_v1(MODULE, proj(decls(), linux()), "")).to_equal("")
```

</details>

#### appends the target id to the RR partition (REQ-GRR-005)

- Derive the linux partition and a not-ok partition (REQ-GRR-005)
   - Expected: hir_variant_object_partition_v1("p", p) equals `"p@" + p.target_id`
   - Expected: hir_variant_object_partition_v1("p", p) equals `p@x86_64-linux-gnu-llvm/debug/baseline`
   - Expected: hir_variant_object_partition_v1("p", proj([d("bad", ["os ="], 0, 0, "b")], linux())) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the linux partition and a not-ok partition (REQ-GRR-005)")
val p = proj(decls(), linux())
expect(hir_variant_object_partition_v1("p", p)).to_equal("p@" + p.target_id)
expect(hir_variant_object_partition_v1("p", p)).to_equal("p@x86_64-linux-gnu-llvm/debug/baseline")
expect(hir_variant_object_partition_v1("p", proj([d("bad", ["os ="], 0, 0, "b")], linux()))).to_equal("")
```

</details>

#### builds an obj.emit RR producer keyed by the variant digest (REQ-GRR-005)

- Derive the RR producer for the windows projection (REQ-GRR-005)
   - Expected: producer.kind equals `obj.emit`
   - Expected: producer.stable_entity_id equals `MODULE`
   - Expected: producer.semantic_profile_digest equals `digest("profile")`
   - Expected: producer.parameter_digest equals `p.variant_digest`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Derive the RR producer for the windows projection (REQ-GRR-005)")
val p = proj(decls(), windows())
val producer = hir_variant_object_producer_v1(MODULE, digest("profile"), p)
expect(producer.kind).to_equal("obj.emit")
expect(producer.stable_entity_id).to_equal(MODULE)
expect(producer.semantic_profile_digest).to_equal(digest("profile"))
expect(producer.parameter_digest).to_equal(p.variant_digest)
```

</details>

#### keeps the legacy sidecar path for an empty target id and splits per target

- Compare legacy and per-target sidecar paths
   - Expected: legacy equals `build/q/" + sha256_text(MODULE) + ".object`
   - Expected: tl == legacy is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compare legacy and per-target sidecar paths")
val legacy = hir_variant_object_sidecar_path_v1("build/q", MODULE, "")
expect(legacy).to_equal("build/q/" + sha256_text(MODULE) + ".object")
val tl = hir_variant_object_sidecar_path_v1("build/q", MODULE, "x86_64-linux-gnu-llvm/debug/baseline")
expect(tl == legacy).to_equal(false)
expect(tl).to_start_with("build/q/")
expect(tl).to_end_with(".object")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md (REQ-GRR-001..009)`
- **Plan:** `doc/03_plan/sys_test/generic_rr_hir_variant_obj.md`
- **Design:** `doc/05_design/generic_rr_hir_variant_obj.md`
- **Research:** `doc/01_research/local/generic_rr_hir_variant_obj.md`


</details>
