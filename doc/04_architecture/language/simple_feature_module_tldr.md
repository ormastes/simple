# Simple Feature Module (SFM) — Architecture TLDR

`.sfm` is a pure-Simple outer container over opaque SMF code units (no new SMF
section). `SFM1` carries one SMF; `SFM2` kind `aspect_pack` carries a bounded,
uncompressed directory plus independently framed SMFs for selected-module-only
loading. The manifest remains the MDSOC+ capsule boundary.

## Core Shape
- `SFM1`: unchanged 16-byte header + manifest + one opaque SMF.
- `SFM2 aspect_pack`: 28-byte header + manifest + directory + opaque SMF frames.
- Metadata is validated up front; only the selected frame is integrity-checked
  and optionally decompressed before reuse of the existing SMF reader.
- Profiles: native | loader | script | web | mobile (loader reports which handled it).
- VERSION → embedded SemVer, retrievable at runtime.

<!-- sdn-diagram:id=simple_feature_module_tldr.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module_tldr.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm -> manifest
sfm -> opaque_smf
manifest -> di
di -> authz
loader -> profile
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module_tldr.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Full: [simple_feature_module.md](simple_feature_module.md) · Design: [../../05_design/simple_feature_module.md](../../05_design/simple_feature_module.md)
</content>
