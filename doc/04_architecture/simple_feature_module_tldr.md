# Simple Feature Module (SFM) — Architecture TLDR

`.sfm` is a pure-Simple container that **embeds opaque SMF bytes** + a feature
manifest (no new SMF section → no seed rebuild). The manifest is the MDSOC+
capsule boundary: exposed **layers** + **SfmSecurityLevel**. **DI** wires layers
data-driven from the manifest; an **AOP** authz aspect gates Trusted layers. The
**loader** picks a profile and hands SMF to the existing `SmfGetter`.

## Core Shape
- Layout (LE): `"SFM1" | ver(u16,u16) | manifest_len u32 | smf_len u32 | manifest | opaque SMF`.
- SMF blob is last and never re-encoded; header is 16 bytes.
- Profiles: native | loader | script | web | mobile (loader reports which handled it).
- VERSION.md → embedded SemVer, retrievable at runtime.

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

Full: [simple_feature_module.md](simple_feature_module.md) · Design: [../05_design/simple_feature_module.md](../05_design/simple_feature_module.md)
</content>
