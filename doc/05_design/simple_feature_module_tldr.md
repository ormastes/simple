# Simple Feature Module (SFM) — Design TLDR

`.sfm` codec is symmetric little-endian: 16-byte header (`"SFM1"`, ver u16×2,
manifest_len u32, smf_len u32) + manifest blob + **opaque SMF blob** (sliced, not
parsed). Manifest = name/version strings (u32-len UTF-8) + security_level u8 +
layer_count u32 + layers (name, entry, `LayerKind` byte). DI registers layers
from the manifest (`Any`-keyed); an AOP Around authz aspect gates Trusted layers.
`VERSION.md`'s SemVer is stamped into the manifest at build time.

<!-- sdn-diagram:id=simple_feature_module_tldr.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module_tldr.design hash=sha256:auto render=ascii
@layout dag
@direction LR

version -> encode
manifest -> encode
smf -> encode
encode -> decode
decode -> di
di -> authz
authz -> security_level
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module_tldr.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Full: [simple_feature_module.md](simple_feature_module.md) · Arch: [../04_architecture/language/simple_feature_module.md](../04_architecture/language/simple_feature_module.md)
</content>
