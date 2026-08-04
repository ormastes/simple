# Simple Feature Module (SFM) — Design TLDR

`SFM1` remains a 16-byte header + manifest + one opaque SMF. `SFM2` kind
`aspect_pack` is a 28-byte header + canonical manifest + bounded uncompressed
directory + independently framed opaque SMFs. Directory metadata is validated
without opening frames; only the selected frame is integrity-checked and
optionally decompressed before the existing SMF reader receives it. DI/AOP and
VERSION wiring remain unchanged.

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
