# Simple Feature Module (SFM) — Detailed Design

Detailed design of the `.sfm` codec, manifest encoding, DI/AOP/security-level
flow, and VERSION.md build wiring. Architecture: [../04_architecture/simple_feature_module.md](../04_architecture/simple_feature_module.md).

<!-- sdn-diagram:id=simple_feature_module.design -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module.design hash=sha256:auto render=ascii
@layout dag
@direction LR

build_version -> encode_sfm
encode_manifest -> encode_sfm
embed_smf -> encode_sfm
encode_sfm -> sfm_file
sfm_file -> decode_sfm
decode_sfm -> manifest_model
decode_sfm -> smf_getter
manifest_model -> register_layers
register_layers -> resolve_layer
resolve_layer -> authz_around
authz_around -> security_level
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module.design hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Container codec (`codec.spl`)
Little-endian, write-then-read symmetric. Header (16 bytes): `"SFM1"` magic,
`ver_major`/`ver_minor` u16, `manifest_len` u32, `smf_len` u32. Then the manifest
blob, then the opaque SMF blob (`smf_len` bytes). The decoder validates magic and
bounds (`SFM_HEADER_BYTES + manifest_len + smf_len <= total`), then slices the SMF
blob without parsing it. Helpers: `push_u16_le`/`push_u32_le`/`push_str`,
`read_u16_le`/`read_u32_le`/`read_str`.

## Manifest encoding (`manifest.spl`)
`name_str | version_str | security_level u8 | layer_count u32 | layers[...]`.
Strings are u32-length-prefixed UTF-8 (arbitrary bytes safe). Each layer encodes
name + entry symbol (length-prefixed) + `LayerKind` byte (FrontGui=0, FrontTui=1,
FrontArgParser=2, BackDb=3, BackHw=other). `SfmSecurityLevel`: Ordinary=0, Trusted=1.

## DI / AOP / security-level flow
`register_layers` walks the manifest and registers each layer into the existing
DI container keyed by `Any` (typed resolve disabled in the DI lib). `resolve_layer`
returns the registered layer. Access is intercepted by an AOP **Around** aspect
(`authz.spl`): it reads the module's `SfmSecurityLevel` and denies privileged-layer
access unless the module is `Trusted`; authorized access proceeds. An Ordinary
module cannot self-grant Trusted — the marker lives in the signed manifest.

## VERSION.md build wiring
`std.sfm.version.read_version_md` reads repo-root `VERSION.md` (first non-comment
line = SemVer) at build time. `encode_sfm` stamps it into the manifest `version`
field, so the built `.sfm`/app can surface it at runtime (e.g. Help/Info menu).
</content>
