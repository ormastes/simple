# Simple Feature Module (SFM) — Detailed Design

Detailed design of the `.sfm` codec, manifest encoding, DI/AOP/security-level
flow, and VERSION.md build wiring. Architecture: [../04_architecture/language/simple_feature_module.md](../04_architecture/language/simple_feature_module.md).

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

## Container codecs (`codec.spl`, `aspect_pack.spl`)

`SFM1` remains write/read symmetric and unchanged: a 16-byte header, canonical
manifest blob, then one opaque SMF image.

`SFM2` major 2, minor 0, kind `aspect_pack` has a 28-byte header followed by the
same canonical `FeatureManifest`, an uncompressed directory, and a payload
area. Every directory entry contains canonical `module_id` and `aspect_id`,
compression mode (`None` or `Zstd`), payload-relative offset, stored and decoded
sizes, dictionary ID, and stored-content hash. Entries and frames are unique,
ordered, contiguous, and independently decompressible. The decoder validates
all structural metadata and limits up front, but validates/copies only the
selected stored frame. The provider then performs bounded decompression and
requires the exact declared decoded length before giving bytes to the existing
SMF reader. Dictionary ID zero is the initial supported profile.

Malformed metadata fails closed with `E-APACK001`; integrity failures use
`E-APACK002`; absent module IDs use `E-APACK003`; configured resource limits use
`E-APACK004`. The stored-content hash is a corruption guard, not pack
authentication; catalog signature/trust policy remains a distinct owner.

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
module cannot self-grant Trusted — the marker lives in the manifest.

## VERSION.md build wiring
`std.sfm.version.read_version_md` reads repo-root `VERSION.md` (first non-comment
line = SemVer) at build time. `encode_sfm` stamps it into the manifest `version`
field, so the built `.sfm`/app can surface it at runtime (e.g. Help/Info menu).
</content>
