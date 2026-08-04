# Simple Feature Module (SFM) — Architecture

SFM (`.sfm`) is the primary feature-module format: a **pure-Simple outer
container** over opaque SMF code units. `SFM1` contains one SMF image. `SFM2`
kind `aspect_pack` contains a bounded directory and independently framed SMF
images so a loader can open only the selected module. Neither form changes the
SMF format. The feature manifest remains the MDSOC+ capsule boundary.

<!-- sdn-diagram:id=simple_feature_module.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

codec -> manifest
codec -> embedded_smf
manifest -> di_bridge
di_bridge -> container
di_bridge -> authz
authz -> aop
loader -> codec
loader -> smf_getter
loader -> profile
version -> manifest
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## Components (`src/lib/nogc_sync_mut/sfm/`)
- **codec.spl** — encodes/decodes the `.sfm` container; treats SMF bytes as opaque.
- **aspect_pack.spl** — owns the `SFM2` aspect-pack header, bounded directory,
  per-frame metadata, and selected-frame integrity validation.
- **manifest.spl** — `FeatureManifest`, `LayerDescriptor`, `LayerKind`, `SfmSecurityLevel`, `SfmHeader`.
- **di_bridge.spl** — `register_layers`/`resolve_layer` over the existing DI container (`src/lib/nogc_sync_mut/src/di.spl`), data-driven from the manifest, `Any`-keyed.
- **authz.spl** — AOP Around interceptor (on `src/lib/nogc_sync_mut/src/aop.spl`) enforcing `SfmSecurityLevel`.
- **loader.spl** — parses container, selects + reports the target profile, hands SMF bytes to `SmfReaderImpl`/`SmfGetter`.
- **version.spl** — reads repo-root `VERSION` at build time; embeds the SemVer.

## Byte layouts (all little-endian)

- Ordinary module (`SFM1`, unchanged): `magic | version | manifest_len |
  smf_len | manifest_blob | opaque SMF`.
- Aspect pack (`SFM2`, kind `aspect_pack`): `magic | version | kind | flags |
  manifest_len | entry_count | directory_len | payload_len | manifest_blob |
  directory | independently framed opaque SMFs`.

The uncompressed `SFM2` directory maps canonical module IDs to contiguous
payload-relative frames and records compression, decoded size, dictionary ID,
and stored-content integrity metadata. Header and directory validation rejects
unsupported versions/kinds, duplicate IDs, gaps, overlap, aliases, trailing
bytes, and configured size/count limits without opening a payload. Only the
selected frame is copied, integrity-checked, and (when required) decompressed.

## Profiles
The loader selects one of **native | loader | script | web | mobile** to handle
the module and reports which handled it. Mobile is a thin load-and-report shim;
app-store packaging is out of scope.

## Integration points
- SMF loader (`SmfReaderImpl`/`SmfGetter`) — reused unchanged, no new SMF
  section. `AspectPackProvider` adapts one selected frame to the existing object
  provider/reader boundary; it is not a second loader.
- DI container and AOP lib — reused; SFM only adds the manifest-driven wiring + authz aspect.
- Public reuse surface: `std.sfm` (`sfm_load`/`sfm_resolve`, manifest model, `register_layers`/`resolve_layer`, authz). Samples in `src/app/sfm_samples/`.
</content>
