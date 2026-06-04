# Simple Feature Module (SFM) — Architecture

SFM (`.sfm`) is the primary feature-module format: a **pure-Simple outer container**
that embeds an existing SMF binary as an opaque code payload and adds a feature
manifest on top. Fits MDSOC+: the manifest is the capsule boundary (exposed
layers + capabilities + security level); the embedded SMF is the code unit.

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
- **manifest.spl** — `FeatureManifest`, `LayerDescriptor`, `LayerKind`, `SfmSecurityLevel`, `SfmHeader`.
- **di_bridge.spl** — `register_layers`/`resolve_layer` over the existing DI container (`src/lib/nogc_sync_mut/src/di.spl`), data-driven from the manifest, `Any`-keyed.
- **authz.spl** — AOP Around interceptor (on `src/lib/nogc_sync_mut/src/aop.spl`) enforcing `SfmSecurityLevel`.
- **loader.spl** — parses container, selects + reports the target profile, hands SMF bytes to `SmfReaderImpl`/`SmfGetter`.
- **version.spl** — reads repo-root `VERSION.md` at build time; embeds the SemVer.

## Byte layout (all little-endian)
`"SFM1"(4) | ver_major u16 | ver_minor u16 | manifest_len u32 | smf_len u32 | manifest_blob | opaque SMF blob`.
The SMF blob is the final segment and is never re-encoded. The reader parses
front-to-back (`SFM_HEADER_BYTES = 16`) and never reaches into the SMF payload.

## Profiles
The loader selects one of **native | loader | script | web | mobile** to handle
the module and reports which handled it. Mobile is a thin load-and-report shim;
app-store packaging is out of scope.

## Integration points
- SMF loader (`SmfReaderImpl`/`SmfGetter`) — reused unchanged, no new SMF section.
- DI container and AOP lib — reused; SFM only adds the manifest-driven wiring + authz aspect.
- Public reuse surface: `std.sfm` (`sfm_load`/`sfm_resolve`, manifest model, `register_layers`/`resolve_layer`, authz). Samples in `src/app/sfm_samples/`.
</content>
