# Simple Feature Module (SFM) Glossary

Terms for the `.sfm` feature-module format. TLDR: [simple_feature_module_glossary_tldr.md](simple_feature_module_glossary_tldr.md).

<!-- sdn-diagram:id=simple_feature_module_glossary.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module_glossary.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm_container -> feature_manifest
sfm_container -> embedded_smf
feature_manifest -> layer
feature_manifest -> security_level
layer -> di_resolve
di_resolve -> aop_authz
aop_authz -> security_level
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module_glossary.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

## SFM (Simple Feature Module)
The primary feature-module format. A `.sfm` is a pure-Simple outer container that embeds an existing SMF binary as an opaque code payload and adds a feature manifest on top.

## `.sfm`
The file extension and byte container. Layout (little-endian): `"SFM1"` magic + version (u16 major, u16 minor) + manifest_len (u32) + smf_len (u32) + manifest_blob + opaque SMF blob (final segment, never re-encoded).

## SMF (and the embed relationship)
The existing Simple Module Format binary. SFM **embeds** SMF rather than adding an SMF section, because SMF's section codec is Rust-owned (`section.rs`) and a new section type would force a forbidden seed/bootstrap rebuild. The reader hands the opaque SMF bytes to the existing `SmfReaderImpl`/`SmfGetter` loader unchanged.

## Feature manifest
The declarative header (`FeatureManifest`) listing the module's exposed layers, name, version, and security level. Encoded ahead of the SMF blob.

## Layer (front-end / back-end)
A `LayerDescriptor` (name, `LayerKind`, entry symbol) exposed by the module. Front-end = UI (gui | tui | arg-parser); back-end = DB | HW.

## LayerKind
Enum of layer roles wired to wire bytes: `FrontGui`, `FrontTui`, `FrontArgParser`, `BackDb`, `BackHw`.

## DI / resolve-by-role
`register_layers`/`resolve_layer` (`di_bridge.spl`) wire manifest layers into the existing DI container data-driven from the manifest (no hard-coded wiring). Resolution is `Any`-keyed (typed resolve is disabled in the DI lib).

## AOP authorization
An AOP Around interceptor (`authz.spl`, on `src/lib/nogc_sync_mut/src/aop.spl`) that gates layer access against the module's `SfmSecurityLevel`: unauthorized access is denied, authorized proceeds.

## SfmSecurityLevel (Ordinary / Trusted)
The privilege marker. `Ordinary` is the default; `Trusted` is the special privileged level required to expose/access privileged layers. An ordinary SFM cannot claim Trusted without the manifest marker.

## Profile
The target the loader (`loader.spl`) selects to handle a module: native | loader | script | web | mobile. The loader reports which profile handled the module. (Mobile is a thin load-and-report shim.)

## VERSION.md wiring
Repo-root `VERSION.md` (first non-comment line is the SemVer). `std.sfm.version.read_version_md` reads it at build time; the built `.sfm`/app embeds the version, retrievable at runtime (e.g. the Help/Info menu).
