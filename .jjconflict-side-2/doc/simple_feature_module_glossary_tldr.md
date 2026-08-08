# SFM Glossary — TLDR

`.sfm` = pure-Simple container that **embeds opaque SMF** + a feature manifest.
Manifest declares **layers** (front-end UI: gui/tui/arg-parser; back-end: DB/HW),
each wired by **DI** (`register_layers`/`resolve_layer`) and gated by an **AOP**
authz interceptor against **SfmSecurityLevel** (Ordinary vs Trusted). The
**loader** picks a **profile** (native/loader/script/web/mobile). **VERSION.md**
supplies the embedded SemVer.

<!-- sdn-diagram:id=simple_feature_module_glossary_tldr.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=simple_feature_module_glossary_tldr.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

sfm -> manifest
sfm -> opaque_smf
manifest -> layer
layer -> di
di -> authz
authz -> security_level
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=simple_feature_module_glossary_tldr.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

Full glossary: [simple_feature_module_glossary.md](simple_feature_module_glossary.md)
</content>
