# Item 5 Stage4 strip policy in link-profile identity

Status: focused native PASS; full Stage4 release-small qualification OPEN.

The Stage4 link-profile input previously recorded debug, PIE, bare-metal, optimization level, duplicate-definition policy, and compiler fallback policy, but omitted `strip_output`. Stripped and unstripped native images could therefore share the same profile hash even though their output bytes and measured size differ.

The production link path now derives its canonical options text from `stage4_link_profile_options_v1`, which includes `strip_output`. A focused unit case checks that the resulting profile inputs differ when only the strip choice changes. A no-stub admitted pure-Simple Stage 2 native probe built with `--entry-closure --backend cranelift --runtime-bundle core-c-bootstrap`, linked two objects, and exited 0. Compiler SHA-256: `e0e5a6cd522d6ee86b0dbb8e7cdd88cad21b3daa39d18b65b2ce163867e0eb06`. Log: `build/mini_builds/item5_stage4_strip_profile_native_probe_20261011.log`. The probe binary is 27,280 bytes; it is not a release-small hello measurement.

This binds one link-affecting option to receipt identity. It does not prove `RuntimeFeatureClosureV1`, first-demand provider loading, a full Stage4 CLI, matched C size, or startup/RSS cohorts.
