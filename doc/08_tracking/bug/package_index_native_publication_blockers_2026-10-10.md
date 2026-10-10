# Native package index publication blockers (2026-10-10)

Status: OPEN. Item 6 native fixture builds but does not publish its first V1 generation.

## Reproduction

In the isolated release worktree at commit `ddb1507c8eb`, the pure-Simple Stage 2 candidate `c535be7321e80a4857413fa1c690008b3172b157e87eac8a860edd98c6772082` passed parent sanity/provenance. Build `test/fixtures/compiler/package_index_publish_cas_native_probe.spl` with LLVM, `--runtime-bundle core-c-bootstrap --source src/compiler --source src/lib --entry-closure --threads 1`, then run it. The build links 40 objects without the earlier declaration-only-module error; the executable exits 1 on initial publication. Logs: `build/mini_builds/item6_semantic_action_probe_llvm_{objectless,diagnostic,explicit_fields}_20261010/`.

## Findings

1. The eight-argument `PackageModuleIndexGenerationV1` constructor did not yield an admitted V1 value in this native probe. Validation returned `legacy-variant-unexpected` although its trailing `variant_digest` and `scope_entry_source_identity` fields declare empty-string defaults. Explicitly passing both empty strings changed validation to `ok`. The production V1 admission constructor and V2 warm route constructors now pass all fields explicitly. The compiler-level default-field cause remains unisolated.
2. With explicit fields, publication still returns false. It creates a 260-byte `.index` file named `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.index`, the SHA-256 of empty input. The file's actual SHA-256 is `7873e9ab9f880d9b0c675bdd487e4fee2997af0bc4b7921c8371f6bcd8f2eeba`. The probe's `sha256_text("producer")` and `sha256_text("inventory")` also yield the empty-input digest. The failing native hash boundary may be UTF-8 conversion, the accelerator, or its call/return path; this evidence does not isolate it. The publisher correctly refuses to advance `CURRENT`.

## Next action

Isolate `sha256_text` on nonempty literals and runtime-built text under the same native backend, fix the owner of the empty-input result, then rerun the CAS fixture. Add a minimal default-field native regression before removing the explicit constructor arguments. Run production cold/warm cohorts only after publication and readback pass. No further probe retry was made after the third verify/fix cycle in this session.

## 2026-10-10 follow-up

A separate six-module native probe isolated the empty-input digest to `text_to_utf8_bytes` returning zero bytes for nonempty text. The sanctioned facade now falls back to `byte_at` only on that invalid result, and its focused native SHA probe passes. This does not revalidate the full CAS fixture; the publisher and runtime ABI owner remain open. See [native text conversion](native_text_to_bytes_empty_2026-10-10.md).
