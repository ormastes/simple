# Native package index publication blockers (2026-10-10)

Status: OPEN. The first V1 generation now publishes; the native fixture stops at second-generation action-digest validation.

## Reproduction

In the isolated release worktree at commit `ddb1507c8eb`, the pure-Simple Stage 2 candidate `c535be7321e80a4857413fa1c690008b3172b157e87eac8a860edd98c6772082` passed parent sanity/provenance. Build `test/fixtures/compiler/package_index_publish_cas_native_probe.spl` with LLVM, `--runtime-bundle core-c-bootstrap --source src/compiler --source src/lib --entry-closure --threads 1`, then run it. The build links 40 objects without the earlier declaration-only-module error; the executable exits 1 on initial publication. Logs: `build/mini_builds/item6_semantic_action_probe_llvm_{objectless,diagnostic,explicit_fields}_20261010/`.

## Findings

1. The eight-argument `PackageModuleIndexGenerationV1` constructor did not yield an admitted V1 value in this native probe. Validation returned `legacy-variant-unexpected` although its trailing `variant_digest` and `scope_entry_source_identity` fields declare empty-string defaults. Explicitly passing both empty strings changed validation to `ok`. The production V1 admission constructor and V2 warm route constructors now pass all fields explicitly. The compiler-level default-field cause remains unisolated.
2. With explicit fields, publication still returns false. It creates a 260-byte `.index` file named `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855.index`, the SHA-256 of empty input. The file's actual SHA-256 is `7873e9ab9f880d9b0c675bdd487e4fee2997af0bc4b7921c8371f6bcd8f2eeba`. The probe's `sha256_text("producer")` and `sha256_text("inventory")` also yield the empty-input digest. The failing native hash boundary may be UTF-8 conversion, the accelerator, or its call/return path; this evidence does not isolate it. The publisher correctly refuses to advance `CURRENT`.

## Next action

Isolate `sha256_text` on nonempty literals and runtime-built text under the same native backend, fix the owner of the empty-input result, then rerun the CAS fixture. Add a minimal default-field native regression before removing the explicit constructor arguments. Run production cold/warm cohorts only after publication and readback pass. No further probe retry was made after the third verify/fix cycle in this session.

## 2026-10-10 follow-up

A separate six-module native probe isolated the empty-input digest to `text_to_utf8_bytes` returning zero bytes for nonempty text. The sanctioned facade now falls back to `byte_at` only on that invalid result, and its focused native SHA probe passes. This does not revalidate the full CAS fixture; the publisher and runtime ABI owner remain open. See [native text conversion](native_text_to_bytes_empty_2026-10-10.md).

## 2026-10-10 transition pointer follow-up

With the guarded text-to-bytes repair, the same no-stub LLVM/core-C fixture generated a correctly named index but failed before publishing CURRENT. A focused 43-module native probe returned `atomic=false exclusive=true` for `file_atomic_write` and `file_create_exclusive` in the same directory. The transition pointer was the failing atomic-write caller. `_transition_point_v1` now stages through the existing exclusive-create facade and renames over TRANSITION under CURRENT.lock, verifying a stale staged file or already-published pointer before accepting it. The next full native fixture created both TRANSITION=none and CURRENT on its first publish.

Build receipt: `build/mini_builds/item6_cas_after_transition_20261010/` (build exit 0, 50 HIR modules, 40 linked objects; run exit 11). The fixture returns 11 when a second-generation graph fails `package_module_index_validate_v1` after assigning its semantic v2 action digest. It does not reach second publish, load, or CAS pin. The exact validation reason is not emitted by this fixture, so it remains unisolated. This was the third bounded verify/fix cycle for this defect; no further retry was made. The lower-level atomic-write failure is tracked separately in [native atomic write](native_file_atomic_write_false_2026-10-10.md).

## 2026-10-10 second-generation isolation

With the admitted pure-Simple Stage 2 candidate SHA-256 `865f63091a88219c99e49cf61e963481d348c9f9d3ca0dc93c34b40844f64d0d`, a failure-only fixture diagnostic identified `action-input-binding-mismatch:module` at exit 11. A second diagnostic proved the fixture's `var edited = entry; edited.source_digest = ...` changed `entry.source_digest` and `graph.entries[0].source_digest` to the edited hash as well. The graph variant stayed unchanged. The fixture now constructs independent entries for its negative control and semantic action, avoiding the native copy-then-mutate alias. A matching production route pattern in `package_index_route.spl` now constructs its snapshot-path entry explicitly rather than mutating a copied indexed entry; a unit assertion pins the indexed source identity.

The corrected no-stub LLVM/core-C fixture builds 50 modules, publishes the second V2 generation, and advances CURRENT; run exit is now 4 at native readback. The pointed-to 917-byte index has the exact CURRENT SHA-256, one canonical count row, and one complete 14-field entry with the expected semantic action digest. The fixture did not emit `PackageModuleIndexReadV1.reason`, so whether decode, generation Option, or another readback check failed is unproven. Receipts: `build/mini_builds/item6_cas_reason_20261010/`, `item6_cas_entry_state_20261010/`, and `item6_cas_explicit_copy_20261010/`. The three-cycle cap stops another readback retry here. Next: capture the reader's exact reason with a focused test, repair at its owner, then prove the full entrypoint and paired time/RSS gates.

## 2026-10-11 exact native readback branch

A failure-only native diagnostic rebuilt the 50-module CAS fixture and returned `readback-failed: valid=false reason=corrupt-entry` (receipt `build/mini_builds/item6_cas_readback_reason_20261011/`). A second bounded probe entered the entry frame reader at field 11, cursor 570 of a 583-byte row. Its tail was exactly `3:scc2:0;2:0;`, colon index 1, and digits displayed as `3`, but `digits.to_i64() ?? -1` produced `-1` (receipt `build/mini_builds/item6_cas_frame_reason_20261011/`). The immutable file hash and framing were valid; native decimal conversion on this substring is the observed failure. Temporary production prints were removed. The fixture retains only failure-path readback diagnostics.

Next repair: parse bounded decimal lengths directly from original text bytes in `package_module_index_frame_read_v1`, rejecting non-digits, leading zeros, and values exceeding the remaining row. This avoids allocating a tail and digit substring for every field, supporting the joint time/memory objective. Apply the same bounded parsing to list/count rows if native probes show the same defect there. Run one focused native publish/read/pin probe and a malformed-length regression, then resume entrypoint and paired p95/RSS evidence. This session's three-cycle limit is exhausted; runtime PASS is still absent.
