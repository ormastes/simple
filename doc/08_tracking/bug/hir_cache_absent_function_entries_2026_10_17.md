# HIR cache admitted absent nonnullable function entries

Status: generator and generated-code repair authored in an isolated worktree; new codec tests and generator regeneration/freshness checks are unexecuted. The initial loss of function values remains open. No frozen campaign source or artifact was edited.

## Actual failure and narrower diagnosis

Canonical Stage 2 candidate SHA256 `7786a031bef37bab3e572b93c345b7cf49c22950859f59bd6bd116da1d712d87` linked, then failed the original `p2_add` admission probe with Windows access violation 0xC0000005 after HIR completed. The retained object maps the fault to `MirLowering.prescan_one_function_v1+0xc98`: its complete HirFunction argument is tagged nil (3), masked to zero and dereferenced. A read-only dump shows all five function dictionary values already nil. The linked rt_dict_values path uses the Rust dictionary layout matching that dump; no C/Rust dictionary ABI mismatch is demonstrated.

The retained cache is earlier evidence, not merely a crash symptom:

`D:/dev/simple-smux-upstream-20261017/build/bootstrap/smux-astra-campaign/stage3/x86_64-pc-windows-msvc/stage2-home/.cache/simple/v1/projects/7dcf7beb22f33342151bfd60494ef3d85d51da9a92b6318d2576edd1a65e5941/native-build/v1/default/hir/02c1269698e465e094c30d82c2b8a20ad9a865911db3a2acd8f4ae74af4ec75a.parser-v4.hir`

It is 4156 bytes with SHA256 `39f1ff805033e6d3a1f79a6708e139e40ea742dede2085db74c9b3fc299fe3a7`. Exact schema alignment: lines 583-593 are the SymbolTable root-scope dictionary; 594 and 595 are its final empty structural-union dictionaries. Line 596 is HirModule.functions count 5. Lines 597-611 contain five `[key-present=1, SymbolId=0..4, function-present=0]` triplets. The generated decoder consequently inserts five nil function values. This is static inspection of retained bytes against generated schema, not a test execution.

The `bodyful:` envelope label comes from parser classification, not proof that function payloads survived serialization. Decode/re-encode equality alone accepted this stable but incomplete frame.

## Actual controlled diagnostic

Root ran the same rejected compiler and original p2_add source with supported `SIMPLE_HIR_CACHE=0`, a private native cache/output and the unchanged resource bound. Build and output execution both completed with exit 0 and quiescent=1; output was exactly `5\n`, stderr empty. Build peak RSS was 3,644,476 KiB and run peak 2,628 KiB. The resulting 1,414,144-byte executable has SHA256 `136bc051e0faa12ed6be8cc492a85689c0095f7085c3349470f8b30acbd815ca`.

Receipts and logs are retained under `D:/dev/simple-smux-upstream-20261017/build/smux-astra-crash-20261017/uncached-p2-add*`, including `uncached-p2-add.job.env` and `uncached-p2-add-run2.job.env`. The earlier run harness failure 89 from missing MSVC environment remains recorded separately. The successful diagnostic distinguishes the failed cache-enabled path from fresh HIR for this fixture. It does not qualify the compiler, prove the exact first corrupting store, validate the new codec, or authorize disabling cache in normal admission.

## Repair boundary

`HirModule.functions` is declared `Dict<SymbolId, HirFunction>`. Neither an absent key nor an absent function is a valid declaration entry. The authoritative generator `src/app/compiler_schema/codec_gen.spl` now requires these immediate dictionary nodes. Its generated encoder rejects absence in the same branch that formerly emitted a zero presence marker; it does not rely on a separate preflight dictionary read that might disagree with serialization. The generated decoder marks missing entries malformed in the existing presence branch and inserts an entry only while `r.ok`. Although the Rust runtime already rejects nil keys without trapping, invalid decoding now performs no dictionary insertion at all. Other nullable nodes, including extern bodies and unresolved types, retain their existing behavior.

The valid wire format is unchanged. Legacy and canonical writer entrypoints already propagate writer rejection; legacy/stable and bounded decoder entrypoints already propagate reader failure. `driver_hir_cache.spl` therefore retains its existing counted codec store refusal and decode miss. Invalid files are not deleted, rewritten or relabeled, and no runtime/GC behavior changes.

Seven new scenarios in `test/01_unit/compiler/hir/hir_codec_required_functions_spec.spl` use actual parsing/lowering and generated codec operations. They cover real function/literal-body roundtrips, canonical bounded roundtrips, an explicit valid-wire control, absent values, absent keys with a valid function payload, bounded malformed reasons, and legitimate empty dictionaries. A proposed typed nil assignment was removed because its source acceptance was not established; no new extern or fake dictionary constructor replaces it. Runtime coverage of the writer's corrupted-state refusal remains pending a supported fixture.

One separate scenario in `test/01_unit/app/compiler_schema/hir_required_function_codec_generation_spec.spl` calls the actual `CodecUniverse.load` and `emit_codec_file`, requires the refusal and guarded-insertion output, and compares the entire generated text to the checked-in codec. It is authored but unexecuted; hand alignment is not claimed as generator execution.

Pending: execute the new scenarios and existing codec/cache suites under an admitted producer; regenerate with the real generator and verify exact generated-file freshness; run normal cache-enabled p2_add/admission. The underlying erased-read or initial-store defect remains separate and unresolved. This fix prevents persisted nil declarations from being treated as complete HIR; it does not synthesize missing bodies.
