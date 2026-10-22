# Result.err() missing from native method lowering

Status: focused native repair qualified; repository-wide verification and release admission remain open.
Workaround tag: `RESULT_ERR_MATCH_PROJECTION` (explicit `match` previously bypassed the missing method; this patch implements the method).

## Reproduction and root cause

A typed `Result<i64, text>` returned by `failure()` fails native compilation at `outcome.err().unwrap()`. The predecessor b20ad174493ac6a18207c0c3b4aa717cb9a7d4455f80f7a9b18f5c515f1d3d60 reported both unresolved `err` and unresolved `unwrap`, exited 1 and emitted no object. The focused 148-module compiler graph also contained this authored chain in `mir_opt/mod.spl`.

The native MIR method dispatcher admits `ok` but omitted zero-argument `err`. The existing typed Result combinator knew the success projection and never selected the error payload for this method. This is separate from imported record payload support and the pending Result.map change (PR 3229). Existing unresolved dispatch records a diagnostic and emits a panic before its placeholder; the warning text alone does not establish silent zero execution.

## Repair

Two body-only owners add zero-argument, type-directed Result.err admission and select the Err discriminant (1) and E payload. The projection uses the existing Some/None wrapping and remembers `Optional<E>` for chained methods. Ok produces None. Wrong arity and unrelated receivers retain ordinary method resolution and diagnostics. No runtime aliases, flags or foreign helpers were added. The qualified producer supports i64/f64/bool/text; record projection is not claimed by its evidence.

## Native evidence, 2026-10-12

Producer `dae595a4c6ad7481633a69f92b29754522aa65927823b081e19b17090cf820af` includes the admitted namespace, generic and enum-owner repairs. Real Hello compiled, linked against the generated core-C runtime pair, and printed `HELLO_RESULT_ERR_METHOD` with exit 0.

All five fixtures under `test/fixtures/compiler/result_err` passed:

- `positive.spl`: 16 assertions; Err text, Ok None/fallback, unchanged ok(), zero/negative/nil-collision integer 3, bool false, float 1.5 and negative-zero sign, empty/UTF8 text, and a custom struct's err method. Object 16,256 bytes, native exit 0.
- `eval-once.spl`: payload and exactly-one receiver evaluation, 2 assertions. Object 3,368 bytes, native exit 0.
- `wrong-arity.spl` and `wrong-receiver.spl`: compiler exit 1, concrete unresolved err diagnostics, object 0.
- `panic-none.spl`: object 2,088 bytes; native exit 1 with `called .unwrap() on a nil Option`, unreachable print absent.

Three MIR semantic specs were added to `builtin_method_extras_lowering_spec.spl`. They are authored but not executed: this bootstrap producer has no SSpec runner. Native fixtures are the executed evidence; no full compiler/core/MCP or release PASS is asserted.

## Cache and performance evidence

Original seed SHA 445c9a1159b5187fd201a830ca9d52f072db0a7e34945f651c8f508399cad91d and the 1,237-owner declaration layout were preserved. Attempt 1 reused 1,233 objects, compiled three, and timed out only the method dispatcher at its 60-second per-file bound. Attempt 2 retained the successful builtin owner and rebuilt exactly entry, mandatory asm and the timed-out method owner: 1,234 reused, 3 compiled, 0 failures, 175.780 seconds total, peak process-tree RSS 2,067,345,408 bytes. The per-file bound was 180 seconds; no semantic code changed between attempts. This large dispatcher compile cost is a concrete performance limitation, not a reason to invalidate the entire cache. No third repair or fourth aggregate was attempted.

External receipts: `/mnt/c/Temp/simple-result-err-method-repair-20261012/`, especially `native-cases-summary.json`, `producer/attempt2/targeted-repair-receipt.json`, source bindings and commands. Producer linking used its paired Rust runtime; native fixture linking used the generated core-C target runtime. These runtime roles were not mixed.

## Prevention and remaining scope

Keep typed admission, discriminant selection, payload E and Optional metadata together. Preserve negative tests, custom method precedence, payload representation and receiver evaluation count. The other focused graph failures (`copypropagation_*` UFCS and imported record unwrap) are separate open causes. All previously exhausted feature and whole-aggregate retry caps remain unchanged. Cross-platform source logic introduces no host access, but Windows, macOS, BSD and SimpleOS execution was not performed.

## Landing composition boundary

The landing candidate is based on release_phase3 eca61a8efc4f054f2c37d4cecef2c140165e4180. Since the tested frozen source, this branch added nominal record ownership and a fourth source_owner argument to builtin_result_payload. The port preserves those changes and passes the retained source_owner while projecting E. Native behavior of this exact composed landing source is UNEXECUTED, including record payloads. Earlier native PASS applies only to producer dae595a and the frozen source hashes in the evidence. No rebuild or admission is implied by this conflict adaptation.
