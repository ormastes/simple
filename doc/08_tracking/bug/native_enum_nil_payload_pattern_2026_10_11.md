# Nested nil enum payload and optional text provenance

Status: OPEN. Canonical bug ID: `native_enum_nil_payload_pattern_2026_10_11`. GitHub: https://github.com/ormastes/simple/issues/2981

Original failure: C35 runner Ok(nil) payload unsupported at rt_hal_isolated_host.spl:157. First binding workaround ARM exit1; unwrapped text formatted as integer handle.

Workaround commits:

- `3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a`; recovery parent `7324234fe33dcc7292849f4907439353228d8535` (review only).
- `9773949ac215c2cb8e8e1234db6b1bc40e967d12`; recovery parent `3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a` (review only).

Current qualification: C36 narrow six-assertion fixture ARM runtime PASS; RISC-V ELF243 object PASS, not execution. Actual rt_hal_isolated_host consumer still MIR FAIL on separate callback fields; private process-loop/runner not qualified.

Producer: `5315b60ff617fd4595390609e89bcd8530204c4595fc7b2f28b32e5b7a40f235`. Source integration before annotations: `f7fdafdea3b251b4fa6f84b7203bd319cce8bc6c`.

Evidence: `/home/yoon/dev/simple-bootstrap-c06-20261011/build/native_probe/phase3-whole-20261011-c06/c36-result-optional-text-boundary/result_optional_payload_workaround/{arm-runtime-source-coverage,riscv-runtime-source-coverage}/`.

Reproducing/prevention source: `test/fixtures/compiler/result_optional_payload_workaround/main.spl`.

Background fix owner and removal condition: MIR enum literal-payload and optional text provenance owners. Restore original Ok(Some(chunk))/Ok(nil) arms and remove identity helper only after original-form negative/present/absent controls and real consumer pass.

These are temporary source workarounds, not underlying fixes. Keep the DB and GitHub bug open. Apply and qualify a permanent owner repair and original-form tests before a separate narrow retirement commit. Root fixes for tracker APIs (#2998), missing imports (#3008/#3009), and the #3012 source group are not relabeled as workarounds here.

Provenance mapping and landing status: Workaround provenance: 3ac1706cb94ac4ab35d7b4f8b81bba7be728af2a -> dbc1c66792be83a937d0b7806324788049f9bf5d (stable patch-id equal; both UNLANDED on checked release); 9773949ac215c2cb8e8e1234db6b1bc40e967d12 -> 09cbce4e77a7707881d570739bd1d50c39703648 (stable patch-id equal; both UNLANDED on checked release). Release checked 95c12f073ffefa99ac774264beeedd68a47e7676. Add actual reachable landed commit/PR link after source landing; original branch SHA is not a release claim.

Exact qualified/failing source attribution: Passing narrow C36 ARM/RISC-V fixture source 9773949ac215c2cb8e8e1234db6b1bc40e967d12; actual C36 consumer integrationf7fdaf remains failing on callback ownership.

Traceability annotation base: `64b8854eaa6eee9470470ddbcef5fa2165902d13`. No earlier source or retained build evidence was modified; native qualifications remain bound to their exact sources above.

## Lane note 2026-11-03 (wl01 lane)
Deferred: per the row the workaround stays active until original-form controls and the real consumer pass on a rebuilt producer; MIR enum literal-payload provenance owners cannot be qualified without native runs.

## Native (pure-Simple) lane note 2026-11-05 (p1w-enumnil)
Reproduced on stage3 43 (`s3_fable43.exe`, x86_64-pc-windows-gnu, llvm-mingw, `native-build --entry-closure --backend llvm --runtime-bundle core-c-bootstrap`, entry renamed + relinked with `-lwinhttp`):
`test/fixtures/compiler/result_optional_payload_original` exits rc=1 (first check, `consume(Ok(Some("bc")), "a", 3) != "abc"`).
A probe isolated it: in an `Ok(Some(chunk))` arm over `Result<text?, text>`, `chunk.len()` = 2 (correct), but `"{chunk}"` prints `1861464387841`. The binder holds the raw payload word, not text. Arm selection (`Ok(nil)`, `Err`) and `i64` payloads were already correct natively.

Root cause: HIR `lower_match_pattern` (expression_components.spl) routed nested builtin wrappers through the untyped `lower_pattern` path. Only a unit-variant or `nil` inner pattern got the subject-derived slot type. So `chunk` had no type, and MIR `emit_deep_subpattern` bound the raw `rt_unwrap_or_self` word as i64.

Fix: HIR now lowers a builtin wrapper nested in a builtin wrapper with its slot type taken from the subject's generic arguments (`lower_nested_wrapper_v1`). MIR's depth>=2 binding decodes a HIR-proven `text` slot through `decode_declared_enum_payload_slot`. New fixture: `test/fixtures/compiler/result_optional_payload_text_binding`.

Status: fix-implemented-verification-pending. Verifying needs a stage3 rebuilt from this source. On 43 the new fixture builds and links, prints the canary, and exits rc=1 (fails before the fix). Repro: build that fixture and `result_optional_payload_original` with the new stage3 using the recipe above; both should print PASS with rc=0. A separate finding: on 43, a fixture draft with `Err(nil)` over `Result<i64, text?>` plus `Some(nil)`/`nil` over `text??` failed MIR (the arm was not isolated) with "nil sub-pattern requires a declared optional payload slot". That is not covered by this fix.

## Verification note 2026-11-05 (r-enumnil)
Baseline on `s3_fable43.exe` (24416768 B): fixture `result_optional_payload_text_binding` builds, prints `hello canary`, exits rc=1 (check 1). Native PASS not yet measured: host commit free 25 GB blocked a private leaf; fold into leaf 46 requested (`_out/leaf_enumnil.ps1` / `relink_enumnil.ps1` in the lane worktree). Spec `test/01_unit/compiler/mir/nested_wrapper_text_binder_spec.spl`: 7/7 on branch, 5/7 on origin sources. The `Err(nil)`/`Some(nil)` MIR error is `match_nil_subpattern_requires_declared_optional_slot_2026-10-24`.

## 2026-11-06 native verified (p1w5)
PR #6943 is merged. `enumnil_r` (the same cases as `result_optional_payload_text_binding`) was built natively with s3_fable46_w5. It exits rc=0 and prints `result_optional_payload_text_binding: PASS`. Status: fixed.
