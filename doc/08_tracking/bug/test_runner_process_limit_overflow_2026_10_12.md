# Test-runner process limit overflow accepted by bootstrap interpreter

Status: OPEN. Focused Phase1 diagnostic and Phase2 native validator qualification pass; full core and whole-test coverage remain unexecuted.

The Phase1 bootstrap diagnostic on source 7de247f6 and seed SHA256 49e31ad317c76d9ebf29e60e32d9a8866f9e74b426dfd02b518d75df30fc03a5 ran args_spec: 94 passed and two failed. One failure was a stale string assertion for the TestLevel enum. The other showed --max-procs=9223372036854775808 accepted because to_i64 retained a wider integer instead of rejecting overflow.

The validator now rejects non-ASCII decimal input first, ignores leading zeros for the range check, then compares significant decimal digits against 9223372036854775807 before any conversion. Zero and all-zero input preserve the existing inherited-host-limit contract; MAX and leading-zero MAX are accepted. Overflow, negative and fractional values remain errors rather than silently defaulting.

The isolated companion spec executes the actual argument parser and resource-policy owner: five focused groups passed, exit0, 3.533 seconds. It covers the two failed contracts plus signed maximum, larger and long values, zero, all zeros and leading-zero boundaries. The 94 already-green cases were not repeated. Evidence: /mnt/c/Temp/simple-phase1-args-fix-group-20261012/{receipt.json,request.json,source-packet/source-receipt.json}. These are bootstrap diagnostic results, not production Rust fallback or full Phase1 Markdown/comment/subtool coverage.

Required native core checks cannot run on the current compiler-only Phase3 entry, which lacks check/test dispatch. No full verification PASS is claimed.

The first native validator probe exposed a distinct omitted-end slice contract defect: value[first_digit:] lowers its end to -1, while the exact paired spl_str_slice provider clamps end to start and returns empty. GDB observed empty significant strings, causing overflow assertion13 to fail. The linked underlying OPEN report is [text_slice_omitted_end_native_contract_2026_10_12](text_slice_omitted_end_native_contract_2026_10_12.md). The production call now explicitly passes value.len(), tagged as a workaround; the compiler/runtime defect is not declared fixed by this app change.

Final native probe source06e14b6c uses the exact production validator bytes plus the preserved test/fixtures/bootstrap/process_limit_native_boundary/main.spl. To reproduce its isolated source closure, copy resource_policy.spl and this main.spl into a private src/app directory, commit it before SCV admission, compile with --source src/app --emit-object --backend=llvm --jobs=1, generate startup from the canonical compile_entry_point_c owner and manually strict-link the paired runtime archives. Exact Phase2 producer d3563806c3babfe69358380aa752a0b90b65f7119a7b83cb441a97a969ca9791 compiled object11040B in8.786s; strict link0, execution0,16 real assertions PASS, stderr0. The earlier omitted-end native execution remains failed in the evidence. No green tests were repeated after convergence.

The five Phase1 groups qualified the original lexical-bound candidate; the16 native assertions qualify its tagged explicit-end revision. Full check src/compiler, check src/lib and MCP/LSP checks remain unavailable on the current compiler-only Phase3 entry. No full verifier or release PASS is claimed.

## Local composition qualification

Transferred from upstream PR #3312 onto local release_phase3 `15616ab39c5bb206e6976dd520e3d09b257fa915`.
Production repairs and regression files in this composed candidate are
AUTHORED_UNEXECUTED. Historical upstream receipts above are not execution
evidence for this source composition or the current ARM/RISC-V compiler.
Status remains OPEN; full Phase3 and required verification remain pending.
