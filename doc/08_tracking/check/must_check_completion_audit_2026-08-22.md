# Must-check completion audit — 2026-08-22

Scope: the original must-check attachment plus the later Caret and cross-host
additions. `PASS` below means retained evidence proves the exact row. `SOURCE`
means implementation exists but runtime acceptance is still missing. `TODO`
never counts as PASS.

| Requirement | State | Authoritative evidence or exact unblock condition |
|---|---|---|
| Textual SDN ledger with TODO-to-first-PASS promotion | FAIL | Generic and signed external promotion paths now fail closed and reject self-attestation, but no production reviewer trust root is provisioned; external TODO-to-PASS promotion remains unavailable until `config/check/must_check_external_reviewers.sdn` receives a reviewed public key |
| Lightweight push / expensive bootstrap split | PASS | `config/check/must_check_gates.sdn`; push retains bounded range/ref checks and two sub-second tree checks; measured whole-tree/compiler/executable rows plus detector mutation fixtures are bootstrap-owned |
| Push completes within ten seconds | PASS | Latest exact committed-tree path on 2026-08-24: 4.84s, 224,840 KiB peak RSS, down from the same-session 6.10s / 224,968 KiB baseline after replacing per-row subprocess parsing with one linear ledger pass; see `../bug/push_must_check_remaining_overhead_2026-08-24.md` |
| Push evidence is exact-ref, bounded, and monotonic | PASS | Exact pushed blobs, 64 MiB pre-hash aggregate cap, two-ref cap, required-ID ratchet, initial unpromoted state, and post-PASS downgrade rejection are covered by `must_check_tiering_test.shs` |
| Bootstrap recorder uses exact admitted Stage 4 | PASS (contract) | Bare mode rejects mutation; `--record-bootstrap-success` binds Stage 1–4 and injects exact Stage 4 into automated gates; recorder self-test PASS |
| Ad-hoc bootstrap reaches admitted Stage 4 | TODO | A fresh diagnostic Stage 2 was admitted, but this does not promote any ledger compiler row. Stage 3 cycle 1 reached MIR and failed at `eval_gt`; cycle 2 cleared that frontier and failed at adjacent `eval_gteq`; cycle 3 was externally terminated with exit 143 before MIR, so the final typed-carrier fix is not admitted. Retained evidence rules out the repository reapers and system memory killers; the repeated 345--348 second boundary points to a blocking tool-call deadline. The three-cycle cap is exhausted for this session. Resume from `build/bootstrap/mustcheck-stage3-arm-body` in a fresh scoped persistent PTY, poll at no more than 60-second intervals, and require `real-lower:done eval_gteq` plus Stage 3 admission. See `../bug/stage3_mir_values_equal_segv_after_full_hir_2026-08-25.md`; do not substitute the Rust seed |
| Whole test finds Markdown and source-comment Sdoctests | SOURCE | `simple test test --whole` now separates spec path from configured Markdown and `src/lib`, `src/compiler`, `src/app` comment roots. Actual Simple execution requires an admitted Stage 4 binary |
| Sdoctest docs, SPipe docs, wiki, README, glossary | PASS (source review) | `doc/02_requirements/app/testing/sdoctest.md`, `doc/06_spec`, `doc/07_guide/infra/testing.md`, `doc/00_llm_process/llm_wiki.md`, `README.md`, and `doc/glossary.md` agree on names and scope |
| Unix and Windows setup scripts | SOURCE | Unix linked-worktree fixture PASS. Native Windows linked-worktree evidence remains `windows-hook-installation` TODO |
| Caret local Slang inference | TODO | No Slang generation endpoint/provider receipt; use the matching row in `doc/03_plan/agent_tasks/must_check_tiering.md` |
| Caret Claude/Codex/Gemini/Kimi wrappers | SOURCE | Bounded argv/process fixtures are automated; real installed provider launches remain a distinct TODO |
| Caret agent manager, multiple Carets, smux | SOURCE/TODO | Agent-manager primitives and bounded multi-manager fixtures are automated; production smux PTY lifecycle remains TODO |
| GPU-assisted web server at least nginx parity | TODO | No qualifying implementation plus retained comparable benchmark receipt |
| GPU-assisted DB server at least PostgreSQL/MySQL parity | TODO | No qualifying implementation plus retained comparable benchmark receipt |
| SimpleOS SBC and matching QEMU `ls` | TODO | Requires paired live receipts; offline/QEMU-only evidence cannot promote the SBC row |
| SimpleOS clang, Simple toolchain, and server executables | TODO | Requires in-guest compile/link/run and executable receipts from the same admitted image/toolchain |
| Shared RV32/RV64 templates and Simple-generated VHDL Linux boot | TODO | Requires ownership audit, generator provenance, boot, and command-correlated `ls` receipt |
| Binary size at most Go | TODO | Requires retained comparable stripped-artifact measurement |
| Interpreter startup beats Python/Bun/Go | TODO | Requires retained cold and warm launch distributions on matched workloads |
| Runtime benchmark at least Rust/Go | TODO | Requires retained representative benchmark, semantic parity, timing, and memory evidence. Executable header/statistics validation exists, but outer target identity and per-language build origin remain open in `../bug/rust_go_benchmark_receipt_target_origin_binding_2026-08-25.md` |

## Current completion boundary

The must-check scheduling, ledger, hook, and documentation infrastructure is
implemented and its shell-level evidence is green. The umbrella goal is not
complete because the admitted Stage 4 runtime and every row marked `SOURCE` or
`TODO` above still require their stated acceptance evidence. The canonical gate
registry and ledger retain those obligations; postponement cannot delete or
promote them.
