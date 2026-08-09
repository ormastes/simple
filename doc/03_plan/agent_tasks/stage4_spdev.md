
## 2026-08-09 Ownership and nilnil checkpoint

- Verified Stage3 recovery PASS: Stage2 sanity, Stage3 sanity, and Stage2 native-build capability; Stage3 SHA-256 `dc3d0af6e013e794744b41932f24cd218ecc49307fa336108386427f0b171437`.
- Stage4 streaming handoff SIGSEGV root cause: builder arrays/dictionaries were mutated in the transient parser scope but only the newest surface payload was promoted. The producer now promotes all builder containers before teardown.
- Evidence: the fixed Stage4 run crossed phase 2 and all phase-3 streaming HIR lowering, then reached `phase4:monomorphize:start`; the former post-parse SIGSEGV did not recur.
- Current blocker: focused HIR reported synthetic `nilnil` in `src/lib/nogc_sync_mut/io.spl`. Source inspection confirms no such identifier exists.
- Fix prepared: conditional-source assembly no longer uses a staged nil-backed empty separator; a production-facade parser regression was added.
- Verification state: ownership fix has Stage4 boundary evidence; the final nilnil fix is unverified because this session reached the mandatory three-cycle cap. Next session starts with one incremental Stage3 refresh and focused Stage4 resume.
- Sidecars: ownership review completed by highest-capability reviewer; merge owner remains Codex; final done mark remains pending fresh-session verification.

## 2026-08-09 nilnil resolution

- Parallel source-loader, runtime-representation, and HIR provenance lanes localized corruption to preprocessor nonblank-line reconstruction.
- Root cause: `_pp_split_lines` used `line_chars.join("")`; the native generic join path can reject the raw empty separator and return a nil sentinel. Adjacent reconstructed slots surfaced as terminal `nilnil`.
- Fix: all empty-separator joins in conditional reconstruction now use first-element-seeded text concatenation; semantic blank placeholders are excluded while newline separators preserve line counts.
- Review: highest-capability review reported no blocking findings and marked the change safe to accept.
- Evidence: pure-Simple Stage2/Stage3 recovery and capability gates passed (Stage3 SHA-256 `adf5a93256c20bffbc0c5e26bee46cb3717da8154c52c614e784a77ef0ef43b2`). Stage4 produced no `nilnil` diagnostics and advanced to unresolved `to_int` in `src/lib/nogc_sync_mut/test_runner/test_runner_args.spl`.
- Next blocker: resolve the independent `to_int` HIR surface/import issue, then resume cached Stage4.
