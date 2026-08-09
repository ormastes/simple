
## 2026-08-09 Ownership and nilnil checkpoint

- Verified Stage3 recovery PASS: Stage2 sanity, Stage3 sanity, and Stage2 native-build capability; Stage3 SHA-256 `dc3d0af6e013e794744b41932f24cd218ecc49307fa336108386427f0b171437`.
- Stage4 streaming handoff SIGSEGV root cause: builder arrays/dictionaries were mutated in the transient parser scope but only the newest surface payload was promoted. The producer now promotes all builder containers before teardown.
- Evidence: the fixed Stage4 run crossed phase 2 and all phase-3 streaming HIR lowering, then reached `phase4:monomorphize:start`; the former post-parse SIGSEGV did not recur.
- Current blocker: focused HIR reported synthetic `nilnil` in `src/lib/nogc_sync_mut/io.spl`. Source inspection confirms no such identifier exists.
- Fix prepared: conditional-source assembly no longer uses a staged nil-backed empty separator; a production-facade parser regression was added.
- Verification state: ownership fix has Stage4 boundary evidence; the final nilnil fix is unverified because this session reached the mandatory three-cycle cap. Next session starts with one incremental Stage3 refresh and focused Stage4 resume.
- Sidecars: ownership review completed by highest-capability reviewer; merge owner remains Codex; final done mark remains pending fresh-session verification.
