# Pinned Phase 2 bounded process call loses command text ABI

- Canonical ID: `phase2_bounded_process_text_abi_2026_10_27`
- Status: open; source compatibility does not close the underlying bug.
- Owner: DevHub / compiler-runtime owners.
- Created: 2026-10-27.
- Producer: P2 `13d73267e690b2cdd46438315e2bfe6d4d6c0c37bcfc15591a921fc9728b270b`.
- Source: `src/lib/nogc_sync_mut/sffi/process_capture.spl`.
- Regression: `test/fixtures/devhub/native_http_curl/main.spl`.

The actual HTTP compatibility probe returned missing command although curl8.21.0 was installed. The existing bounded tuple runtime provider accepts explicit command pointer and UTF8 length; a source adapter can preserve that ABI without changing the compiler or provider.

## Evidence

Frozen-source HTTP and binary probes compiled but returned missing command before any localhost request. The exact tuple-provider source adapter and final actual loopback evidence are owned by the provider lane; no success is inferred by this record.

## Removal condition

Remove the source adapter only after the deployed producer correctly marshals command text, argv, deadline and output bound to the normal bounded process ABI and passes real quoted-argument, Unicode, timeout, output-limit and HTTP transport regressions.

Commit identity and final receipts must be appended through the canonical BugDatabase API after integration. No compiler rebuild, standard SSpec execution or unexecuted matrix is claimed.
