# resume-stage3 materialized-links consumer refuses dir-junction links (publication.parent-or-volume)

Date: 2026-11-14
Lane: work/release-1.0.0-mcp-local (MSVC), tips e71d18538bb / 3a99130752c
Related: candidate_hir_typekind_escapes_codec_visitor_2026-11-14.md (#9071),
bootstrap_stage2_seed_parent_retention_oom_2026-10-22.md (addendum)

## Symptom

The sanctioned two-phase Stage-3 lane
(`--full-bootstrap --stop-after-stage2` trust-root admission, then
`produce-bootstrap-planner-admission-v2.shs` + `resume-stage3-from-admitted.sh`)
dies in stage2-verify AFTER the preflight receipt verifies clean:

```
PASS — authoritative preflight receipt verified: .../bootstrap-preflight.env
stage3-materialized-consumer: Exception calling "Run" with "0" argument(s):
  "publication.parent-or-volume"
VERDICT — ABORTED: stage=stage2-verify exit=1 signal=none reason=stage2-verify
```

The exception comes from the native publisher embedded in
scripts/check/lib/bootstrap-stage3/authority.shs:5068-5073, reached via
bootstrap_stage3_materialized_git_state -> the receipt consumer: while
(re)validating the materialized-links receipt, the consumer RE-PUBLISHES a
recorded link whose parent directory is a reparse point (a directory
junction): `dir.Attributes & 0x410 != 0x10` -> throw publication.parent-or-volume.

## Why it happens on this lane

The Windows materializer (scripts/setup/materialize-symlinks-windows.shs)
records 66 mode-120000 index entries; 4 of them are the src/app t32
APPLICATION DIRECTORIES (cmm_lsp, mcp_t32, t32_cli, t32_lsp_mcp), which are
directory links (the file-hex/source snapshot records them as
`link-dir-hex:` rows pointing at examples/10_tooling/trace32_tools/*). The
consumer's publisher is written for FILE links (regular-file identity,
Links==1, same-volume checks); a dir link that needs republish lands on the
parent-reparse refusal. The receipt is fresh (produced minutes earlier by the
same bootstrap run, record_count=66, failed=0), so nothing is actually stale —
the consumer's repair path is spurious for dir links.

## Repro

1. Fresh worktree at origin/release/1.0.0 (any of the listed tips), MSVC env
   (scripts/setup/windows-msvc-bootstrap-env.shs), nightly-2026-09-15 cargo +
   clang+llvm-23.1.1 on PATH.
2. `SIMPLE_BUILD_MEMORY_RESERVE_BYTES=1073741824` (Hyper-V balloon host, see
   windows_balloon_memory_headroom_false_refusal_2026-11-13.md),
   `SIMPLE_BOOTSTRAP_PROCESS_TREE_RSS_CAP_KIB=50331648`,
   `SIMPLE_NATIVE_FILE_TIMEOUT=1200`,
   `sh scripts/bootstrap/bootstrap-windows.sh --msvc --full-bootstrap
    --stop-after-stage2 --mode=dynload --jobs=1
    --output=build/bootstrap/mcp-local --no-mcp`
   (admission publishes; the slim matrix may be killed early, e.g.
   BOOTSTRAP_VERIFY_CAMPAIGN_TIMEOUT_SECONDS=1, to keep the tree at
   admission-time state — the campaign legitimately materializes more links
   after admission and breaks the later snapshot gates either way).
3. `SIMPLE_LINKER_FLAVOR=msvc sh scripts/bootstrap/produce-bootstrap-planner-admission-v2.shs
    --target=//bootstrap:stage3 --reason=verify-landed-compiler-fix
    --parent-compiler=build/bootstrap/mcp-local/stage2/x86_64-pc-windows-msvc/simple.exe
    --planner-backend=llvm --bootstrap-output=build/bootstrap/mcp-local`
4. `SIMPLE_BOOTSTRAP_REASON_RECEIPT=<that receipt> SIMPLE_WINDOWS_MATERIALIZED_LINKS_RECEIPT=
    <run's materialized-links/windows-materialized-links.*.env>
    sh scripts/bootstrap/resume-stage3-from-admitted.sh build/bootstrap/mcp-local`

Result: preflight PASS, then publication.parent-or-volume, ABORTED.

## Evidence gathered

- All earlier gates in the chain pass with in-run artifacts: planner admission
  (v2, verify-landed-compiler-fix), preflight receipt (PASS — the binding
  requirements are: seed = stage2-runtime-authority/simple.exe, expect-config
  ends with a stray " llvm" suffix derived by the resume, git/source snapshots
  must equal the admission-time captures — which requires stopping the
  bootstrap right after admission).
- The consumer failure is deterministic across two pristine runs (cycles 19
  and 20 at e71d18538bb) and independent of the receipt PID (206, 794).
- authority.shs:5072 — `if ((dir.Attributes & 0x410u) != 0x10u || src.Volume
  != dir.Volume) throw publication.parent-or-volume;` — the parent of the
  link being republished carries FILE_ATTRIBUTE_REPARSE_POINT (0x400).

## Owner asks

1. Teach the consumer's publisher to skip (or handle) dir-type link records
   (the link-dir-hex rows), or make the producer record them in a form the
   consumer republishes without the reparse-parent refusal.
2. Alternatively give resume-stage3-from-admitted a no-repair validation mode
   when the receipt is fresh (validated identity without republish).
3. Document the intended seam: currently no flag stops the bootstrap
   immediately AFTER Stage-2 admission but BEFORE the compiler-tests campaign
   materializes the t32 links that break the snapshot/git-state gates — a
   --stop-after-admission would make the two-phase lane race-free.

## Impact

Blocks the entire MSVC stage3/stage4 resume lane on Windows hosts whose tree
contains the t32 application directory links (i.e. every release/1.0.0
worktree), which blocks the downstream native MCP rebuild + deploy for the
three-client configuration work queued behind it.
