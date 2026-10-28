# BuildRunner cached output loses executable permissions

Baseline: release/1.0.0 `74650d7f4f7`. Date: 2026-10-29.

The runtime file-copy repair preserves mode on newly copied output. However,
BuildRunner accepted an existing destination using only its content hash, and
both cache admission paths bypassed publication for matching bytes. Removing
execute permission from a published Hello executable therefore left an
unusable output that still qualified as a cache hit and passed `verify`.

Publication now compares ordinary POSIX permissions with the retained artifact
and repairs mismatches after validating both files' digests. It also sets and
checks staged-copy permissions before publication, including with older pinned
copy providers. Special mode bits are not propagated. Different content and
non-regular leaves remain refused. Windows keeps its existing permission model.

Both cache paths consult the already retained local output before admission.
An SSH attempt's collected local copy is sufficient: a matching cache hit does
not contact the remote host or acquire another process owner. Missing output
bytes retain the previous recovery route. A missing retained copy cannot supply
permission authority and therefore does not qualify for a repaired cache hit.
Read-only `verify` compares modes and refuses drift without modifying output.

Path-based permission changes have the same protected-root requirement as
existing publication: the manager must own the output and attempt directories
and their ancestors. Static symlinks are refused; hostile concurrent replacement
inside those private roots is outside this change's contract.

## Verification

The pinned Phase 1 source interpreter was reused without rebuilding:
`aa58a24ebe00248b428d4507e5cb0c58ec497c28ec8b2a3ed71ec65d697f756c-ecd1ed1cbf3f68a7abc6c2f852358542fae0b6e2e66c88e5abfcd5ea22cb3d2b/simple`,
under the existing `release-bootstrap-integration-20261025` bootstrap generation.
Each spec ran with `SIMPLE_LIB=src` and
`test SPEC --mode=interpreter --assert-ran --no-cache --no-db --no-session-daemon --sequential`.

- Baseline mode regression: 1 passed, 2 failed. Matching cached content retained
  missing execute bits; nonexecutable content retained stray execute bits.
  Log: `/private/tmp/buildrunner-cached-mode-red.log`.
- Final POSIX mode spec: 4/4. It executes a repaired shell Hello fixture with
  exact stdout, checks read-only mode refusal, removes stray execute bits,
  refuses different bytes, and refuses a destination symlink without changing
  its target. Log: `/private/tmp/buildrunner-cached-mode-final-posix.log`.
- Extended output-root spec: 3/3. Its existing synthetic receipt fixture now
  demonstrates `chmod` drift, nonmutating `verify` refusal, actual CLI cache
  repair, and successful verification. An SSH-host cache case uses the retained
  local snapshot without remote recovery. Log: `/private/tmp/buildrunner-cached-mode-cli.log`.

These are source-interpreter component and cache-orchestration tests, not native
compiler execution evidence. The shell fixture and synthetic unit receipts are
not a substitute for the production Hello integration. Darwin V4 descendant
ownership remains unavailable, and previous pinned native manager builds did
not produce an executable before their RSS caps. No provider guard was relaxed,
no no-child proof was added, and no Phase 2 compiler was rebuilt.
