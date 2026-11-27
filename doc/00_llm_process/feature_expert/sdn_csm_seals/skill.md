# SDN .csm sidecar seals (feature expert)

A sealed data file `dir/X.sdn` has ONE empty sibling `dir/X.<algo>_<lowercase hex>.csm`
(PR #6468). The hash covers the LF-normalized content (every CR dropped), so CRLF
checkouts verify. Replaces the in-file `#sdn-crc32:` header (still accepted as LEGACY).

- Algorithms: `crc32` (8 hex), `xxh3` (16, default), `blake3` (64).
- Policy: `config/check/sdn_seal_policy.sdn` (`seal_policy |glob, algo|`, first match wins).
  A `.csm` whose algo differs from the policy is RESEAL_NEEDED (gate FAIL).
- States (`csm_judge`): OK | CORRUPT (mismatch/odd tag) | MERGED_UNSEALED (>1 sidecar after a
  merge) | MISSING | LEGACY. Loader (`src/lib/nogc_sync_mut/database/csm_seal.spl`) fails closed.
- Shell twin: `scripts/check/sdn-seal-lib.shs` (`csm_hash_hex`, `csm_hash_batch`, `csm_seal_file`).
  Native `xxhsum -H3` / `b3sum` preferred, else `bin/simple run src/app/hash/main.spl --xxh3 --lf`.
  Every hasher is KAT-checked on empty input. xxhsum prints three dialects (GNU
  `XXH3_<hex>  stdin`, bare hex, BSD `XXH3 (stdin) = <hex>` as in Ubuntu 24.04's 0.8.2); all parsed.
  Verified byte-identical native vs CLI (xxhsum 0.8.4: bug_db, test_db, CRLF copy, 1-byte, 100 KB).
- Reseal: `sh scripts/check/reseal-sdn-crc32.shs <file.sdn>` writes the one new sidecar and deletes
  every other (collapses MERGED_UNSEALED, also across algorithms). Merge conflicts on bug_db:
  union rows, delete all `bug_db.*.csm`, reseal, `git add` both. Writers (bug-claim, tracking
  sync, Simple writers) reseal on write; `scripts/vcs/gh-pr-sdn-sync.shs` reseals the merged tree.
- Gate: `scripts/check/check-sdn-crc32-sealed.shs --rev <sha>`; use `--no-selftest` in loops.
  CI installs xxhsum; blake3 selftest fixture is skipped (NOTE) when no b3sum/CLI exists.
- Windows: works with `MSYS_NO_PATHCONV=1` (temp dirs and tool root use native `C:/` spelling).
