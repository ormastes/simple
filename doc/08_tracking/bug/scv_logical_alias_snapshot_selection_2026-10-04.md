# SCV snapshot selection drops logical directory aliases

Status: source repair prepared; native regression and bootstrap validation pending.

The Windows Phase4 T32 failure used source
`9737d1217bc44439b56bba6c2ef16faaff51bd20` and snapshot revision
`scv-revision-v1-d1538026fd00d61d36804861b126f0d2f000659b7f7962393d98f12d8c4305a9`.
Its admitted source generation `99f17385eb15a38cfd17d6cfa559f691b5773091413abace1f2a04de8ee1b709`
contains 92 descendants of the declared Git directory aliases `src/app/cmm_lsp`,
`src/app/mcp_t32`, and `src/app/t32_cli`. A read-only audit found all 92 physical
files matching their admitted content hashes and byte counts. None appears in
the snapshot inventory. The alias targets are inside `examples/10_tooling/trace32_tools`.

`scv_compile_snapshot_inventory_entries_v1` resolved each identity through
`path_absolute` before matching requested source roots. A provider that resolves
directory links turns the logical `src/app/...` identity into `examples/...`,
then excludes it from the `src/app` selection. Rust's path provider resolves
links; the Windows C provider uses lexical `_fullpath`. This provider difference
is source evidence, not proof of which provider created the retained snapshot.

The repair selects by the admitted logical identity and checks checkout/cache
containment separately. Existing materialization still verifies the admitted
hash and byte count, writes regular bytes at the logical identity, and detects
source drift. The additional logical rows change the content-addressed snapshot
revision; the old snapshot is neither modified nor relabelled.

SCV v1 authenticates logical identity and contents, not link topology. Declared
alias origin remains the source materialization catalog/Git source authority.
The existing platform path provider is not a new handle-pinned, no-follow
ancestor security boundary; this fix makes no such claim. There is no fallback
from an immutable snapshot to its live alias target.

Regression coverage:

- Five unit scenarios cover logical alias membership, exact root boundaries,
  excluded physical siblings, traversal/outside-owner refusal, and managed caches.
- `test/04_smoke/scv_directory_alias_snapshot.spl` exercises real publication,
  selected manifest membership, independent snapshot contents after owner mutation,
  and stale-admission materialization refusal.
- `scripts/check/scv-directory-alias-snapshot-test.ps1` creates a real Windows
  junction and checks the produced snapshot has regular files and ancestors.
  Supply the actually compiled fixture via `-FixtureBinary`; it never substitutes
  a simulated link or reports a skipped native run as PASS.

PowerShell AST validation passed. Native Simple cases remain UNRUN. The retained
read-only proof is in the local bootstrap evidence packet under
`scv-logical-alias-selection/frozen-inventory-proof.json`.
