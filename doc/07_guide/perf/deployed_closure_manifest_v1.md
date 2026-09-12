# DeployedClosureManifestV1

Part of the L5 wave ("generated/deployed binary closure", 2026-09-12), package
L5-F. Produces an inventory of every physical file a deployment root ships,
separates **primary binary bytes** from **total closure bytes** from
**duplicated bytes**, and gates on physical (non-hardlinked) duplication.

This is a byte-accounting tool, not a memory-profiling one: none of these
numbers are process RSS. Never quote `closure_bytes` or `duplicated_bytes` as
"how much memory this uses" — they describe what is on disk under the root you
pointed the tool at.

## Producer

```bash
sh scripts/perf/deployed-closure-manifest.shs <root> [--out <file>] [--wrapper-name NAME]...
```

- `<root>` is required and positional. The tool is **read-only**: it never
  writes, links, or deletes anything under `<root>`.
- `--out <file>` writes the SDN to `<file>` instead of stdout (and prints a
  one-line confirmation with the four headline numbers to stdout).
- `--wrapper-name NAME` (repeatable) additionally classifies a basename as
  `wrapper` regardless of location — use this when scanning a root (e.g.
  `bin/`) that mixes generated wrapper scripts from `scripts/setup/setup.shs`
  (`simple_mcp_server`, `simple_lsp_mcp_server`, `t32_mcp_server`,
  `t32_lsp_mcp_server`, and their `.cmd` twins) with unrelated tools.
- Exits 2 (`ERROR — nothing was checked`) when `<root>` does not exist, has
  zero regular files, or no `sha256sum`/`shasum` is on `PATH`.

### What counts as "the deployment"

Point `--root` at the exact surface you want measured:

| root | covers |
|---|---|
| `bin/release` | the per-triple compiler + companion binaries, `.sha256` sidecars, and anything else sitting in that tree (including stray backups) — this is what `scripts/bootstrap/bootstrap-from-scratch.sh`'s deploy step (`deploy_dir=` block, around line 4030) populates: `simple`, `simple_seed`, `simple_ui_backend`, `simple_mcp_server`(+`.sha256`), `simple_lsp_mcp_server`(+`.sha256`), one `launcher.<program>` per program, and the `authority.*.env`/`.sdn` provenance files |
| `bin` | additionally sweeps the generated wrapper scripts `scripts/setup/setup.shs` writes directly into `bin/` — pass `--wrapper-name` for each one you want classified `wrapper` |

### Kind classification

| kind | rule |
|---|---|
| `sidecar` | basename ends `.sha256` |
| `smf` | basename ends `.smf` |
| `wrapper` | basename starts `launcher.`; OR a top-level file (directly under `<root>`, not in a subdirectory) whose first two bytes are `#!`; OR a basename passed via `--wrapper-name` |
| `primary` | basename is exactly `simple`, `simple_seed`, `simple_ui_backend`, `simple_mcp_server`, `simple_lsp_mcp_server`, or `simple_native`, AND the file sits inside a subdirectory of `<root>` (a platform-triple directory) — a same-named file directly at the root (e.g. `bin/release/simple`, the platform-dispatch wrapper script) is classified by the wrapper rule instead, not this one |
| `other` | everything else (`authority.*.env`, unrecognised backups, lock files, etc.) |

### `primary_binary` / `primary_bytes`

The single `kind=primary` row with the greatest size (ties broken by the
earliest relpath in a `LC_ALL=C` sort). This reliably picks the real compiler
binary out of a triple directory even when smaller same-classified companions
(`simple_mcp_server`, `simple_lsp_mcp_server`) are also present, because the
compiler binary is always far larger. If no file is classified `primary`,
`primary_binary` is the empty string and `primary_bytes` is `0` — this is not
an error condition (a wrapper-only or fixture root may legitimately have no
primary binary).

### `duplicated_bytes`

Group every file row by `sha256`. For each group, count the **distinct
inodes** it spans:

- All occurrences share one inode (any number of hardlinks) -> the sha256
  contributes `0` to `duplicated_bytes`. This is the "hardlink-dup -> PASS"
  case: linking is exactly how you ship one physical copy under two names.
- The sha256 spans more than one distinct inode (at least one copy exists
  that is not a hardlink of the others) -> **every** row carrying that
  sha256 contributes its `size` to `duplicated_bytes`, including any
  hardlinked siblings within the same group. A hardlinked pair sitting next
  to an un-hardlinked third copy is not itself the problem, but the sha256 as
  a whole is not fully deduplicated, so the whole group's bytes are counted.
  This is the "copy-dup -> FAIL" case.

`closure_bytes` is always the flat sum of `size` over every file row
(duplicates included) — the total bytes a naive `cp -r <root>` would move.

## Gate

```bash
sh scripts/check/check-deployed-closure-dedup.shs [--root <dir>]   # default root: bin/release
sh scripts/check/check-deployed-closure-dedup.shs --selftest
```

Runs the producer, then FAILs on either of two independent conditions:

1. **Physical dedup** — the manifest's `duplicated_bytes` is `> 0`.
2. **Sidecar integrity** — a `*.sha256` row's recorded digest does not match
   the actual sha256 of its companion binary (same directory, `.sha256`
   suffix stripped), or the companion binary is missing. Both the bare-hash
   form (`bootstrap-from-scratch.sh`'s own candidate-digest check expects
   this) and the standard `sha256sum`/`shasum` `"<hash>  <filename>"` form are
   accepted — the sidecars actually deployed under `bin/release` on this host
   use the latter.

`--selftest` runs unconditionally before any real scan and is fatal — a
selftest failure is reported as `ERROR`, never as a fabricated verdict. Six
fixtures:

| fixture | setup | expected |
|---|---|---|
| copy-dup | two files, identical content, distinct inodes (`cp`) | FAIL |
| hardlink-dup | two names, one inode (`ln`), identical content | PASS |
| sidecar mismatch | a `*.sha256` recording a digest that does not match its companion binary | FAIL |
| matching sidecar | a `*.sha256` recording the companion binary's real digest | PASS |
| empty root | a directory with zero regular files | ERROR (exit 2) |
| clean single file | one file, no sidecar, no duplicate | PASS |

Verdict is always the last line of stdout, same convention as sibling
`scripts/check/*.shs` gates:

```
PASS  — <n> file(s) checked (root <path>), 0 duplicated bytes, 0 sidecar mismatch(es)   exit 0
FAIL  — <n> file(s) checked (root <path>), <k> duplicated bytes, <m> sidecar mismatch(es)   exit 1
ERROR — nothing was checked                                                                 exit 2
```

This gate does not attempt to repair a duplicate — choosing which copy to
keep, or whether to hardlink instead, is a deployment-authoring decision.

## Wiring

- Manifest row `push-deployed-closure-dedup` in
  `config/check/must_check_gates.sdn` (`push`, `push_blocking: false`, mode
  `tree`).
- Exact-match dispatch case in `run_manifest_push_gates()`
  (`scripts/check/check-push-must-pass.shs`) for
  `push-deployed-closure-dedup:tree:sh scripts/check/check-deployed-closure-dedup.shs`.
- Advisory step in the `advisory-gates` job of `.github/workflows/repo-hygiene.yml`
  (that job already runs with `continue-on-error: true`).

Landed **advisory**, not blocking, because it is honestly RED on this host
right now (see below) — promote to blocking once the real duplicate is
resolved (either delete the stale backup or hardlink it to the primary).

## This host's manifest (2026-09-12, root = `bin/release`, aarch64)

```
deployed_closure_manifest |schema, root, primary_binary, primary_bytes, closure_bytes, duplicated_bytes, file_count, measured_at_utc|
    "simple.deployed-closure-manifest/v1", "/home/yoon/dev/simple/bin/release", "aarch64-unknown-linux-gnu/simple", 50093192, 255668551, 100186384, 8, "2026-09-12T05:11:13Z"
files |relpath, size, sha256, inode, nlink, kind|
    "aarch64-unknown-linux-gnu/simple", 50093192, "3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef", 19563885, 1, "primary"
    "aarch64-unknown-linux-gnu/simple.bs-lane-2026-09-05-2009", 50093192, "3d120a6f9ab5704b2225654e4f2773cdbdc787108bd21b67aab657ffe3da72ef", 19535722, 1, "other"
    "aarch64-unknown-linux-gnu/simple.pre-sosix-2026-09-05", 154560904, "0eeaf1893db8ee0aaf610cc4b458dd1427fa05f7e25dcb43a6ef98965e4f3c9b", 19535614, 1, "other"
    "aarch64-unknown-linux-gnu/simple_lsp_mcp_server", 145376, "1d176e4dbaebcb616fbc0329b986005dbb668a092c830fbd66440518cba1b79a", 19535749, 1, "primary"
    "aarch64-unknown-linux-gnu/simple_lsp_mcp_server.sha256", 88, "3e63b146505ff0b63c222eae57108724063687e90165a45a44c6f722735df512", 19535750, 1, "sidecar"
    "aarch64-unknown-linux-gnu/simple_mcp_server", 773104, "e44bea904c09f746479f86b9773b4cc2ce4e27ca3a3881fc9b25f9e8d1c64dc7", 19535747, 1, "primary"
    "aarch64-unknown-linux-gnu/simple_mcp_server.sha256", 84, "33a26b7e8c244488d9915f3ed68dc776210d152f81148effa32ce665ec0387e7", 19535748, 1, "sidecar"
    "simple", 2611, "58897c8b2be8b8e24be74500b09d84358d6186a81df6b1ae3b4a1f068309e2a1", 4065111, 1, "wrapper"
```

Headline numbers, stated separately as required:

- **primary binary bytes**: 50,093,192 (`aarch64-unknown-linux-gnu/simple`)
- **deployed closure bytes**: 255,668,551 (sum over all 8 files under `bin/release`)
- **duplicated bytes**: 100,186,384 — `aarch64-unknown-linux-gnu/simple` and
  `aarch64-unknown-linux-gnu/simple.bs-lane-2026-09-05-2009` are byte-identical
  (verified: same sha256) on two **distinct** inodes (19563885 vs 19535722,
  not hardlinked). `check-deployed-closure-dedup.shs --root bin/release` FAILs
  on this host for exactly that pair; sidecar integrity is clean (0
  mismatches). `simple.pre-sosix-2026-09-05` is a different binary (distinct
  sha256) and does not count as a duplicate.

This is a real, unplanted duplicate found on this host's `bin/release` while
building this tool — not a synthetic example. `bin/release` was treated
strictly read-only while producing it (see Instructions above): nothing under
`bin/` was created, modified, linked, or deleted.
