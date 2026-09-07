# `test/05_perf/ui_slim/ref/vendor/` — vendored third-party sources

**External path.** Everything under this directory is upstream third-party
source, vendored verbatim for reference-only benchmark fixtures. Per CLAUDE.md
§ Owned-Code Scope it must be **excluded from owned-code counts, reviews,
verification scans and lint**. It is not product code and is never linked into
any Simple binary.

Adding this prefix to CLAUDE.md's external-path list is an A00 integration
decision — this work package does not own CLAUDE.md.

## Allowed entries

| Entry | Kind | Notes |
|---|---|---|
| `FILE.md` | manifest | this file (owned, not vendored) |
| `termbox2.pin` | pin | upstream commit sha read by `../termbox2/build.shs` (owned) |
| `termbox2/` | vendored | see below (owned by A08) |
| `nuklear/`, `microui/` | vendored | GUI references, work package **A09** — pins and licenses are documented by A09, not here |

## termbox2

| Field | Value |
|---|---|
| Upstream | https://github.com/termbox/termbox2 |
| Pinned commit | `cdf62e9990d8b200768780080fb10a4e2f680051` |
| Commit date | 2026-09-02 |
| Fetched | 2026-09-06 via `git clone --depth 1`; `.git` removed |
| License | MIT — `termbox2/LICENSE`, copied verbatim from upstream |
| `termbox2.h` sha256 | `edfa22b227c1a82a4a33ffcd1699b2903a7bff46075a210be2e8849127c63f62` |

**Subset of the pinned revision.** Only `termbox2.h`, `LICENSE`, `README.md`,
`.clang-format` and `.gitattributes` are kept. `demo/`, `tests/`, `Makefile`
and `codegen.sh` were removed — the fixture compiles the single header with
`-DTB_IMPL` and needs nothing else. Nothing in the retained files was edited.

## ncursesw is NOT vendored

The ncursesw fixture links the **system-installed** Homebrew build
(`/opt/homebrew/opt/ncurses`, ncursesw 6.6.20251230, wide-char). No ncurses
source lives in this tree. See `doc/07_guide/ui/ui_slim_c_references.md`.
