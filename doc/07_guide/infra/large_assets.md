# Large Assets (no Git LFS)

Owner policy: the repo does **not** use Git LFS and does not commit large
binaries. `.gitattributes` has no `filter=lfs` rules; images are plain git blobs
marked `binary`.

An asset too large (or not owned) to commit is instead:

1. listed in `config/assets/large_assets.sdn` (`path, url, sha256, size`; prefer
   an upstream URL, GitHub media URLs pinned to a commit sha only when no
   upstream exists),
2. gitignored by exact path in `.gitignore`,
3. materialised by `sh scripts/setup/fetch-large-assets.shs` (download to temp,
   sha256 + size verify, atomic `mv`; idempotent).

```bash
sh scripts/setup/fetch-large-assets.shs            # fetch missing / mismatched
sh scripts/setup/fetch-large-assets.shs --check    # verify only, no network
sh scripts/setup/fetch-large-assets.shs --selftest # offline fixture test
```

`GITHUB_TOKEN`, if set, is sent as an auth header. Current entries: the 37
Tauri shell icons under `tools/tauri-shell/src-tauri/` (former LFS pointers).
