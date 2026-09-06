# Vendored: microui (reference fixture dependency, A09)

Third-party source. Per CLAUDE.md Owned-Code Scope this directory is **not owned
code**: it is excluded from code counts, reviews and verification scans unless
explicitly requested. Do not edit these files; re-vendor from upstream instead.

upstream_url: https://github.com/rxi/microui
pinned_commit: 0850aba860959c3e75fb3e97120ca92957f9d057
vendored_utc: 2026-09-06
license: MIT (LICENSE, copied verbatim below)

## Files taken

Only the two library translation units are vendored. The upstream `demo/`,
`doc/` and `README.md` trees are deliberately NOT copied: they are unused here
and adding ~dozens of files would push against the repo tree-size guard band
(`scripts/check/check-tree-size-push.shs`).

| file | upstream path |
|---|---|
| `microui.c` | `src/microui.c` |
| `microui.h` | `src/microui.h` |
| `LICENSE`   | `LICENSE` |

## License (verbatim, upstream `LICENSE`)

```
Copyright (c) 2024 rxi

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
