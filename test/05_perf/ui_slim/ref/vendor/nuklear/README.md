# Vendored: Nuklear (reference fixture dependency, A09)

Third-party source. Per CLAUDE.md Owned-Code Scope this directory is **not owned
code**: it is excluded from code counts, reviews and verification scans unless
explicitly requested. Do not edit these files; re-vendor from upstream instead.

upstream_url: https://github.com/Immediate-Mode-UI/Nuklear
pinned_commit: e3e18dc1e4d3de935095d372aaa211f12183befb
vendored_utc: 2026-09-06
license: MIT OR Unlicense (dual, licensee's choice — LICENSE copied verbatim below)

## Files taken

Nuklear is a single-header library. Only the amalgamated header is vendored;
the upstream `src/`, `demo/`, `example/` and `extra_font/` trees (hundreds of
files, backends and font blobs) are deliberately NOT copied — they are unused by
the headless fixture and would push against the repo tree-size guard band
(`scripts/check/check-tree-size-push.shs`).

| file | upstream path |
|---|---|
| `nuklear.h` | `nuklear.h` |
| `LICENSE`   | `LICENSE` |

## License (verbatim, upstream `LICENSE`)

```
License

This software is available under 2 licenses -- choose whichever you prefer.

ALTERNATIVE A - MIT License
Copyright (c) 2017 Micha Mettke
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

ALTERNATIVE B - Public Domain (www.unlicense.org)
This is free and unencumbered software released into the public domain.
Anyone is free to copy, modify, publish, use, compile, sell, or distribute this
software, either in source code form or as a compiled binary, for any purpose,
commercial or non-commercial, and by any means.
In jurisdictions that recognize copyright laws, the author or authors of this
software dedicate any and all copyright interest in the software to the public
domain. We make this dedication for the benefit of the public at large and to
the detriment of our heirs and successors. We intend this dedication to be an
overt act of relinquishment in perpetuity of all present and future rights to
this software under copyright law.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN
ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
```
