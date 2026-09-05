# Third-Party Notices

This repository is primarily distributed under the Apache License 2.0 in
[LICENSE](LICENSE).

Some shipped source files vendor third-party code. Those files keep their
original upstream notices and SPDX identifiers. This file records the bundled
components that are intended to ship with Simple distributions.

## Bundled Components

| Component | Paths | Upstream | License Choice Used By Simple |
| --- | --- | --- | --- |
| miniaudio | `src/runtime/miniaudio.h` | https://github.com/mackron/miniaudio | MIT No Attribution (MIT-0) |
| stb_image | `src/runtime/stb_image.h` | https://github.com/nothings/stb | MIT |
| stb_truetype | `src/runtime/stb_truetype.h` | https://github.com/nothings/stb | MIT |
| liburing subset | `src/runtime/vendor/liburing/` | https://github.com/axboe/liburing | MIT for dual-licensed liburing files; `io_uring.h` keeps its upstream SPDX identifier `(GPL-2.0 WITH Linux-syscall-note) OR MIT` |

## Distribution Notes

- Keep this file together with [LICENSE](LICENSE) when redistributing source or packaged builds.
- Keep the embedded headers and SPDX notices intact in vendored files.
- `src/runtime/vendor/liburing/include/liburing/io_uring.h` is carried with its original upstream SPDX identifier because it mirrors kernel interface definitions. The vendored copy remains dual-licensed exactly as marked in the file.
- Release bundles should exclude development-only caches and downloaded runtimes such as `src/app/vscode_extension/node_modules/`, `src/app/vscode_extension/.vscode-test/`, and `src/compiler_rust/target/`.

## Development-Only Local Artifacts

Some checked-in or workspace-populated paths may contain third-party binaries or downloaded test assets used only for local development. They are not part of the intended bootstrap/full release payloads.

- `src/app/vscode_extension/node_modules/`
- `src/app/vscode_extension/.vscode-test/`
- `src/compiler_rust/target/`
- `build/`

Treat those as upstream-controlled artifacts with their own licenses and do not assume they are covered solely by the root MIT license.

## MIT License Text

The following MIT text covers the vendored files above where the file header or
upstream project offers MIT as a valid license option.

```text
MIT License

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

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

## MIT-0 / No-Attribution Text For miniaudio

`src/runtime/miniaudio.h` offers public-domain dedication or MIT No
Attribution. Simple relies on the MIT No Attribution option.

```text
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```
