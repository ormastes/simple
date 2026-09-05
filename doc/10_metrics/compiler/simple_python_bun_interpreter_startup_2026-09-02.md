# Simple, Python, and Bun Interpreter Startup — 2026-09-02

## Verdict

`bin/simple run` cannot currently be benchmarked: the admitted self-hosted binary exits 1 with `error: unknown command 'run'` before loading either fixture. Python and Bun rows are valid. Simple timings below measure rejected CLI startup only and are not interpreter results or suitable for a speed ratio.

## Environment

- Host: Darwin 25.5.0 arm64
- Repository revision: `c846dc3c074d03392b7f2041fa7e74290a67a925`
- Simple launcher: `/Users/ormastes/simple/bin/simple`, SHA-256 `d9345e7439b64fa3e882f85a28bca8ccda5cea041f26e3efafd211fba6172b15`
- Admitted Simple binary: `/Users/ormastes/simple/bin/release/aarch64-apple-darwin-macho/simple`, SHA-256 `1860830a88ac901b3a608efe428ed1d70c18eaa23bc81fbfeb9a8c757afc6164`, `simple-bootstrap 1.0.0-beta`
- Python: `/opt/homebrew/Cellar/python@3.14/3.14.3_1/Frameworks/Python.framework/Versions/3.14/bin/python3.14`, SHA-256 `cbf84109626aa1013bbe408fbb9590bd0f1c1548f038b2221c6b8b87de26ca43`, Python 3.14.3
- Bun: `/opt/homebrew/Cellar/bun/1.3.14/bin/bun`, SHA-256 `fb46ac6497104821512b67a3b3157c9fbbab8a99e311fb38da5b7039a373d860`, Bun 1.3.14

## Method

- Each workload used a new isolated temporary fixture directory.
- Each row used a separate process with daemon reuse disabled for Simple.
- The first invocation is labeled cold; the following 15 invocations form the warm sample.
- Wall time surrounds `/usr/bin/time -l`; RSS is its maximum-resident-set-size value.
- p95 uses nearest-rank selection over the 15 warm samples.
- No native compilation, daemon reuse, filesystem cache purge, or cross-runtime preloading was used.
- Output was captured and SHA-256 checked on every invocation.

## Results

| Runtime/workload | Cold ms | Warm p50 ms | Warm p95 ms | Max RSS MiB | Exit | Output SHA-256 |
|---|---:|---:|---:|---:|---:|---|
| Simple no-op (rejected) | 216.76 | 21.89 | 24.86 | 25.31 | 1 | `070abf034736feadba820e4fc3f439613705149b71274ca1504eb636cfdabf97` |
| Simple hello (rejected) | 21.67 | 21.14 | 22.27 | 25.30 | 1 | `070abf034736feadba820e4fc3f439613705149b71274ca1504eb636cfdabf97` |
| Python no-op | 26.90 | 26.08 | 28.95 | 14.58 | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Python hello | 24.18 | 25.89 | 27.02 | 14.66 | 0 | `5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03` |
| Bun no-op | 159.42 | 17.15 | 19.42 | 24.14 | 0 | `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855` |
| Bun hello | 33.88 | 18.62 | 19.86 | 26.03 | 0 | `5891b5b522d5df086d0ff0b110fbd9d21bb4fc7163af34d08286a2e846f6be03` |

The Simple output checksum is the checksum of `error: unknown command 'run'\n`, not workload output. The valid hello checksum for Python and Bun corresponds to `hello\n`.

## Interpretation

- Bun warm startup is about 7–9 ms faster than Python on these fixtures.
- No Simple/Python or Simple/Bun performance comparison is valid until an admitted full CLI exposes `run` and actually executes the fixtures.
- The blocker agrees with the bootstrap provenance evidence: the admitted artifact is a bootstrap CLI rather than the Stage4 full CLI.

## Required Follow-up

After an admitted Stage4 full CLI is available, rerun this exact harness once with the same fixture contents, repetition count, daemon policy, checksum checks, and RSS collection. Do not reuse the rejected Simple rows as a baseline.
