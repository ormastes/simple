# duplicate-check cosine: native build peaks at 12 GB (seed 2.4 GB)

- Status: open
- Date: 2026-11-18
- Component: src/compiler/90.tools/duplicate_check (cosine mode), native runtime

## Measurements (Windows x86_64, `src/runtime --include-c --exclude vendor`)

| build | mode | wall | peak working set |
|---|---|---|---|
| seed interpreter | token | 266 s | 536 MB |
| native (seed codegen, SIMPLE_NATIVE_BUILD_RUST=1) | token | 112 s | 505 MB |
| seed interpreter | cosine | 551 s | 2.3 GB |
| native | cosine | 328 s | **12.0 GB** |

Group output is identical between seed and native (token 21, cosine 230 groups),
so the algorithm is the same; the extra ~9.7 GB is native-only.

## Suspected cause

`_Detector/similarity_grouping.spl` builds per-block feature vectors,
signature strings (`feature_signature(..., 5)` split per bucket) and a
`{text: [i64]}` adjacency dict with string keys. Under the native runtime these
temporaries appear to be retained (no release of intermediate text/array
values), while the seed interpreter frees them.

## Repro

```
SIMPLE_NATIVE_BUILD_RUST=1 bin/simple.exe native-build <checker main> -o dupcheck.exe
dupcheck.exe src/runtime --include-c --mode cosine --exclude vendor -q
```
Sample PeakWorkingSet64 every 200 ms.

## Also observed

Seed-interpreted cosine is ~1.7x slower than native and was seen to stall
on the full tree earlier in the session; the native build is the usable path.
