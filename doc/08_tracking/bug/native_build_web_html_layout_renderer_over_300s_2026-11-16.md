# Perf: native-build of simple_web_html_layout_renderer.spl exceeds 300 s

- Date: 2026-11-16
- Status: open
- Area: compiler / native-build per-file compile time (Rust seed lane)

## Symptom

Full K1 CLI native build (`native-build src/app/cli/main.spl ... --source
src/compositions/kernel_llvm --source src/compositions/cuda_disabled --source
src/compiler --source src/app --source src/lib --source src/plugins
--entry-closure`) failed twice with the default per-file limit:

```
src\lib\gc_async_mut\gpu\browser_engine\simple_web_html_layout_renderer.spl: timeout (300s)
```

The second run had a warm cache (`compiled=904 reused=2863 failed=1`), so this
is a real single-file cost, not a cold-cache artifact. The first timeout also
cascaded into 904 `NOT_ATTEMPTED: previous native worker timed out` files.

## Measurement

Rerun with `--timeout 900` succeeded:

```
Build complete: 4 compiled, 3764 cached, 0 failed
Time: 558.3s compile + 63.5s link = 621.8s total
```

The renderer was the only file that had not compiled before; the 558.3 s
compile phase covered 4 files. native-build prints no per-file time, so the
renderer cost is >300 s (measured twice) and at most 558 s. The file has 3083
lines. Host: shared Windows box, seed
`C:/dev/wt/sqlcov-20261114/build/nb/seed-vtable.exe`.

Against the "first object in 10 s" target this is roughly 30-55x over.

## Next

- Add a per-file timing line to native-build output so the cost is measurable.
- Profile which HIR/MIR phase dominates for this file (size alone does not
  explain it; other 3k-line files compile far faster).
- Workaround for full-CLI lanes: pass `--timeout 900`.
