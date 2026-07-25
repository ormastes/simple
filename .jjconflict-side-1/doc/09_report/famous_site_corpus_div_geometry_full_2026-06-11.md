# Famous-Site Corpus Div Geometry Full Evidence

- status: pass
- corpus rows: 132
- selected rows: 132
- matched rows: 132
- mismatched rows: 0
- missing metrics: 0
- viewport: 160x120
- command mode: single Simple process
- blur/tolerance used: false

This evidence compares stored Chromium DOM metrics against Pure Simple Draw IR
for the deterministic famous-site corpus div box in one aggregate command. It
checks exact border-box geometry, background color, and fixture text through
structural reports. It does not use blur, downscaling, pixel tolerance, copied
Chromium pixels, or text antialiasing normalization.

## Command

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple \
  run src/app/wm_compare/site_corpus_div_geometry_summary_cli.spl \
  0 0 160 120 /tmp/full_div_geometry_limit0.sdn 132
```

## Output

```text
status=pass
offset=0
limit=0
expected=132
viewport_width=160
viewport_height=120
report_path=/tmp/full_div_geometry_limit0.sdn
```

## Regression Spec

```sh
SIMPLE_LIB=src /home/ormastes/dev/pub/simple/bin/simple \
  test test/03_system/gui/wm_compare/structural_layout_report_spec.spl \
  --mode=interpreter --clean --format json
```

Observed result: `11` passed, `0` failed.
