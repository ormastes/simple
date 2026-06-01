# Profile Layout Native Smoke Evidence - 2026-06-01

Scope: pure-Simple BOLT-like profile layout path on Linux x86-64.

Commit under test: `7b4c3b657b` plus the native smoke entrypoint in this
checkpoint.

Command:

```bash
SIMPLE_LIB=/tmp/simple-pgo-evidence/src \
  /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple \
  test /tmp/simple-pgo-evidence/test/system/app/optimize/feature/profile_layout_native_smoke_spec.spl \
  --mode=interpreter --fail-fast
```

Result:

```text
profile_layout_native_smoke_spec.spl: 2 passed
```

Native artifacts from `/tmp/simple_profile_layout_native_smoke_spec_2599942`:

```text
baseline_ms_200=507
optimized_ms_200=431
speedup_pct=14
baseline_size=15936
optimized_size=16048
size_delta=112
```

Generated-C section map evidence:

```text
SIMPLE_LAYOUT_SECTION_dispatch -> .text.simple.hot.0.dispatch
SIMPLE_LAYOUT_SECTION_parse -> .text.simple.hot.1.parse
SIMPLE_LAYOUT_SECTION_rare -> .text.simple.cold.2.rare
```

Interpretation:

- The smoke proves the chain from `.sprof` function counts to generated-C
  section map, section attribute application, baseline native binary, optimized
  native binary, runtime measurement, and size measurement.
- This is a smoke workload, not a release speedup claim. The remaining gate is a
  representative workload report using the same evidence path.
