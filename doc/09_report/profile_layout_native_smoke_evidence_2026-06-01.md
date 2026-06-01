# Profile Layout Native Smoke Evidence - 2026-06-01

Scope: pure-Simple BOLT-like profile layout path on Linux x86-64.

Commit under test: `8a65c51237` plus the native symbol-order evidence
checkpoint in this worktree.

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

Native artifacts from `/tmp/simple_profile_layout_native_smoke_spec_2613539`:

```text
baseline_size=15936
optimized_size=6256
non_profile_counter_symbol_count=0
```

Generated-C section map evidence:

```text
SIMPLE_LAYOUT_SECTION_dispatch -> .text.simple.hot.0.dispatch
SIMPLE_LAYOUT_SECTION_parse -> .text.simple.hot.1.parse
SIMPLE_LAYOUT_SECTION_rare -> .text.simple.cold.2.rare
```

Native symbol-order evidence:

```text
generated order file:
_ZL8dispatchv
_ZL5parsev
_ZL4rarev

optimized nm -an:
0000000000001640 t _ZL8dispatchv
0000000000001650 t _ZL5parsev
0000000000001660 t _ZL4rarev
0000000000001760 T main
```

Interpretation:

- The smoke proves the chain from `.sprof` function counts to generated-C
  section map, section attribute application, baseline native binary, optimized
  native binary, runtime measurement, size measurement, and final native symbol
  order through the generated Simple symbol-order file.
- The non-profile baseline binary was inspected with `nm` and contains zero
  `__simple_profile*` counter symbols, preserving the explicit profile-build
  boundary.
- This is a smoke workload, not a release speedup claim. The remaining gate is a
  representative workload report using the same evidence path.
