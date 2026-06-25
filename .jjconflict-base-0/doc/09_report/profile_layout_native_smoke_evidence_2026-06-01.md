# Profile Layout Native Smoke Evidence - 2026-06-01

Scope: pure-Simple BOLT-like profile layout path on Linux x86-64.

Commit under test: `8a65c51237` plus the native symbol-order evidence
checkpoint in this worktree.

Command:

```bash
SIMPLE_LIB=/tmp/simple-pgo-evidence/src \
  /home/ormastes/dev/pub/simple/src/compiler_rust/target/bootstrap/simple \
  test /tmp/simple-pgo-evidence/test/03_system/app/optimize/feature/profile_layout_native_smoke_spec.spl \
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

## Representative Full-Flow Evidence

Scope: generated-C representative workload with real Simple-owned native
counters, runtime snapshot import, `.sprof` generation, layout-map generation,
native rebuild, final symbol-order proof, and before/after measurement.

Representative profile artifact directory:
`/tmp/simple_profile_layout_representative_spec_2619277`.

Profile snapshot and `.sprof` import:

```text
snapshot_status=valid
sprof_records=15
function;key=c:rare:entry;count=0
function;key=c:parse:entry;count=20
function;key=c:dispatch:entry;count=200
function;key=c:main:entry;count=1
```

Native layout and non-profile boundary:

```text
generated order file:
_ZL8dispatchv
_ZL5parsev
_ZL4rarev

optimized nm -an order:
_ZL8dispatchv>_ZL5parsev>_ZL4rarev

non_profile_counter_symbol_count=0
```

Before/after native measurement:

```text
baseline_ms_50=146
optimized_ms_50=147
baseline_size=16112
optimized_size=6608
```

Interpretation:

- The representative path now proves the full requested chain from native
  profile counters through `.sprof`, layout map, native rebuild, final symbol
  order, and measured before/after runtime/size.
- Runtime is effectively neutral on this small process-launch workload, so this
  report is evidence of the full flow and not a speedup claim. The size delta is
  favorable because the optimized rebuild uses the `lld` symbol-order lane.
