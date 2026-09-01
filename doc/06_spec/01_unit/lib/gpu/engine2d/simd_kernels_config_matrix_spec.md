# simd_kernels_config_matrix_spec

> engine2d SIMD kernels — 6-config shared test matrix

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simd_kernels_config_matrix_spec

engine2d SIMD kernels — 6-config shared test matrix

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

engine2d SIMD kernels — 6-config shared test matrix

One shared test body runs across all six CPU configs (x86_64, aarch64,
riscv64 — each scalar and SIMD), plus config-specific assertions per lane.
Host hardware fixes which lane executes natively; every lane's pure-Simple
branches (level texts, evidence validity, scalar/simd parity) are still
exercised here so CPU-specific branch coverage does not depend on the host.

Shared-body pattern: configs are data, the body is one function — see
.claude/skills/spipe.md § "Config-variable shared tests".

## Scenarios

### engine2d 6-config shared kernel matrix

#### shared body holds bit-exact scalar parity in every config lane

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- shared body holds bit-exact scalar parity in every config lane
   - Expected: shared_kernel_body(cfg) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shared body holds bit-exact scalar parity in every config lane")
for cfg in all_configs():
    expect(shared_kernel_body(cfg)).to_equal("")
```

</details>

#### each config maps level to the right arch and feature text

- each config maps level to the right arch and feature text
   - Expected: cfg.level.arch_text() equals `cfg.arch`
   - Expected: cfg.level.feature_text() equals `cfg.feature`
   - Expected: cfg.level.arch_text() equals `unknown`
   - Expected: cfg.level.feature_text() equals `scalar`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("each config maps level to the right arch and feature text")
for cfg in all_configs():
    if cfg.simd:
        expect(cfg.level.arch_text()).to_equal(cfg.arch)
        expect(cfg.level.feature_text()).to_equal(cfg.feature)
    else:
        expect(cfg.level.arch_text()).to_equal("unknown")
        expect(cfg.level.feature_text()).to_equal("scalar")
```

</details>

#### covers every SimdLevel text arm including Avx512 and Sse42

- covers every SimdLevel text arm including Avx512 and Sse42
   - Expected: SimdLevel.None_.to_text() equals `None`
   - Expected: SimdLevel.Sse42.to_text() equals `SSE4.2`
   - Expected: SimdLevel.Avx2.to_text() equals `AVX2`
   - Expected: SimdLevel.Avx512.to_text() equals `AVX-512`
   - Expected: SimdLevel.Neon.to_text() equals `NEON`
   - Expected: SimdLevel.Rvv.to_text() equals `RVV`
   - Expected: SimdLevel.Sse42.arch_text() equals `x86_64`
   - Expected: SimdLevel.Avx512.arch_text() equals `x86_64`
   - Expected: SimdLevel.Avx512.feature_text() equals `avx2`
   - Expected: SimdLevel.Sse42.feature_text() equals `sse42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("covers every SimdLevel text arm including Avx512 and Sse42")
expect(SimdLevel.None_.to_text()).to_equal("None")
expect(SimdLevel.Sse42.to_text()).to_equal("SSE4.2")
expect(SimdLevel.Avx2.to_text()).to_equal("AVX2")
expect(SimdLevel.Avx512.to_text()).to_equal("AVX-512")
expect(SimdLevel.Neon.to_text()).to_equal("NEON")
expect(SimdLevel.Rvv.to_text()).to_equal("RVV")
expect(SimdLevel.Sse42.arch_text()).to_equal("x86_64")
expect(SimdLevel.Avx512.arch_text()).to_equal("x86_64")
expect(SimdLevel.Avx512.feature_text()).to_equal("avx2")
expect(SimdLevel.Sse42.feature_text()).to_equal("sse42")
```

</details>

### cpu_simd_required_evidence_valid per config

#### accepts genuine SIMD evidence in each simd lane

- accepts genuine SIMD evidence in each simd lane
   - Expected: cpu_simd_required_evidence_valid(ev, cfg.arch, 0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts genuine SIMD evidence in each simd lane")
for cfg in all_configs():
    if cfg.simd:
        val ev = make_evidence(cfg, true, true, 4)
        expect(cpu_simd_required_evidence_valid(ev, cfg.arch, 0)).to_equal(true)
```

</details>

#### rejects on wrong expected arch

- rejects on wrong expected arch
   - Expected: cpu_simd_required_evidence_valid(ev, "other_arch", 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects on wrong expected arch")
for cfg in all_configs():
    if cfg.simd:
        val ev = make_evidence(cfg, true, true, 4)
        expect(cpu_simd_required_evidence_valid(ev, "other_arch", 0)).to_equal(false)
```

</details>

#### rejects when kernels did not all execute

- rejects when kernels did not all execute
   - Expected: cpu_simd_required_evidence_valid(ev, cfg.arch, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects when kernels did not all execute")
val cfg = all_configs()[1]
val ev = make_evidence(cfg, false, true, 4)
expect(cpu_simd_required_evidence_valid(ev, cfg.arch, 0)).to_equal(false)
```

</details>

#### rejects when native output diverged from scalar

- rejects when native output diverged from scalar
   - Expected: cpu_simd_required_evidence_valid(ev, cfg.arch, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects when native output diverged from scalar")
val cfg = all_configs()[3]
var ev = make_evidence(cfg, true, false, 4)
expect(cpu_simd_required_evidence_valid(ev, cfg.arch, 0)).to_equal(false)
```

</details>

#### rejects when hit counter never advanced

- rejects when hit counter never advanced
   - Expected: cpu_simd_required_evidence_valid(ev, cfg.arch, 0) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects when hit counter never advanced")
val cfg = all_configs()[5]
var ev = make_evidence(cfg, true, true, 4)
ev.native_simd_hits = 0
ev.native_simd_executed = true
expect(cpu_simd_required_evidence_valid(ev, cfg.arch, 0)).to_equal(false)
```

</details>

#### rejects when any scalar fallback call was observed

- rejects when any scalar fallback call was observed
   - Expected: cpu_simd_required_evidence_valid(ev, cfg.arch, 1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects when any scalar fallback call was observed")
val cfg = all_configs()[1]
val ev = make_evidence(cfg, true, true, 4)
expect(cpu_simd_required_evidence_valid(ev, cfg.arch, 1)).to_equal(false)
```

</details>

### varied-pattern blend parity (native vs scalar)

#### blends a varied translucent pattern identically on native and scalar paths

- blends a varied translucent pattern identically on native and scalar paths
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("blends a varied translucent pattern identically on native and scalar paths")
# Guards the native-vs-scalar blend contract on varied (non-canonical)
# alpha. A divergence on a different input class (iterated const-src
# blending over translucent dst) is tracked in doc/08_tracking/bug/
# engine2d_native_blend_diverges_from_scalar_on_varied_patterns_2026-08-15.md
# The scalar reference is the contract; do not weaken this assertion.
val n: i64 = 64
var dst: [u32] = [0; 64]
var ref_dst: [u32] = [0; 64]
var src: [u32] = [0; 64]
var i: i64 = 0
while i < n:
    # varied alpha/color, incl. translucent dst pixels
    val a = ((i * 37 + 11) % 256) as u32
    val c = ((i * 97 + 5) % 256) as u32
    src[i.to_i32()] = (a << 24) | (c << 16) | ((255u32 - c) << 8) | (a ^ c)
    val da = ((i * 53 + 3) % 256) as u32
    dst[i.to_i32()] = (da << 24) | (c << 8) | 0x40u32
    ref_dst[i.to_i32()] = dst[i.to_i32()]
    i = i + 1
alpha_blend_span(dst, src, 0, n)
_scalar_alpha_blend_span(ref_dst, src, 0, n)
var mismatches: i64 = 0
i = 0
while i < n:
    if dst[i.to_i32()] != ref_dst[i.to_i32()]:
        mismatches = mismatches + 1
    i = i + 1
expect(mismatches).to_equal(0)
```

</details>

#### iterated const-src blends over translucent dst stay bit-identical to scalar

- iterated const-src blends over translucent dst stay bit-identical to scalar
   - Expected: mismatches equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("iterated const-src blends over translucent dst stay bit-identical to scalar")
# Reproducing input class from doc/08_tracking/bug/
# engine2d_native_blend_diverges_from_scalar_on_varied_patterns_2026-08-15.md:
# a constant translucent src blended repeatedly over a varied translucent
# dst (the span-bench pattern). Before the fix the scalar reference lane
# mis-executed the da/dr/dg/db bit ops on the any-typed dst (seed MIR
# unboxed-binop-result bug), diverging from the native kernels on
# 350/640 bench pixels. The scalar formula is the contract; native and
# scalar must agree on every pixel after every iteration.
val n: i64 = 64
var dst: [u32] = [0; 64]
var ref_dst: [u32] = [0; 64]
var src: [u32] = [0; 64]
var i: i64 = 0
while i < n:
    val da = ((i * 61 + 19) % 256) as u32   # includes da < 255 (translucent dst)
    val dr = ((i * 17 + 23) % 256) as u32
    dst[i.to_i32()] = (da << 24) | (dr << 16) | ((255u32 - dr) << 8) | (dr ^ 0x55u32)
    ref_dst[i.to_i32()] = dst[i.to_i32()]
    src[i.to_i32()] = 0x80CC4488u32          # constant translucent src
    i = i + 1
var pass_no: i64 = 0
var mismatches: i64 = 0
while pass_no < 4:
    alpha_blend_span(dst, src, 0, n)
    _scalar_alpha_blend_span(ref_dst, src, 0, n)
    i = 0
    while i < n:
        if dst[i.to_i32()] != ref_dst[i.to_i32()]:
            mismatches = mismatches + 1
        i = i + 1
    pass_no = pass_no + 1
expect(mismatches).to_equal(0)
```

</details>

### scroll region branch edges

#### overshoot delta leaves buffer untouched (rows_to_copy <= 0)

- overshoot delta leaves buffer untouched (rows_to_copy <= 0)
   - Expected: buf[0] equals `0xAAu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("overshoot delta leaves buffer untouched (rows_to_copy <= 0)")
var buf: [u32] = [0xAA; 16]
simd_scroll_region(buf, 4, 0, 0, 4, 4, 5)
simd_scroll_region(buf, 4, 0, 0, 4, 4, -4)
expect(buf[0]).to_equal(0xAAu32)
```

</details>

#### zero delta and empty rect return early

- zero delta and empty rect return early
   - Expected: buf[15] equals `0xBBu32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("zero delta and empty rect return early")
var buf: [u32] = [0xBB; 16]
simd_scroll_region(buf, 4, 0, 0, 4, 4, 0)
simd_scroll_region(buf, 4, 0, 0, 0, 4, 1)
simd_scroll_region(buf, 4, 0, 0, 4, 0, 1)
expect(buf[15]).to_equal(0xBBu32)
```

</details>

### host lane detection

<details>
<summary>Advanced: host resolves to exactly one lane of the matrix</summary>

#### host resolves to exactly one lane of the matrix

- host resolves to exactly one lane of the matrix
   - Expected: ok is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("host resolves to exactly one lane of the matrix")
val level = detect_simd_level()
val arch = level.arch_text()
val ok = (arch == "x86_64" or arch == "aarch64" or
    arch == "riscv64" or arch == "unknown")
expect(ok).to_equal(true)
```

</details>


</details>

#### simd config mode is a known vocabulary value

- simd config mode is a known vocabulary value
   - Expected: known is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("simd config mode is a known vocabulary value")
val mode = simd_config_mode()
val known = (mode == "auto" or mode == "off" or mode == "sse2" or
    mode == "avx2" or mode == "neon" or mode == "rvv")
expect(known).to_equal(true)
```

</details>

#### forced ISA mode forces the reported level (D8 wiring)

- forced ISA mode forces the reported level (D8 wiring)
   - Expected: detect_simd_level().feature_text() equals `sse42`
   - Expected: detect_simd_level().feature_text() equals `avx2`
   - Expected: detect_simd_level().arch_text() equals `aarch64`
   - Expected: detect_simd_level().arch_text() equals `riscv64`
   - Expected: native_pixel_rows_enabled() is false
   - Expected: mode equals `auto`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("forced ISA mode forces the reported level (D8 wiring)")
# Run this spec with SIMPLE_2D_SIMD=sse2|avx2|neon|rvv to drive each
# non-host detection arm on any host; the C kernels still dispatch on
# the real CPU so the shared parity body above stays bit-exact.
val mode = simd_config_mode()
if mode == "sse2":
    expect(detect_simd_level().feature_text()).to_equal("sse42")
elif mode == "avx2":
    expect(detect_simd_level().feature_text()).to_equal("avx2")
elif mode == "neon":
    expect(detect_simd_level().arch_text()).to_equal("aarch64")
elif mode == "rvv":
    expect(detect_simd_level().arch_text()).to_equal("riscv64")
elif mode == "off":
    expect(native_pixel_rows_enabled()).to_equal(false)
else:
    expect(mode).to_equal("auto")
```

</details>

#### forced-level mapper covers every ISA name and rejects non-ISA values

- forced-level mapper covers every ISA name and rejects non-ISA values
   - Expected: _forced_simd_level("sse2") equals `SimdLevel.Sse42`
   - Expected: _forced_simd_level("avx2") equals `SimdLevel.Avx2`
   - Expected: _forced_simd_level("neon") equals `SimdLevel.Neon`
   - Expected: _forced_simd_level("rvv") equals `SimdLevel.Rvv`
   - Expected: _forced_simd_level("auto") equals `SimdLevel.None_`
   - Expected: _forced_simd_level("off") equals `SimdLevel.None_`
   - Expected: _forced_simd_level("bogus") equals `SimdLevel.None_`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("forced-level mapper covers every ISA name and rejects non-ISA values")
expect(_forced_simd_level("sse2")).to_equal(SimdLevel.Sse42)
expect(_forced_simd_level("avx2")).to_equal(SimdLevel.Avx2)
expect(_forced_simd_level("neon")).to_equal(SimdLevel.Neon)
expect(_forced_simd_level("rvv")).to_equal(SimdLevel.Rvv)
expect(_forced_simd_level("auto")).to_equal(SimdLevel.None_)
expect(_forced_simd_level("off")).to_equal(SimdLevel.None_)
expect(_forced_simd_level("bogus")).to_equal(SimdLevel.None_)
```

</details>

#### native rows gate agrees with detected level when mode is not off

- native rows gate agrees with detected level when mode is not off
   - Expected: native_pixel_rows_enabled() is false
   - Expected: native_pixel_rows_enabled() equals `has_simd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("native rows gate agrees with detected level when mode is not off")
if simd_config_mode() == "off":
    expect(native_pixel_rows_enabled()).to_equal(false)
else:
    val level = detect_simd_level()
    val has_simd = level != SimdLevel.None_
    expect(native_pixel_rows_enabled()).to_equal(has_simd)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5a27b61e5294ef0242ae3f116dc53efe7057e4dd1de825fba067a961fb7264f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5a27b61e5294ef0242ae3f116dc53efe7057e4dd1de825fba067a961fb7264f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5a27b61e5294ef0242ae3f116dc53efe7057e4dd1de825fba067a961fb7264f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shared body holds bit-exact scalar parity in every config lane' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'each config maps level to the right arch and feature text' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/engine2d/simd_kernels_config_matrix_spec.spl:112:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'covers every SimdLevel text arm including Avx512 and Sse42' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
