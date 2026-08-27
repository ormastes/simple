# simplebox_build_spec

> simplebox build wiring — native-build cross-compiles simplebox for a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simplebox_build_spec

simplebox build wiring — native-build cross-compiles simplebox for a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tools/simplebox_build_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

simplebox build wiring — native-build cross-compiles simplebox for a
freestanding SimpleOS target into the rootfs (where image_builder packs it as
/bin/simplebox).

Locks the build half of the userland->image wire: the command compiles the
libc-consuming entry with its full import closure (--entry-closure pulls the
pure-Simple libc), links against the SimpleOS sysroot linker script, and outputs
to the rootfs path the image builder reads.

## Scenarios

### simplebox build wiring

#### native-build command for a freestanding simpleos target

#### uses the llvm backend

- uses the llvm backend
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `--backend`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses the llvm backend")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("--backend")).to_equal(true)
```

</details>

#### passes the freestanding target triple

- passes the freestanding target triple
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `x86_64-unknown-none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes the freestanding target triple")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("x86_64-unknown-none")).to_equal(true)
```

</details>

#### compiles the full import closure (pulls the pure-Simple libc)

- compiles the full import closure (pulls the pure-Simple libc)
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `--entry-closure`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles the full import closure (pulls the pure-Simple libc)")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("--entry-closure")).to_equal(true)
```

</details>

#### compiles the libc-consuming simplebox entry

- compiles the libc-consuming simplebox entry
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `src/os/tools/simplebox/simplebox_main.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compiles the libc-consuming simplebox entry")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("src/os/tools/simplebox/simplebox_main.spl")).to_equal(true)
```

</details>

#### links against the SimpleOS sysroot linker script

- links against the SimpleOS sysroot linker script
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `--linker-script`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("links against the SimpleOS sysroot linker script")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("--linker-script")).to_equal(true)
```

</details>

#### emits to the rootfs path the image builder packs

- emits to the rootfs path the image builder packs
   - Expected: simplebox_native_build_cmd("x86_64-unknown-none") contains `build/os/rootfs/bin/simplebox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits to the rootfs path the image builder packs")
expect(simplebox_native_build_cmd("x86_64-unknown-none").contains("build/os/rootfs/bin/simplebox")).to_equal(true)
```

</details>

#### output path matches the image pack source

#### is the rootfs bin path

- is the rootfs bin path
   - Expected: simplebox_output_path() equals `build/os/rootfs/bin/simplebox`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is the rootfs bin path")
expect(simplebox_output_path()).to_equal("build/os/rootfs/bin/simplebox")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ee1b813e7ea96f5dbca065f487a80a12d18f4773eb1851094d65373fa652794c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee1b813e7ea96f5dbca065f487a80a12d18f4773eb1851094d65373fa652794c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee1b813e7ea96f5dbca065f487a80a12d18f4773eb1851094d65373fa652794c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/tools/simplebox_build_spec.spl
mirror: doc/06_spec/01_unit/os/tools/simplebox_build_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tools/simplebox_build_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tools/simplebox_build_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tools/simplebox_build_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the llvm backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_build_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes the freestanding target triple' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tools/simplebox_build_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compiles the full import closure (pulls the pure-Simple libc)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
