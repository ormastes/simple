# riscv_rtl_debuggability_spec asserts a lint-clean bundle the generator deliberately never emits

- Status: RESOLVED 2026-08-17 via unblock option (b) — spec rewritten fixture-based, 13/13 GREEN
- Resolution: the spec now builds a known-clean bundle itself (`make_clean_bundle`
  generates the placeholder bundle then patches sidecar observability flags,
  sourceMap + matching `-- source-map:` VHDL header line, runnerSuccessMarkers /
  per-testbench `passMarker` metadata, `report "<marker>"` lines in each
  `tb_*.vhd`, and a >=3-entry reportMarkers list into a self-consistent
  debuggable state). Every mutation case now starts from this clean fixture and
  guards its `.replace()` with `expect(broken == original).to_equal(false)`, so
  the previously vacuous RTLDBG101/003/102 cases are now non-vacuous. The
  generator's placeholder contract is untouched and stays asserted elsewhere.
  Mirror `test/unit/compiler/lint/riscv_rtl_debuggability_spec.spl` synced.
- Found: 2026-08-17
- Spec: `test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl` (mirror: `test/unit/compiler/lint/riscv_rtl_debuggability_spec.spl`)
- Lint under test: `src/compiler/35.semantics/lint/riscv_rtl_debuggability_lint.spl`
- Generator: `src/lib/hardware/fpga_linux/riscv_fpga_linux.spl`

## Symptom

`SIMPLE_TIMEOUT_SECONDS=600 bin/simple test test/01_unit/compiler/lint/riscv_rtl_debuggability_spec.spl`
→ `13 examples, 3 failures` (10 pass). All three are `expected true to equal false`:

- line 30 `accepts clean generated RV64 debug sidecars`
- line 98 `accepts sidecars with non-canonical whitespace`
- line 156 `accepts board boot products manifests with reordered acceptance markers and relaxed spacing`

## Root cause — stale spec, NOT a lint-rule regression

Linting a freshly generated, unmodified bundle already yields 14 findings:

```
RTLDBG002 sidecar/source-map entry counts do not match the VHDL header
RTLDBG101 x6  (fetch/trap/halt/memoryAccess/registerProbes/debugProbes coverage false)
RTLDBG003 x5  (runnerSuccessMarkers disagrees with runnerTestbenches for each tb_*.vhd)
RTLDBG102 x2  (missing declared PASS marker; report markers too thin)
```

The generated sidecar (`rv64/rtl/simple_rv64gc_core.debug.json`) is a documented
placeholder: `"readiness": "contract-not-ready"`, `"reason":
"placeholder-core-no-semantic-rvfi"`, `"sourceMap": []`,
`"runnerSuccessMarkers": {}`, `"reportMarkers": ["GENERATED_RTL_NOT_IMPLEMENTED"]`,
and every `observability.*` flag except `proofFailureReports` set to `false`.

That is intended behaviour, asserted elsewhere and documented:
`src/lib/hardware/fpga_linux/test/riscv_fpga_linux_spec.spl:225,256`,
`src/verification/riscv_product/GENERATED_CONTRACT.md:27`,
`doc/05_design/riscv32_riscv64_fpga_simpleos_production.md:71-72`,
`doc/08_tracking/bug/fpga_linux_no_synthesizable_rv64_core_2026-07-23.md:34`.

The lint is behaving correctly; the spec predates the placeholder generator.

## Secondary finding — the 10 passing examples are partly vacuous

Cases like `emits RTLDBG101 when observability coverage is incomplete` flip
`"registerProbes": true` → `false`, but the generated sidecar already has it
`false`, so the `.replace()` is a no-op and the assertion passes on a finding
that would fire anyway. Same for several RTLDBG003 cases. Any rewrite must fix
this too, not only the three reds.

## Unblock condition

Either (a) the generator emits a real, debuggable RV64 core (blocked on
`fpga_linux_no_synthesizable_rv64_core_2026-07-23.md`), or (b) the spec is
rewritten to build its own known-clean sidecar fixture instead of relying on
`generate_default_riscv_fpga_rtl_bundle`, so that "clean" is a fixture property
rather than a generator promise the design explicitly refuses to make.

Deliberately NOT done: relaxing the assertions to expect the placeholder
findings. That would hide the real gap (per `.claude/rules/testing.md`).
