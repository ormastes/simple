# Cranelift AOT constructor rejects aggressive ISA setting

Status: default-optimization Cranelift hello passes with the fixed experimental
producer; full compiler admission remains a separate pending gate.

The experimental compiler produced from `eecd0d7c0de` rejects even
`src/compiler/bootstrap_admission/hello_world.spl` on Cranelift. LLVM hello and
the loader succeed. The retained session diagnostic hides the underlying error
behind an enum address.

Debugger evidence under
`/home/yoon/dev/phase2-six-results-20261011/cranelift-hello-diagnosis/` establishes:

- `gdb-provider.log`: the original error is `Failed to create Cranelift AOT module`.
- `gdb-constructor.log`: target `aarch64-unknown-linux-gnu`, CPU `generic`, ISA
  optimization value `3`; the constructor returns zero.
- `gdb-constructor-opt2.log`: numeric `--opt-level 2` still passes value `3`;
  the feature-string length is correctly zero. The earlier constructor log's
  ninth-argument length was read at the wrong stack offset and is not evidence
  of a feature-string defect.

The Rust provider's `cranelift_opt_setting` accepts only `0` (none), `1`
(speed-and-size), and `2` (speed). Simple's `cranelift_isa_opt_level_v2` incorrectly
mapped Aggressive to the unsupported value `3`. Map Aggressive to the maximum
supported ISA setting `2`, retaining the aggressive MIR optimization pipeline.
LLVM keeps its separate O3 mapping. No Rust provider semantics are changed.

The focused bootstrap CLI's `focused_native_build_opt_level` currently accepts
the words `none`, `basic`, and `standard`; unrecognized values, including numeric
`2`, fall back to `3`. The supported source-level spelling is
`--opt-level standard`, but a native hello attempt with that spelling also
failed with the outer session enum error. It is not a verified workaround.
Its exact inner error has not yet been inspected. The numeric spelling mismatch
is a separate CLI defect and must not be described as a second provider failure.

The ordinary default, numeric `2`, and word `standard` attempts are retained
under `experimental-c486-hello-loader/cranelift/hello`, `hello-opt2`, and
`hello-standard` respectively. None is a native acceptance PASS. Further flag
guessing stopped after these bounded variants.

Regression: `test/01_unit/compiler/backend/cranelift_opt_setting_spec.spl`
checks aggressive/speed -> 2, none -> 0, size -> 1, and unsupported basic -> -1.
Existing LLVM optimization specs continue to require Aggressive -> O3.

Native evidence: source revision `6bffb3135df3e938a39f5e3dba13e62cde297ce1`,
producer SHA-256 `54f23cb2274e43f781138a7c110ebcd3a421fb958337e5624d615af6a7fe9da3`.
The default-optimization hello build exits 0 and its executable prints exactly
`hello\n` with exit 0. Receipt:
`/home/yoon/dev/phase2-six-results-20261011/cycle3-hello-loader/cranelift/hello/result.json`.
This exercises the previously rejected default request without an optimization
override. The helper unit spec has not been separately executed; do not equate
the native smoke evidence with a full unit-suite or compiler-admission PASS.
