# JIT text-return extern segfault

## Status

**Resolved — 2026-05-29.**

The refreshed root cause is not the extern return itself. The failing physical
NVMe checker path reached `body.len().to_text()`: MIR lowered `.to_text()` as a
primitive builtin method, but the Cranelift builtin maps only routed
`to_string`/`str` to `rt_to_string`. The JIT then fell through method-call
resolution with an untyped/incorrect virtual register and segfaulted.

This repair is in the Rust seed JIT layer because there is no parallel pure
Simple implementation for Cranelift method-call lowering. Pure Simple remains
the primary system; this patch only keeps the seed backend aligned with the
Simple language surface.

Fixed files:

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs`
- `src/compiler_rust/compiler/src/codegen/instr/calls.rs`
- `src/compiler_rust/compiler/src/codegen/instr/core.rs`
- `src/compiler_rust/compiler/src/codegen/instr/body.rs`
- `src/compiler_rust/compiler/src/mir/lower/tests/branch_coverage/calls.rs`

`bin/simple` was rebuilt from the fixed Rust seed and refreshed from
`src/compiler_rust/target/bootstrap/simple` on 2026-05-29.

## Reproduction

```bash
cat > /tmp/simple_jit_text_extern_probe.spl <<'SPL'
extern fn rt_file_read_text(path: text) -> text

fn main() -> i64:
    val body = rt_file_read_text("/tmp/missing") ?? ""
    print "len=" + body.len().to_text()
    0
SPL

bin/simple run /tmp/simple_jit_text_extern_probe.spl
```

Observed on 2026-05-28: `bin/simple` exits 139 with `Segmentation fault`.
`SIMPLE_EXECUTION_MODE=interpret bin/simple run ...` exits without crashing.

The same class of crash is triggered by `rt_cli_get_args()` and
`main(args: [text])`, so JIT argument-vector/text-return handling is suspect.

Follow-up isolation on 2026-05-28 showed one serial-checker crash class was the
Cranelift vreg type map losing `text` for string constants and known text-return
SFFI calls. That caused text equality to fall through to the generic native
equality path and segfault on JIT heap strings. A second still-active trigger on
2026-05-29 was `.to_text()` missing from the JIT builtin method maps.

The minimized default-JIT crash was:

```spl
fn main() -> i64:
    val n = 0
    print n.to_text()
    0
```

## Impact

The checked-in `bin/simple` no longer shows the crash. The physical NVMe wrapper
no longer sets `SIMPLE_EXECUTION_MODE=interpret`; it runs the checker through the
CLI-capable `bin/simple` default. A synthetic invalid serial log now exits with a
normal validation failure:

```text
physical_nvme serial_log=/tmp/simple_nvme_serial.HSZrKZ.log reason=missing-physical-nvme-marker:storage_provider=simple-driver
rc=1
```

## Acceptance

- The probe above exits without a signal in the default `bin/simple run` lane.
- The serial checker can run without `SIMPLE_EXECUTION_MODE=interpret`.
- Existing serial checker SPipe coverage remains green.

Verified:

```bash
cargo test -p simple-compiler primitive_to_text_method_call_is_builtin_qualified -- --nocapture
cargo test -p simple-compiler build_vreg_types -- --nocapture
bin/simple run /tmp/jit_text_07.spl
bin/simple run /tmp/simple_jit_text_extern_probe.MG9fAq.spl
SIMPLE_LIB=src bin/simple test test/unit/app/simpleos_nvme_serial_check_spec.spl --mode=interpreter --clean
sh scripts/os/run_simpleos_physical_nvme_perf.shs --serial-log /tmp/simple_nvme_serial.HSZrKZ.log --validate-log-only
```
