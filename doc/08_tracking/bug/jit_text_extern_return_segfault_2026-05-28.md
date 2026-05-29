# JIT text-return extern segfault

## Status

Mitigated in source; release binary refresh still required.

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

Follow-up isolation on 2026-05-28 showed the immediate serial-checker crash was
the Cranelift vreg type map losing `text` for string constants and known
text-return SFFI calls. That caused text equality to fall through to the generic
native equality path and segfault on JIT heap strings. Source fix:

- `src/compiler_rust/compiler/src/codegen/instr/body.rs` now records
  `ConstString`, `rt_env_get`, `rt_get_env`, and `rt_file_read_text*` result
  types.
- `src/compiler_rust/compiler/src/codegen/instr/core.rs` now uses
  `rt_string_eq` for known text equality without the prior inline CFG fast path.

## Impact

The checked-in `bin/simple` / release binary may still show the crash until it
is rebuilt from the fixed Rust sources. The production physical NVMe wrapper
still sets `SIMPLE_EXECUTION_MODE=interpret` for this checker as a conservative
release-lane guard until the release binary is refreshed and verified.

## Acceptance

- The probe above exits without a signal in the default `bin/simple run` lane.
- The serial checker can run without `SIMPLE_EXECUTION_MODE=interpret`.
- Existing serial checker SPipe coverage remains green.
