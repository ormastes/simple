# JIT text-return extern segfault

## Status

**Blocked — binary rebuild required.**

The Rust source fix is committed (commit `33a854f608`, 2026-05-29 08:21 UTC).
The checked-in `bin/simple` binary was built at 2026-05-29 05:33 UTC — **2h 48min
before that commit** — so it does not contain the fix.

This is not fixable in pure Simple (`.spl`). The vreg type-map that loses `text`
for string constants and known text-return SFFI calls lives entirely in the Rust
JIT layer (`src/compiler_rust/compiler/src/codegen/instr/body.rs`); the
Simple-side codegen (`src/compiler/70.backend/codegen.spl`) delegates to that
layer and has no parallel implementation to patch.

**Required action:** rebuild `bin/simple` from the fixed Rust sources:

```bash
scripts/bootstrap/bootstrap-from-scratch.sh --deploy
```

Until then the probe exits 139 (segfault) in default JIT mode and exits 0 in
`SIMPLE_EXECUTION_MODE=interpret` mode. The interpret-mode guard on the serial
checker NVMe wrapper remains appropriate.

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
