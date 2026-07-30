# `.pop()` on a struct-field array does not shrink the array (Rust debug engine)

- **Found:** 2026-07-30, re-verifying `test/01_unit/lib/editor/document_service_spec.spl`
- **Status:** OPEN (engine defect). Call sites in the extension kernel worked
  around; the primitive is still wrong.
- **Severity:** silent wrong results. `pop()` returns the correct element, so
  nothing errors — the array just keeps its length.

## Symptom

`arr.pop()` where `arr` is reached **through a struct field** returns the last
element correctly but leaves `len()` unchanged. A plain local array pops fine.

```
struct Box:
    xs: [i64]

fn main():
    var b = Box(xs: [])
    b.xs.push(7)
    print(b.xs.len().to_text())      # 1   (correct)
    val v = b.xs.pop()
    print(v.to_text())               # 7   (correct)
    print(b.xs.len().to_text())      # 1   WRONG, expected 0

    var plain = [1, 2, 3]
    val p = plain.pop()              # 3, len 2 -- correct
```

## Engine matrix

| Binary | struct-field `pop()` | local `pop()` |
|---|---|---|
| `bin/release/x86_64-unknown-linux-gnu/simple` (deployed self-hosted) | correct | correct |
| `src/compiler_rust/target/debug/simple` (Rust debug) | **len unchanged** | correct |

Both rows measured with `SIMPLE_EXECUTION_MODE=interpreter`, so this is not a
JIT-vs-interpreter split — it is a per-binary divergence.

## Why it matters more than it looks

`bin/simple test` **spawns the Rust debug binary as its child** (the run log
prints `child binary: .../target/debug/simple`). So the spec suite exercises the
broken engine while `bin/simple run` exercises the correct one — a spec can go
red on correct code, and conversely a real defect in the deployed binary can
stay green. This is the same class as
`run_vs_test_harness_divergence_2026-07-28.md`.

## Reproduction

```bash
SIMPLE_EXECUTION_MODE=interpreter src/compiler_rust/target/debug/simple run <the probe above>
SIMPLE_EXECUTION_MODE=interpreter bin/simple run <the probe above>
```

## Workaround (in use)

Index-read the last element and slice-reassign the field — correct on both
engines:

```
val last_index = handle.undo_stack.len() - 1
val inverse_tx = handle.undo_stack[last_index]
handle.undo_stack = handle.undo_stack.slice(0, last_index)
```

Applied at `src/lib/editor/document/registry.spl` `DocumentRegistry.undo`.

## Fix direction

Find where the array method receiver is resolved for a field access in the Rust
runtime's list builtins: `pop` almost certainly mutates a temporary copy of the
field's array and never stores it back, while `push` does (push works). Same
shape as the known "class instances in array FIELDS lose mutations" family, so
check whether one write-back path covers both.
