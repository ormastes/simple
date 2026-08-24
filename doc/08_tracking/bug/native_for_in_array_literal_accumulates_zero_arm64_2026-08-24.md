# Native `for x in <array literal>` accumulates 0 on aarch64-apple-darwin (2026-08-24)

Status: OPEN — reproduced minimally, not diagnosed, not fixed.
Found incidentally while building a regression fence for
`stage2_cranelift_direct_segv_nil_struct_fields_2026-08-24.md`; unrelated to
that bug's dict-values mechanism.

## Reproduce (deterministic, seconds)

```
fn main():
    val xs = [1, 2, 3, 4]
    print "len={xs.len()}"
    var total = 0
    for x in xs:
        total = total + x
    print "sum={total}"
```

| lane | output |
|------|--------|
| interpreted (`simple run`) | `len=4` / `sum=10` — CORRECT |
| `native-build --backend=llvm` | `len=4` / `sum=0` — **WRONG** |
| `native-build --backend=cranelift` | `len=4` / `sum=0` — **WRONG** |

`.len()` on the same local is correct, so the array handle is live; only the
for-in accumulation is lost. Both backends fail identically, which points at
MIR lowering / the shared runtime-array for-in desugaring
(`lower_for_array_indexed`, `src/compiler/50.mir/mir_lowering_stmts.spl`),
not at either code generator.

A wider fixture in the same run showed the same shape for text-keyed dicts and
string arrays, plus a runtime diagnostic on stderr:

```
[simple-runtime][error] rejected invalid array handle before dereference;
  probable compiler/FFI ABI mismatch (value_bits=0x000000095b0030b0)
R_intarray_sum 0 / R_dict_keys_sum 0 / R_dict_values_sum 0 / R_strarray_join <empty>
```

## Environment

- Host/target: `aarch64-apple-darwin` (macOS 25.5.0, arm64).
- Compiler source: `origin/main` @ `6eb889a1b07`, unmodified.
- Worker: a seed built fresh from that tree's `src/compiler_rust`
  (`cargo build --release --bin simple`, 1m53s), NOT the stale Jul-25 deployed
  seed — that one cannot parse current stdlib (`unsafe(capabilities: [ffi]):`
  blocks) or current compiler source at all.
- Two macOS-only harness notes, needed to reproduce: `setsid` does not exist on
  macOS and the native-build worker spawns through it (shim it); and the hosted
  entry stub failed to link until the fix landed alongside this record.

## NOT verified

- Whether x86_64 Linux reproduces. Untested.
- Whether a struct-element array reproduces: the sibling struct fixtures
  (`for f in d.values()` over `Dict<i64, Big>`, 6- and 16-field `Big`) were
  CORRECT in the same runs, so this is not a blanket for-in failure.
- Root cause. Not investigated.
