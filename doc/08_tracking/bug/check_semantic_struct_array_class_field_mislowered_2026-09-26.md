# `simple check` (semantic, single-file) mis-lowers a class holding a struct array: `undefined: <Class>`, `[Struct]` typed as `[i64]`, cascading "unsupported expression kind: Cast(IntLit(0), u64)"

Date: 2026-09-26
Lane: SOSIX mmap arena slice (src/os/services/sosix/mmap_v1.spl)
Owner: unassigned (compiler tooling)
Found by: SOSIX interface slice 3 implementation session

## Summary

`bin/simple check <file>` (semantic mode, deployed self-hosted binary
`bin/release/aarch64-unknown-linux-gnu/simple`, 2026-09-25) rejects a
minimal, import-free construct that `bin/simple run` and
`bin/simple test --mode=interpreter` both accept and execute correctly:

```spl
pub struct P:
    a: u64

pub class C:
    items: [P]

impl C:
    pub fn bump():
        var i = 0
        while i < self.items.len():
            i = i + 1
```

`check` reports, on this exact file: `error[semantic]: undefined: C` at the
`impl`, then lowers the `items: [P]` field to `[i64]` ("no method 'len'
found for type '[i64]'"), then cascades "unsupported expression kind:
HirExprKind::Cast((IntLit(0), Int(64,false)))" for every `0u64` literal in
the impl. `run` executes the same file correctly (probe exit 0).

## Impact

None on the real gates: `scripts/check/check-pr-fast.shs` already records
that semantic `simple check` "reports HIR unresolved-name errors on
UNCHANGED origin/main files ... so it cannot gate a PR without failing
clean code" and defaults to `--syntax-only`, and
`scripts/check/check-dangling-imports.shs` notes `check <f>` is "NOT an
oracle". The SOSIX slices verify through
`bin/simple test <spec> --mode=interpreter`, which is unaffected.

## Repro

```
cat > /tmp/probe3.spl <<'EOF'
pub struct P:
    a: u64
pub class C:
    items: [P]
impl C:
    pub fn bump():
        var i = 0
        while i < self.items.len():
            i = i + 1
fn main() -> i64:
    0
EOF
bin/simple check /tmp/probe3.spl    # errors: undefined: C, [i64] has no len, Cast(IntLit 0)
bin/simple run /tmp/probe3.spl --mode=interpreter   # exit 0
```

## Suspected area

Single-file semantic check path (HIR lowering of `impl` blocks whose
receiver class has a struct-typed array field); the interpreter/JIT path
lowers the same construct fine. Fix or reject explicitly — silently
poisoning the module scope turns one bad lowering into ~30 cascading
"undefined" errors at unrelated positions.
