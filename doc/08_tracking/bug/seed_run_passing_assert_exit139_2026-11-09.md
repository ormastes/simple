# Seed exits 139 when `simple run` reaches a passing assert()

- **Priority**: P2
- **Status**: open
- **Repro**: `test/fixtures/repro/seed_run_passing_assert_exit139.spl`

## Observed (2026-11-09)

Binary: shared seed `C:/dev/simple/bin/simple.exe`, mtime 2026-11-04 16:58:52 +0900, size 40739328 bytes.

```
fn main():
    assert(1 == 1)
    print("after assert")
```

`simple.exe run <repro>` -> Segmentation fault, exit 139, nothing printed after the seed warning.
The same script without the `assert` line prints and exits 0.

## Expected

A passing assert is a no-op; the script prints `after assert` and exits 0.
