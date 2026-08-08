# `bin/simple run` resolves `std.*`/`lib.*` to a stale bundled stdlib — on-disk edits are silently ignored

- **Date:** 2026-08-08
- **Status:** OPEN
- **Severity:** High (measurement trap — produces confident false results, not a crash)
- **Component:** module resolution in the deployed binary
  (`bin/release/x86_64-unknown-linux-gnu/simple`), `run` subcommand

## Summary

Under `bin/simple run <script>`, an import of a stdlib module (`use std.X` or
`use lib.X`) does **not** resolve to the corresponding file in the working tree.
It resolves to a stale copy bundled with the deployed binary. Edits to
`src/lib/**/*.spl` have **zero effect** on the running program, and nothing in the
output says so — the script runs, exits 0, and reports plausible-looking values
computed from the old code.

`bin/simple test` does **not** have this problem: the same edits are live there.

This matters because the standing guidance is that "compiler/stdlib `.spl` edits
are live on the interpreter path, no rebuild needed." That is true for
`bin/simple test`; it is **false** for `bin/simple run`. Anyone verifying a
stdlib change with a `run` script gets a silent false result.

## Reproducer (the proof is a sabotage that did nothing)

1. Edit `src/lib/common/bcrypt/salt.spl` so `generate_random_bytes` is
   unmistakably different — replace the per-byte expression at line 115 with the
   constant `7`:

   ```
   var byte_val = 7
   ```

   Confirm the change is on disk with `grep -n "byte_val = " src/lib/common/bcrypt/salt.spl`.

2. Run a script that imports it:

   ```
   use std.bcrypt.salt.{generate_random_bytes}

   fn main():
       val a = generate_random_bytes(4)
       print(a[0].to_text() + "," + a[1].to_text() + "," + a[2].to_text() + "," + a[3].to_text())
   ```

   ```
   SIMPLE_EXECUTION_MODE=interpret bin/simple run /tmp/probe.spl
   ```

3. **Expected if source were live:** `7,7,7,7`.
   **Actual:** `126,223,44,245` — the exact output of the *pre-edit* LCG
   (`seed=12345; seed = (seed * 1103515245 + 12345) % 2147483648; seed % 256`).

The old LCG's exact stream is what makes this conclusive: the printed bytes are
not merely "unchanged", they are provably the output of the code that was
deleted from disk.

## Scope of what was tried and did not help

| Attempt | Result |
|---|---|
| `use lib.common.bcrypt.salt` instead of `use std.bcrypt.salt` | Same stale values |
| `SIMPLE_EXECUTION_MODE=interpret` (bypass JIT) | Same stale values |
| `SIMPLE_LIB=/home/ormastes/dev/pub/simple/src/lib` | Same stale values — the env knob does not move resolution |
| Clearing `.simple/cache`, `~/.cache/simple` | No cache entry for the module existed; not a cache-staleness issue |
| Second, independent module (`tls/_TlsUtilities/hex_encoding.spl`) | Same behaviour — returned `180,2,59,33`, the old length-seeded LCG's exact stream for `length=4` |

Two unrelated modules in two different stdlib families both exhibit it, so this
is general resolution behaviour, not one bad file.

Relevant symbols in the binary (`strings`):
`simple_compiler::stdlib_variant::stdlib_root_candidates`,
`simple_compiler::module_resolver::types::detect_stdlib_root`,
`simple_compiler::pipeline::module_loader::resolve_from_stdlib_root`.

## A second trap found alongside it (independent defect)

While probing, indexing a `list<i64>` with a **loop variable** under the JIT
returned each value **shifted left by 3** (`126` read back as `1008`, `223` as
`1784`, `44` as `352`). Literal indices (`a[0]`, `a[1]`) returned correct values.
A range check written as `if av < 0 ... if av > 255` therefore passed vacuously on
corrupt data. This matches the known "list.get returns value shifted left 3"
defect and is called out here only because it compounds the trap above: the first
probe reported *both* a stale value *and* a corrupt one, and looked plausible.
Running with `SIMPLE_EXECUTION_MODE=interpret` avoids the shift.

## Impact

Any verification of a stdlib change performed with `bin/simple run` is
fail-open. This includes crypto changes, where a false GREEN means shipping a
generator that still emits constants. The bcrypt and TLS CSPRNG fixes landed on
2026-08-08 were initially "verified" this way and appeared to fail; only the
sabotage test revealed the harness, not the fix, was at fault.

## Recommended action

1. Make `bin/simple run` resolve `std.*`/`lib.*` from the working tree the way
   `bin/simple test` does, **or**
2. Fail loudly: when `run` resolves a stdlib module to a bundled copy that
   differs from the working-tree file, emit a warning naming both paths.

Option 2 is the smaller change and removes the fail-open property, which is the
actual danger. Silence is what made this expensive.

## Standing guidance until fixed

Verify stdlib `.spl` edits with `bin/simple test <spec>`, never `bin/simple run`.
Confirm the harness is live with a sabotage-to-constant before trusting a GREEN.
