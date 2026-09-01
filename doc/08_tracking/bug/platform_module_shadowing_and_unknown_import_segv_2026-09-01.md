# `platform.spl` shadowed by `platform/__init__.spl`; an unknown import SEGVs mute

- **Found:** 2026-09-01, Windows 11, during the Windows path-commonization pass.
- **Binary:** `bin/simple` (`bin/release/.../simple.exe`), which self-identifies as
  `WARNING: this Rust-built Simple binary is a bootstrap seed only`. Not the
  pure-Simple full CLI.
- **Status:** OPEN. Worked around, not fixed — see *Workaround normalized* below,
  which is itself the thing that should not have to happen.

## Defect 1 — two `platform` modules, the directory silently wins

`src/lib/nogc_sync_mut/` carries **both**:

| path | size | kind |
|---|---|---|
| `platform.spl` | 7,968 B | file module |
| `platform/__init__.spl` | 3,789 B | directory module |

They are near-duplicates: each defines its own `is_windows`, `is_unix`,
`is_macos`, `is_linux`, `dir_sep`, `path_sep`, `exe_ext`, `get_host_os`,
`get_host_arch`. `src/lib/platform.spl` (the `std.platform` shim) does
`export use nogc_sync_mut.platform.*`, and that resolves to the **directory**,
so `platform.spl` — the larger, `pub`-annotated, docstring-carrying one — is
**dead for every `use std.platform` caller in the tree**.

Nothing reports the collision: no lint, no guard, no warning. It is invisible
until you add a symbol to the wrong half, which is exactly how it was found.

## Defect 2 — importing a name the module does not export SEGVs (rc=139), mute

Measured three times, three different names:

```
use std.platform.{normalize_arch}    # does not exist   -> rc=139
use std.platform.{normalize_os}      # does not exist   -> rc=139
use std.platform.{to_native_path}    # existed in platform.spl, not in
                                     # platform/__init__.spl -> rc=139
```

No diagnostic, no "unresolved import", no stack — the process dies. A
0-argument name that *does* resolve (`is_windows`, `dir_sep`) works fine, and a
1-argument name from a different module (`std.common.path_pure.to_backslash`)
works fine, so this is not about arity: it is unresolved-symbol handling.

This is the same **"fails mute"** class as `e9cf9800e54`, `8200b73b3bd` and
`ce2bc9df521`: the failure produces no message a caller can act on. It cost
roughly an hour here, because the SEGV was initially and wrongly attributed to
the newly added function rather than to the import that could not resolve. The
misattribution is the real cost: a mute unresolved-import looks exactly like a
codegen bug in whatever you just wrote.

## Workaround normalized (recorded deliberately, per repo rule)

`to_native_path` was added to **both** `platform.spl` and
`platform/__init__.spl`, with the same body. That is duplication knowingly
added to a bug about duplication. It is the minimum that makes the symbol
reachable without deleting one of two near-duplicate modules that 156
`src/lib` files may transitively depend on — a deletion that needs its own
change and its own verification, not a drive-by.

## Fix, in order

1. Make an unresolved import a **diagnostic**, not a SEGV. This is the
   load-bearing one; the shadowing above is survivable while this is not.
2. Collapse the two `platform` modules into one, keeping `platform.spl` (the
   documented, `pub` one) and deleting `platform/__init__.spl`, or vice versa
   — after auditing importers.
3. Add a guard for file-vs-directory module collisions under `src/lib/**`.
   `grep`-able in one pass: for every `X.spl`, assert no sibling `X/__init__.spl`.
   The same collision may exist elsewhere and nothing would report it.

## Not verified

POSIX. No POSIX host was available; both defects are platform-independent by
inspection (module resolution and import handling), but that is inspection, not
execution, and should not be recorded as a measurement.
