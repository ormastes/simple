# Target 5 Linux Stage4 SQLite demand candidate

Status: focused Linux candidate implemented; full CLI and Target 5 qualification
remain open.

The Stage4 runtime compiler now compiles `runtime_sqlite_demand.c` on Linux.
The Stage4 linker packages that object as its own candidate archive, checks
its exact 27 `rt_sqlite_*` entry points plus the demand-state probe, rejects
direct `sqlite3_*` imports, and offers the archive to the exact requested
symbol owner resolver. The shared SQLite library remains an external provider
admitted by the bridge on first use.

## Focused evidence

- A host C object scan found the 27 bridge entry points and
  `spl_sqlite_demand_state`; its undefined symbols include `dlopen`, `dlsym`,
  `spl_dynlib_snapshot_linux`, `rt_sha256_file_raw_v1`, and host string
  callbacks, with no `sqlite3_*` reference.
- The no-stub Stage2 native symbol-contract spec compiled 40 source units and
  passed 3/3 examples, including missing-symbol and eager-import rejection.
- The no-stub Stage2 archive integration spec compiled 492 source units and
  passed 1/1 example. It built the C object, staged the Stage4 archive,
  scanned the real archive, and resolved `rt_sqlite_open` to its sole owner.
- A pure-Simple native-build probe entry compiled 959 source units and linked
  at 13,482 KiB, with a build peak RSS of 3,164,120 KiB. It contains the
  updated linker but is a diagnostic compiler, not an admitted full CLI.
- The installed self-hosted runtime's `check src/compiler` did not complete
  within a 180-second bound. It produced warnings before timing out, so this
  candidate has no full compiler check PASS receipt.

## Full CLI boundary

The first full CLI Stage4 attempt stopped at a stale relative import from
`src/compiler/99.loader/loader/smf_cache.spl` to
`compiler.monomorphize.note_sdn`. That import is now absolute. The retry
passed source closure (2,446 files) but its diagnostic compiler reported
many `flat AST bridge: unhandled decl node kind (tag=)` parse errors by
module 1,077/2,446. The run exited after about 78 seconds with peak RSS
17,275,068 KiB. It never reached Stage4 link selection, so the earlier
173-symbol full CLI link result has not been reduced by an executable build
receipt. The parse failure is a separate bootstrap/compiler limitation; no
claim is made that the full CLI currently links.

A final bounded retry set `SIMPLE_NATIVE_ARENA_DECLS=1` with a 12 GB
address-space cap and a 120-second timeout. It failed at the same flat AST
bridge error after 34.69 seconds, peaking at 5,580,064 KiB RSS. The first
reported source was `src/app/cli/_CliMain/args_and_os_commands.spl` at its
EOF (line 452, parser context kind 190), with an empty declaration tag;
many later files showed the same pattern. Native arena mode reduced memory
pressure but did not repair the declaration lookup. No further full CLI
retry was run after the session's three-attempt verification cap. See
`doc/08_tracking/bug/target5_native_full_closure_empty_decl_tag_2026-09-28.md`.

## Remaining gates

Run the full CLI through an admitted compiler that parses its current source
closure, then confirm SQLite symbols resolve through the bridge, no SQLite
provider appears in hello `DT_NEEDED`, and UI storage still works after
missing/corrupt/ABI/concurrent/rollback admission. Package the provider with
an immutable install receipt, qualify other platforms and optional families,
and run the matched size, startup, RSS, and compile-time cohorts. Stage4 now
builds and scans one extra Linux candidate; its warm-build cost needs a
measured receipt before Target 5 can pass the joint performance rule.
