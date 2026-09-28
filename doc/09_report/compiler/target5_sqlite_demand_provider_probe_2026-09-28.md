# Target 5 SQLite first-demand provider probe (2026-09-28)

## Scope and result

An isolated Linux aarch64 native UI access-store spec links
`runtime_sqlite_demand.o` instead of the SQLite shared library. `readelf -d`
shows only libc and the ELF interpreter in `DT_NEEDED`; SQLite is absent.
The bridge starts in state 0, admits an exact sealed provider on the first
SQLite call, and reaches state 2. The store spec passed 2 examples, 0 failures
with repeated cached reads and disabled-cache cleanup. Four simultaneous
native pthread callers opened and closed SQLite connections through one
first-use admission (1 example, 0 failures).

The provider is built with `SIMPLE_SQLITE_DEMAND_PROVIDER=1` and `-z defs`.
Its ABI v1 init receives the host's string-new, string-data, and string-len
callbacks, leaving no unresolved Simple runtime symbols. Admission requires
`SIMPLE_SQLITE_PROVIDER_PATH` and `SIMPLE_SQLITE_PROVIDER_SHA256`; it verifies
the hash of the same sealed memfd that `dlopen` maps, then requires ABI v1 and
all 27 `rt_sqlite_*` functions. A shared monotonic snapshot fd namespace
prevents an old `dlopen` pathname from being reused for newer bytes. The
provider stays mapped for the process lifetime to keep live handles valid.

The rejection spec passed separately for a missing path, wrong SHA-256,
incompatible ABI, and missing symbols (1 example, 0 failures for each fresh
process). The first rejection run exposed the existing SQLite wrapper's
positive-handle check accepting tagged nil (`3`); its local handle validator
now rejects that value. No crash or partial open was observed in those runs.

## Size and performance limits

| Artifact | Bytes |
|---|---:|
| Demand spec executable | 131,816 |
| O2 demand provider shared library | 21,864 |
| Demand bridge object, before final section removal | 14,392 |
| Earlier direct-linked spec executable | 121,392 |

The demand executable is 10,424 bytes larger than the earlier direct-linked
spec executable (8.6%), with two additional admission-state assertions and
different provider builds. This is a focused bridge cost, not the release-small
hello result. One demand spec sample reported 0.00 s elapsed and 3,232 KiB
max RSS; no matched repeated cohort exists, so no normalized time/RSS verdict
is claimed. The provider itself is absent from startup mapping by link
contract, but the full CLI, Office/GPU families, install receipt, rollback,
and all-platform feature matrix remain open.

## Reproduction

Build the provider from `src/runtime/runtime_sqlite.c` with
`-DSIMPLE_SQLITE_DEMAND_PROVIDER=1 -shared -fPIC -O2 -lsqlite3 -Wl,-z,defs`.
Build `src/runtime/runtime_sqlite_demand.c` as a PIC object. Set
`SIMPLE_LINK_OBJECTS` to the bridge object when using the no-stub pure-Simple
native builder with `--entry-closure` and the three specs in
`test/02_integration/app/ui_access_sqlite_*_spec.spl`. Set the provider path
and its `sha256sum` digest before execution. The concurrent spec additionally
links `test/02_integration/runtime/sqlite_demand_concurrent_probe.c`.

The first attempt without `--entry-closure` scanned the entire source set and
was canceled after several minutes; the bounded builds compiled 39 to 106
units in roughly 2 to 5 seconds. An initial concurrent spec using
`std.concurrent.thread` crashed in `rt_thread_spawn_isolated` before reaching
SQLite. The final pthread probe calls the same native bridge without that
separate thread-runtime failure.
