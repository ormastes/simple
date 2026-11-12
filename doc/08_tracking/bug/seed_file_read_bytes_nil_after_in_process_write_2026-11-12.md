# Seed interpreter: `file_read_bytes_result` returns Err (rt nil) for a file this process just wrote

Date: 2026-11-12
Discovered by: lane p1-devhub (writing `sqlcipher_salt_binding_spec.spl`)
Binary: phase-1 seed `C:/dev/wt/p1-20261112/src/compiler_rust/target/bootstrap/simple.exe`
(Rust seed, Windows 11, `bin/simple.exe test <spec> --no-session-daemon`)
Status: OPEN — worked around in the spec, root cause not located

## Observed
Within one interpreted spec process, `std.io_runtime.file_read_bytes_result(path)`
returns `Err("file byte read failed: ...")` for a file that
`std.nogc_sync_mut.io.file_ops.file_write_bytes` wrote moments earlier in the
same process, while at the same instant:

- `file_exists(path)` is `true` and `file_size(path)` is the full byte count;
- `file_read_result(path)` (text session read) opens and reads the bytes
  (it fails only on UTF-8 decode, as expected for binary) — so the OS has no
  sharing lock on the file;
- a fresh process reads the same file with `file_read_bytes_result` fine.

The failure is NOT deterministic per call shape. In one process:

| write site | read site | bytes | result |
|---|---|---|---|
| inside fn `rotate` | same fn, right after write | 36864 | OK 36864 |
| inside fn `rotate` | top-level `val` after the fn returned | 36864 | **Err** |
| inside fn `rotate` (1st rotation, same spec) | top-level `val` | 36864 | OK 36864 |
| fn `probe` local path, 100/127/128/200/4096 bytes | same fn | all | OK |
| top-level `file_write_bytes` | top-level print | 100 | OK |
| fn rewrite of an already-read path | top-level print | 200 | **Err** |
| top-level/fn write to `root + "outer.bin"` | top-level `val`, inside `it` | 200 | **Err** |

Both externs resolve to plain `std::fs` in the interpreter
(`interpreter_extern/file_io.rs`: `rt_file_read_bytes` -> `fs::read`,
`rt_file_write_bytes_array` -> `rt_file_write_bytes` -> `fs::write`), and
`rt_file_read_bytes` maps every `Err` to `Value::Nil` without logging the OS
error, which is why the Simple side only sees "read failed".

## Minimal repro (seed, Windows)
```
use std.spec.*
use std.env.{env_get}
use std.io_runtime.{time_now_unix_micros, file_read_bytes_result, file_size}
use std.nogc_sync_mut.io.file_ops.{file_write_bytes}

val stamp: text = time_now_unix_micros().to_string()
val root: text = env_get("TEMP").replace("\\", "/") + "/zz_dbg_" + stamp + "_"
fn read_len(path: text) -> i64:
    match file_read_bytes_result(path):
        case Ok(b): b.len()
        case Err(_): -1
fn make(n: i64) -> [u8]:
    var out: [u8] = []
    var i = 0
    while i < n:
        out.push((i % 251).to_u8())
        i = i + 1
    out
val pf: text = root + "outer.bin"
val wrote: bool = file_write_bytes(pf, make(200))
val got: i64 = read_len(pf)          # observed -1 while file_size(pf) == 200

describe "repro":
    it "reads back what it wrote":
        expect(wrote).to_equal(true)
        expect(file_size(pf)).to_equal(200)
        expect(got).to_equal(200)     # FAILS on the seed
```

## Impact
Any spec or tool that writes a binary file and reads it back in the same
interpreted process can see a spurious read failure. The devhub secured-db
specs that only read committed fixtures are unaffected; `sqlcipher_rekey_roundtrip_spec`
happens to hit an OK row of the table above.

## Workaround applied
`test/02_integration/app/devhub/messenger/sqlcipher_salt_binding_spec.spl`
threads the encrypted image in memory between rotation hops and checks the
written file with `file_size` plus a storage-port reopen (which reads the file
through its own path and succeeds).

## Next step for a fix lane
1. Make `rt_file_read_bytes` (interpreter) surface the OS error text in the
   `Err`, or at least log it under a debug env var, so the failing syscall
   is visible.
2. Re-run the repro above on Windows and Linux seeds; check whether the
   `Value::byte_array` returned is being read as nil on the Simple side
   (`bytes == nil` in `io_runtime.spl:322`) rather than `fs::read` failing.
