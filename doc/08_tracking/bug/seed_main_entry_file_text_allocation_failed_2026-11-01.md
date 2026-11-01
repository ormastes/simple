# Seed runtime: file reads from an auto-invoked `main` fail with "file text input allocation failed"

Status: OPEN 2026-11-01 — worked around in `scripts/check/cert/mcdc_module_coverage.spl` (no `main` entry; top-level call).

**Severity:** Blocking for any script that defines `fn main()` and reads a file on the Rust bootstrap seed (`src/compiler_rust`, `cargo build --profile bootstrap`, Windows llvm-mingw lane, 2026-11-01 build).
**Affected runtime path:** `src/lib/nogc_sync_mut/io/file_text_session.spl` (`text_byte_buffer` / `text_bytes_concat_checked` under `FileTextSession.read`), reached through `std.io_runtime.file_read_result` / `file_read` / `read_file`.
**Found by:** MC/DC module coverage tool lane (`doc/05_design/generics_coverage_mcdc.md`).
**Path:** `bug` track.

## Symptom

Same file, same cwd, same import (`use std.io_runtime.{file_read_result, file_exists}`), interpreter mode (`SIMPLE_NO_JIT=1` makes no difference):

```
# top-level script statements (build/probe_a.spl)
A exists=yes
A result ok len=8907

# identical calls inside `fn main():` (build/probe_b.spl, main auto-invoked)
B exists=yes
B result err=file text input allocation failed
B local err=file text input allocation failed
```

`file_exists` succeeds in both contexts; only the text-session byte-buffer
allocation fails under the auto-invoked `main`. The failure is silent for
callers that use `file_read` / `read_file` (they return `""`), which made the
CLI appear to "instrument zero decisions" and write 0-byte shadow files.

## Repro

```
BIN=build/cargo-target/bootstrap/simple.exe
cat > /tmp/p.spl <<'EOF'
use std.io_runtime.{file_read_result}
fn main():
    match file_read_result("src/compiler/30.types/type_infer/generic_calls.spl"):
        case Ok(c): print "ok " + c.len().to_text()
        case Err(e): print "err " + e
main()
EOF
"$BIN" run /tmp/p.spl          # err file text input allocation failed
```
Remove the `fn main():` wrapper (keep the body at top level) → `ok 8907`.

## Workaround

Scripts that must read files on the seed should not define `main`; run the
body as top-level statements (`val code = tool_main()` + `exit(code)`), as
`scripts/check/cert/mcdc_module_coverage.spl` now does.

## Not yet done

* Root cause inside the seed's entry-closure execution of `main` (allocation
  budget / arena differences for `[u8]` buffers) not identified.
* Not re-checked on a pure-Simple self-hosted `bin/release/<triple>/simple`
  (none available on this host on 2026-11-01); re-run the repro there and
  close this note if it passes.
