# `case Ok(message):` loses a text payload under Stage-2 native codegen

- Status: OPEN (2026-09-13)
- Found: bootstrap lane BOOT-6, `work/bootstrap-full-4-2026-09-12`
- Severity: **masking.** It does not fail a build by itself; it erases the
  reason another failure gives, which is strictly worse than a loud failure.

## The measurement

`strace -f -q -y` on the Stage-2 candidate
`build/bootstrap-boot5c/stage2/aarch64-unknown-linux-gnu/simple.rejected`
(sha256 `67786227817bf45f...`), positional `native-build` of
`scripts/check/cert/redeploy_gate/fixtures/hello_world.spl`, second build into
a populated cache scope:

```
openat(.../simple-aot-diagnostic-njhtYD/message.tmp.2271314.0, O_WRONLY|O_CREAT|O_EXCL|O_CLOEXEC, 0666) = 4
write (.../message.tmp.2271314.0, "AOT object destination already exists", 37) = 37
openat(.../simple-aot-diagnostic-njhtYD/message, O_RDONLY|O_NOFOLLOW|O_CLOEXEC) = 4
read  (.../message, "AOT object destination already e", 32) = 32
read  (.../message, "xists", 32) = 5
read  (.../message, "", 27) = 0
write (1, "backend object-path status 1 (diagnostic file empty; path .../message)", 335) = 335
```

The writer wrote 37 bytes. The reader opened the published file and read all
37 bytes back. The frame that consumed them then reported the file as EMPTY.

## Where

`src/compiler/80.driver/driver_aot_native_output.spl`, the failure arm of
`_compile_selected_module`:

```
match file_read_regular_no_follow_bounded(diagnostic_path, 4096):
    case Ok(message):
        if message.len() > 0: ... return _aot_compile_failure(name, message)
        diagnostic_note = "diagnostic file empty"
```

`message.len()` answered `<= 0` for a 37-byte payload that the syscalls prove
arrived. `rt_string_len` answers `-1` for any word it cannot decode as a heap
string, so `-1` (a lost binding) and `0` (a genuinely empty file) are
indistinguishable at this guard — which is exactly why the note was wrong.

This is the same family as the `[receipt-size-canary]` lines this binary prints
unconditionally (`field=457343569:runtime=1080`, a garbage `i64` read off an
optional-bound `FileFingerprint`), and the same family the file's own comment
at :940 already predicts: "it will misread any other `case Ok(record):` field
read the same way". The canary is for an optional-bound SCALAR field; this is a
Result-bound TEXT payload. Both are reads of a payload bound by a pattern match
in a Stage-2 native binary.

## Not fixed here; worked around

BOOT-6 did not fix the codegen. The driver now asks the RUNTIME for the
diagnostic's size (`file_size_raw`) before naming the failure mode, and when
the file has bytes but the bound payload reads as empty it re-reads through
`_sffi_file_read_text(path) ?? ""` — the same `?? ""` shape that verifies the
capsule receipt successfully on this very binary — and delivers that text. If
both reads come back empty the note is now
`diagnostic <n> bytes on disk, payload lost on read`, which is a true statement
naming this defect, instead of `diagnostic file empty`, which was false.

The workaround only takes effect in a compiler built from the fixed source. The
codegen defect itself is untouched and will misread the next Result-bound
payload that nobody has a runtime-side cross-check for.

## Next step

Reduce it: a self-contained `.spl` that writes n bytes, reads them through
`file_read_regular_no_follow_bounded`, and prints `.len()`, compiled natively
by a Stage-2 binary. Until that exists the blast radius is unknown.
