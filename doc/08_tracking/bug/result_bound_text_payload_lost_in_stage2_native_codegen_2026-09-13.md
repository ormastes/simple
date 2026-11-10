# `case Ok(message):` loses a text payload under Stage-2 native codegen
## Open 2026-09-16 — needs owner triage

Reviewed in the 2026-09-16 bug-ledger normalization pass; no resolution
evidence found in the body. This is bookkeeping, not verification.

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


---

## Addendum 2026-11-11 (lane boot7) — SUPERSEDED (masking symptom fixed on tip; codegen root fix tracked by the stage2-miscompile campaign)

State at release tip b364745fdbf8:

- **The masking symptom this row filed is fixed.** The failure arm of
  `_finish_selected_module_compile` now asks the RUNTIME for the on-disk size
  before naming the failure mode, re-reads through
  `_sffi_file_read_text(path) ?? ""` when the bound payload reads empty, and
  reports `diagnostic <n> bytes on disk, payload lost on read` when both reads
  fail — a true statement naming this defect instead of the false
  `diagnostic file empty` (driver_aot_native_output.spl:4478-4508, including
  the 2026-09-13 strace measurement quoted in its comment). Pickaxe for
  "payload lost on read" lands on 9e7e7a526edb (PR #7597) / the release
  transplants (88aac2ffe286, bb3f6ab8ab29). This is exactly the "worked
  around" state the doc records, now shipped.

- **The underlying stage2 codegen defect** (a `case Ok(x):`-bound payload —
  text here, scalar in the `[receipt-size-canary]` family — misread by a
  stage-2-compiled binary) is covered by the systematic stage2-miscompile
  campaign, not by a per-bug root fix: MIR payload-provenance fixes are on the
  tip (e.g. ffe84b4e0a2 "register an Optional payload NAME and give
  `case Some(x)` the type-directed path", b0729ed807bd, and the 2026-11-05
  s2fix sweep notes in bug_db.sdn which mark the related Result/Optional
  payload rows "still open, root fix needs a stage3 producer"). The
  `[receipt-size-canary]` runtime cross-checks are still present at
  driver_aot_native_output.spl:1111, :3513, :3793 — i.e. the guards remain
  because the frozen stage-2 producer still misreads pattern-bound payloads.
  Root-fix verification needs a stage3 native producer — a native/entry-closure
  build, forbidden in this lane (BLOCKED: `native-build` of the stage3 chain +
  this bug's own "next step" self-contained repro, per the doc).

Seed-smoke verification (2026-11-11, seed 0791c2b7f4a7, interpreter mode):
- `bin/simple.exe test test/01_unit/compiler/codegen/native_result_struct_payload_push_spec.spl
  --mode=interpreter --no-cache` — 2/2 PASSED (Result-struct payload family
  coverage).
- `bin/simple.exe test test/01_unit/compiler/mir/optional_payload_struct_provenance_source_spec.spl
  --mode=interpreter --no-cache` — behavioral cases PASSED; 2 of 4 failed only
  on pinned-source-text drift (expected-source embedding references old
  `compiler.mir.*` module spellings) — pre-existing spec drift on the tip,
  unrelated to this row.
