# SMF reader relocations marshalling perf — `rt_smf_parse_relocs` clones 8.6MB Vec<Value>

**Date:** 2026-04-29
**Severity:** P2 (test timeout, not correctness)
**Status:** Open

## Symptom

`test/system/simple_smf_format_validity_spec.spl` test
"compiler SMF relocation table is parseable" times out after 120s when called
on `build/os/simple_cli_apps/x86_64/compile.smf` (8.6MB, 139,248 relocs).

```
[watchdog] wall-clock timeout (120s) exceeded
✗ compiler SMF relocation table is parseable
  timeout: execution exceeded 0 second limit
```

## Root cause

`SmfReaderMemory.read_relocations()` (in
`src/compiler/70.backend/linker/smf_reader_memory.spl`) calls:

```simple
rt_smf_parse_relocs(self.data, self.sections_offset,
                    self.header.section_count as i64,
                    self.header.smf_data_offset)
```

The first argument is the entire SMF file as a `[u8]`. In the interpreter, this
is a `Vec<Value>` where each byte is a `Value::Int(n as i64)`. The Rust impl
in `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs::rt_smf_parse_relocs`
does:

```rust
let data_vals = match args.first() {
    Some(Value::Array(a)) => a.as_ref().clone(),  // 8.6M-element clone
    ...
};
let data: Vec<u8> = data_vals.iter().map(|v| match v {
    Value::Int(n) => *n as u8, ...
}).collect();
```

That is one full `Vec<Value>` deep clone of 8.6M elements followed by a second
8.6M-element iteration into a `Vec<u8>`, before the relocation parsing even
starts. This easily exceeds the 60s spec budget (and the 120s watchdog) on the
release interpreter even after `target/release/simple` is rebuilt.

## Failed approaches considered (all out of scope)

1. **Slice in Simple, pass smaller buffer** — same bottleneck, just smaller.
2. **Pure-Simple parser loop** — 139k push iterations hit the interpreter's
   O(N²) array-push wall the extern was created to bypass. Worse, not better.
3. **Cover-up `Ok([])`** — explicit cover-up per `feedback_no_coverups`. Not
   acceptable.

## Proposed fix (out of scope for current commit)

Rust-side change in `src/compiler_rust/compiler/src/interpreter_extern/file_io.rs`:

- Add a path-based variant: `rt_smf_parse_relocs_from_path(path: text, ...)
  -> [i64]`. Reads bytes directly via `std::fs::read`, skipping the
  `Value::Array → Vec<u8>` marshalling.
- Alternative: accept a `Value::Bytes` (raw byte buffer) variant where the
  interpreter already holds a flat `Vec<u8>` (no per-element `Value::Int`
  wrappers).

Update `SmfReaderMemory.read_relocations()` to use the path-based extern when
the SMF was loaded from disk, falling back to the byte-array form otherwise.

Constraint context: changes to `src/compiler_rust/` were out of scope for the
2026-04-29 SMF byte-layout reconciliation commit (parallel agent active in
that subtree). Logging this as P2 so it can land in a follow-up commit.

## Verification gate (post-fix)

```bash
timeout 60 bin/simple test test/system/simple_smf_format_validity_spec.spl
```

Must reach 14 passed / 0 failed in <60s.

## Current status (2026-04-29)

After release-binary rebuild that exposed `rt_smf_parse_relocs`:
- 13/14 pass (was 12/14 — the prior failure was "unknown extern function" on
  both reloc tests; rebuild fixed the second test).
- 14th test gated on this perf issue.
