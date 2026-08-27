# char.to_i32() input-independent zero degenerates checksum hashes - 2026-08-26

Status: **SOURCE FIXED; DEPLOYED RUN EVIDENCE BLOCKED BY AN UNRELATED, ALREADY-TRACKED
SEED BUILD BREAKAGE** (same shape as
`doc/08_tracking/bug/rust_interpreter_mixed_if_import_newline_2026-08-25.md`'s
verification blocker). Root cause, fix, and pre-fix probe evidence below are
all real and reproduced against a running binary. Post-fix end-to-end
re-execution of that exact binary could not be produced in this session
because `cargo check -p simple-compiler --lib` at the current tree tip fails
with 8 unrelated pre-existing errors (`probe_source_cached` missing from
`crate::interpreter`, `IMPORT_AST_HITS`/`IMPORT_AST_PARSES` missing from
`crate::perf_counters`, `read_trace` unresolved, and stale
`importer_glob_sources`/`importer_fn_bindings` field names on `Lowerer` at
`hir/lower/lowerer.rs:790,795` — none touched by, or related to, this fix in
`interpreter_method/string.rs`). See Verification below.

## Summary

`ch.to_i32()`, where `ch` is a loop variable bound by `for ch in <text>`,
returned `0` for **every** non-numeric single character, regardless of which
character it was. This is a distinct defect from
`doc/08_tracking/bug/u64_range_for_loop_checksum_mismatch_2026-05-14.md`
(which is about `u64` range-loop counter type lowering) — this one is a
runtime method-dispatch bug with no loop-typing involvement at all; it
reproduces on a single `x.to_i32()` call with no loop.

Suspected by: an observed hash collision in a checksum spec
(`test/01_unit/tools/shell/checksum_spec.spl`), which computes a djb2-style
hash as `hash = ((hash << 5) + hash) + ch.to_i32()` over each character of a
string. Two different strings hashed the same because `ch.to_i32()`
contributed `0` for every character in both.

## Root cause

There is no separate runtime `char` value in the Rust seed: `for ch in text`
yields a single-character `Value::Str`
(`src/compiler_rust/compiler/src/value.rs`), and `char` exists only as a
static HIR type (`HirType::Char`,
`src/compiler_rust/compiler/src/hir/type_registry.rs`) that is erased to text
before it ever reaches the interpreter's value representation.

`ch.to_i32()` therefore dispatches through the generic string-method arm in
`src/compiler_rust/compiler/src/interpreter_method/string.rs`, which (before
this fix) treated `to_i32`/`to_i64`/`to_i16`/`to_i8`/`to_int` purely as a
"parse this text as an integer" operation:

```rust
"to_int" | "to_i64" | "to_i32" | "to_i16" | "to_i8" => {
    match s.trim().parse::<i64>() {
        Ok(n) => return Ok(Value::Int(n)),
        Err(_) => return Ok(Value::Int(0)),   // <-- always 0 on parse failure
    }
}
```

Any non-digit single character (i.e. almost every character in a text
checksum) fails to parse as an integer and silently fell back to a hardcoded
`Value::Int(0)` — **input-independent**, exactly as suspected. This is
separate machinery from `ord`/`codepoint` (same file, a few lines below),
which correctly returns the Unicode code point but is a different method
name and was never called by the checksum spec.

## Confirmation (direct probe)

Binary: Rust seed at `bin/release/x86_64-unknown-linux-gnu/simple`
(`bin/simple --version` prints the bootstrap-seed warning + `Simple Language
v1.0.0-RC`).

```spl
for ch in "hello":
    print(ch.to_i32())
print("---")
for ch in "world":
    print(ch.to_i32())
```

Pre-fix output (`bin/simple run`): `0 0 0 0 0 --- 0 0 0 0 0` — confirmed
input-independent for every character in both words.

## Fix

`src/compiler_rust/compiler/src/interpreter_method/string.rs`, the
`to_int`/`to_i64`/`to_i32`/`to_i16`/`to_i8` arm: on parse failure, if the
receiver is exactly one character, fall back to that character's Unicode code
point instead of a hardcoded `0`. Multi-character non-numeric text (where a
codepoint fallback would be meaningless) still returns `0`, and
already-numeric text (`"42".to_i32()`) is completely unaffected since it
still hits the `Ok(n)` branch first. This is the minimal, semantics-preserving
fix: it does not touch the loop/type-lowering machinery from the 2026-05-14
bug, does not add a runtime `Char` value, and does not change behavior for
any existing multi-character numeric-string caller.

Post-fix, `'h'.to_i32()` etc. should print the actual per-character codepoints
(104, 101, 108, 108, 111 for `hello`; 119, 111, 114, 108, 100 for `world`),
making `test/01_unit/tools/shell/checksum_spec.spl`'s "produces different hash
for different input" case pass — verified by source-level trace of the new
match arm (single-char fallback to `c as i64`), not yet by re-running the
compiled binary (blocked, see Status).

## Verification

- Rust seed (interpreter path), PRE-FIX: reproduced live by direct
  `bin/simple run` on the probe below against the deployed seed binary at
  `bin/release/x86_64-unknown-linux-gnu/simple` (identifies itself via
  `--version` as the bootstrap seed). Output: `0 0 0 0 0 --- 0 0 0 0 0`.
- Rust seed (interpreter path), POST-FIX: the fix was made in
  `src/compiler_rust/compiler/src/interpreter_method/string.rs` and reviewed
  by inspection (traced the new match arm against `'h'`, `'w'`, `"42"`, `"5"`,
  `""`). It could NOT be re-run against a freshly built binary in this
  session: `cargo check -p simple-compiler --lib` at the current tree tip
  fails with 8 unrelated, pre-existing errors unconnected to this file (listed
  in Status above) — the same class of "seed unbuildable from unrelated dirty
  compiler integration" blocker already documented in
  `rust_interpreter_mixed_if_import_newline_2026-08-25.md`. No stale binary
  was substituted and reported as post-fix evidence.
- Native/LLVM codegen and the self-hosted Simple compiler's own
  `to_i32`-on-string handling were not touched by this fix and were not
  independently probed here; if either has its own separate string-to-int
  cast implementation, it should be checked for the same pattern.
- Whoever next gets a green `cargo check -p simple-compiler` on this tree
  should rebuild `bin/release/x86_64-unknown-linux-gnu/simple` and re-run
  `test/01_unit/lib/common/bytes/char_to_i32_probe_spec.spl` plus
  `test/01_unit/tools/shell/checksum_spec.spl` to close this out as fully
  RESOLVED.

## Reproduce + defect-class coverage

- `test/01_unit/lib/common/bytes/char_to_i32_probe_spec.spl` — reproduce spec.
  Run against the deployed (pre-fix) seed binary:
  `SPEC FILE VERDICT: ... executed=6 passed=2 failed=4` — the 4 failures are
  exactly the distinctness checks (`to_i32`/`to_i64`/`to_i8` all-same-value
  for distinct letters, and the djb2 collision reproduction); the 2 passes are
  the numeric-parsing and empty-string guards, which the fix must not
  disturb. Expected to flip to `executed=6 passed=6 failed=0` once a build of
  this fix can be deployed (see Status/Verification above for the blocker).
- `test/01_unit/tools/shell/checksum_spec.spl` (pre-existing, not authored by
  this fix) independently confirms the same defect against the deployed
  binary: `Results: 2 total, 1 passed, 1 failed` — "produces different hash
  for different input" fails pre-fix because `hash1 == hash2` when every
  character contributes `to_i32() == 0`.

## Verified 2026-08-26 — and the bug is only HALF fixed

### The "cannot verify, seed does not build" caveat was wrong

This record originally said post-fix verification was blocked by 8 pre-existing
errors in `cargo check -p simple-compiler --lib`. That is **refuted**. At
`origin/main`, both of these return **rc=0 with 0 errors**:

    cargo check --release --bin simple        -> SEED_CHECK_RC=0, 0 errors
    cargo check -p simple-compiler --lib      -> LIB_CHECK_RC=0,  0 errors

The failure was local staleness in the investigating clone, not a repo defect —
the same trap `.claude/rules/` records as costing an earlier session three false
leads. A seed was therefore built with the fix (`cargo build --release --bin
simple`, rc=0, 4m10s) and the fix was measured, not traced.

### Controlled A/B — the fix WORKS on the interpreter path

Same probe, same `SIMPLE_EXECUTION_MODE=interpreter`, two binaries:

| binary | `for ch in "hello": print(ch.to_i32())` |
|---|---|
| pre-fix deployed seed | `0 0 0 0 0` |
| post-fix build | `104 101 108 108 111` |

`"world"` -> `119 111 114 108 100`. Correct code points, distinct per character.

### SECOND DEFECT, still OPEN: the JIT path is unfixed and additionally corrupts

The default `run` path (JIT) is NOT fixed by this change and is worse than a
wrong number — it leaks mis-tagged values:

| expression | interpreter (fixed) | JIT (default, broken) |
|---|---|---|
| `for ch in "hello"` | `104 101 108 108 111` | `0 0 0 0 0` |
| `"5".to_i32()` | `5` | `<value:0x5>` |
| `"a".to_i32()` | `97` | `0` |
| `"42".to_i32()` | `42` | `0.000...0002` (a float-shaped 300-digit string) |

`<value:0x5>` and the float-shaped output are a value printed through the wrong
tag, not merely an arithmetic error. This is an engine-differential defect of
the class §22.5 exists to catch, and it means **any checksum built on
`ch.to_i32()` is still degenerate under the default execution mode.** Filed
separately rather than folded in here, because it is a different layer
(codegen/JIT dispatch) from this record's interpreter method table.

### Residual semantic ambiguity (neither defect, but do not lose it)

`'5'.to_i32()` returns **5** (the numeric parse wins) while `'a'.to_i32()`
returns **97** (the code point). Digits and the control characters sharing their
values therefore collide in any per-character fold. The conservative choice is
deliberate — making digits return code points would break `"7".to_i32() == 7`
for existing callers — but the real fix is to stop erasing `HirType::Char` so a
character and a one-character string are distinguishable at runtime. Until then
`ord`/`codepoint` is the unambiguous method and should be preferred in hashes.
