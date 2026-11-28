# Seed re-verification: typed `f64?`/`f32?` Some print/interpolation sink

Recipe for re-checking the seed fix for
`doc/08_tracking/bug/seed_jit_f64_option_some_print_sink_reads_raw_payload_as_value_2026-11-27.md`
after the next Rust seed rebuild + `bin/simple.exe` refresh. Do not edit the
bug record; run this recipe and append the outcome as a new lane addendum
elsewhere if a lane owns one.

## What was fixed

The Rust seed runtime's flat float-optional sinks
(`src/compiler_rust/runtime/src/value/sffi/io_print.rs`):

1. `rt_opt_f64_to_string` (the `print c` sink for `f64?`/`f32?`) assumed its
   operand is always the legacy flat raw-bits payload and bit-cast it. A typed
   float optional escapes `mir/float_option_inline.rs` to this sink in any of
   the one-word forms `rt_option_float_bits` already decodes: the Option enum
   over the raw IEEE bits (explicit typed `Some(x)`), the Option enum over a
   boxed float (generic producers), or the flat boxed float (`return x` into
   an `f64?` slot). The sink now routes enum words through
   `rt_option_float_bits` (with the `None` variant rendered as
   `Option::None`), keeps the verbatim-bit path for raw-bits words, and
   decodes flat boxed-float words. Measured before the fix:
   `val c: f64? = Some(0.1); print c` ->
   `Option::Some(0.000...014354639028913)` (the enum's heap address as a
   denormal).
2. New typed interpolation sink `rt_opt_f64_value_to_string`: the tagged
   counterpart for `f64?`/`f32?` words reaching string interpolation. The
   existing `rt_opt_value_to_string` must stay type-erased — a typed float
   Some payload is the RAW IEEE bits while an `i64?`/`bool?` Some payload is
   a tagged `RuntimeValue`, and the two alias at the word level (raw `1.0`
   bits look like TAG_INT, raw `0.1` bits look like TAG_FLOAT), so no
   type-erased decoder can be exact.
3. The new symbol is registered wherever its siblings are: `value/mod.rs`,
   `lib.rs` (keep-static + re-export), `common/src/runtime_symbols.rs`,
   `codegen/runtime_sffi.rs`, `codegen/common_backend.rs`, `elf_utils.rs`.

Pending lowering hunk (TAKEN lane `mir/lower/**`; patch design, to be applied
by the merge owner): in
`compiler/src/mir/lower/lowering_expr_builtin.rs`, the
`rt_value_to_string` special case for flat primitive optionals
(the `flat_opt_to_string_fn(arg.ty).is_some()` branch) hardcodes
`rt_opt_value_to_string`. Route by inner type exactly like the print path
already does: when `flat_opt_to_string_fn(arg.ty)` returns
`rt_opt_f64_to_string` (inner `F32`/`F64`), emit a call to
`rt_opt_f64_value_to_string` instead; keep `rt_opt_value_to_string` for the
int/bool inners. Same for the `parse_*` tagged branch only if a parse family
ever returns a float optional (today it is int-only — leave it). Without this
hunk, `print "i={c}"` of a typed float optional still renders
`Option::Some(<enum@0x...>)`; with it, the output matches the interpreter.

## Rebuild the seed (after the fix is in the tree)

```sh
cd src/compiler_rust
CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
  CARGO_TARGET_DIR=$PWD/../../build/p3cache/f64opt/cargo-target \
  cargo build --release -p simple-driver
# artifact: build/p3cache/f64opt/cargo-target/release/simple.exe
```

Do not overwrite `build/p3cache/fresh-seed/simple.exe` from a lane scratch
build; the seed deploy flow (`scripts/bootstrap/`) owns that copy.

## Checks (in order)

1. Runtime sink unit tests (word-form exactness, no Simple tooling needed):

   ```sh
   CC="$HOME/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64/bin/clang.exe" \
     CARGO_TARGET_DIR=$PWD/../../build/p3cache/f64opt/cargo-target \
     cargo test --release -p simple-runtime --test f64_option_print_sink
   # expect: 2 passed
   ```

2. Doc repro on the JIT lane prints `Option::Some(0.1)` twice:

   ```sh
   SIMPLE_HIR_CACHE_DIR=$PWD/build/p3cache/f64opt/hircache \
   TMPDIR=$PWD/build/p3cache/f64opt/tmp \
   <scratch-simple.exe> run build/p3cache/f64opt/probes/repro.spl
   # expect:
   #   Option::Some(0.1)
   #   interp Option::Some(0.1)   <- needs the lowering routing hunk too
   ```

   (`build/p3cache/f64opt/probes/repro.spl` is the 6-line program from the
   bug record.)

3. Regression spec (RED on the pre-fix seed for the print example; the
   interpolation-hole example asserts the post-routing oracle and stays under
   `# @tag:in-development` until the lowering hunk ships in a seed):

   ```sh
   SIMPLE_BINARY=<scratch-or-deployed-simple.exe> \
   <simple.exe> test test/01_unit/language/f64_option_some_print_sink_spec.spl
   # expect today: 3 examples, 2 passed, 1 failed (in-development)
   # after the hunk + seed: 3/3, then remove the tag
   ```

4. Interpreter oracle cross-check (the spec's expected strings must equal the
   interpreter lane):

   ```sh
   SIMPLE_EXECUTION_MODE=interpreter <scratch-simple.exe> run \
     build/p3cache/f64opt/tmp/specwork/print_sink.spl
   # expect: Option::Some(0.1) / Some(1.0) / Some(NaN) / Some(-0.0) /
   #         Some(0.1) / Some(0.1) / None  (matches EXPECT_SOME in the spec)
   ```

5. Existing parity tests stay green:

   ```sh
   cargo test --release -p simple-compiler --test primitive_option_parity_jit
   # expect: all passed
   ```

## Evidence recorded by the fixing lane (2026-11-27, lane p3-sweep4)

- Baseline (pre-fix scratch seed of the current tree, JIT lane):
  `print c` -> `Option::Some(0.000...014354639028913)`; `print "i={c}"` ->
  `Option::Some(<enum@0x2a47801ef80>)`; interpreter lane ->
  `Option::Some(0.1)` for both. Probes:
  `build/p3cache/f64opt/probes/sinks.spl`, `repro.spl`.
- Post-fix scratch seed: print sink output matches the interpreter oracle
  exactly for explicit `Some(0.1)`, `Some(1.0)` (raw bits alias TAG_INT),
  quiet-NaN and `-0.0` payloads, the flat boxed-float form, `f32?`, and
  `None`; `rt_opt_f64_value_to_string` (called directly via `extern fn`)
  renders every form exactly, including the generic-producer boxed-float enum.
- `cargo test -p simple-runtime --test f64_option_print_sink`: 2/2.
- Regression spec: 2/3 green; the interpolation-hole example stays RED until
  the lowering routing hunk (TAKEN lane, patch design above) lands.
- Residual gaps (out of scope, same defect class, separate sinks/owners):
  `i64?`/`bool?` print+interpolation of enum words (e.g. `Some(5)` prints the
  enum address via `rt_opt_i64_to_string` / `<enum@...>` via
  `rt_opt_value_to_string`); `val z: f64? = nil` prints `Option::None` on the
  JIT vs `nil` in the interpreter (the nil word is indistinguishable from
  `None` at the sink); typed `Dict.get`/`Array.at` producers wrap the payload
  in an Option on the JIT while the interpreter prints the bare value — the
  divergence is in the producer lowering, not the sinks.
