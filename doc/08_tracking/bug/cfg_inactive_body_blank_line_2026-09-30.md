# Inactive @cfg bodies leaked after blank lines

## Failure and correction

Windows Phase 2 full CLI compilation reported unexpected backticks from the
multiline docstring in `src/os/kernel/memory/vmm_address_space.spl:425`.
The conditional preprocessor stopped excluding an inactive declaration when it
encountered an empty line. A paragraph break therefore removed the opening
triple quote but exposed the remainder of the docstring as source code.

`parser_preprocessor.spl` now keeps the exclusion state across empty and
whitespace-only lines. The next nonempty dedented line still ends exclusion.
Blank output lines preserve the original diagnostic line numbers. The change
does not alter string grammar or rewrite valid source docstrings.

The two other failures in the same log (`core_widgets.spl:93` and
`extended_widgets.spl:142`) were already corrected by `d405819f00d` on main.
See `case_prefixed_fat_arrow_match_body_2026-09-29.md` for its parser evidence.
No duplicate match-arm patch is needed.

## Focused verification

Base: verified remote main `5eb63efa451298e05201c06934f64b76ead7a8f8`.
Invoked executable: admitted Windows Phase 2 producer, SHA-256
`0be6e4c2a802e4fa7993fde80003eb87ffae097e564adb82ab4c937bbc640161`.
The executable identity alone does not establish which compiler route ran.
The positional reproductions below use the pure compiler driver. The explicit
`--entry` component command instead selected the embedded Rust compiler.

In `D:/dev/simple-phase2-parser-failures-20260930`:

- `build/native_probe/phase2_parser/inactive_docstring.spl` reproduces the
  failure with `@cfg(false)`, a docstring paragraph break and backticks.
  The admitted producer exits 1 with the matching unexpected-backtick errors.
  Log: `build/native_probe/phase2_parser/inactive_docstring.log`.
- An active `@cfg(x86_64)` control compiles successfully with that producer;
  the string lexer itself accepts the paragraph and backticks.
- `test/fixtures/compiler/cfg_blank_line_probe.spl` builds the corrected
  preprocessor from source and checks exact output for four cases: inactive
  docstring paragraphs, whitespace-only lines between statements, a nested
  inactive method followed by a retained sibling, and an enabled docstring.
  Exact output checks include unchanged line positions and retained siblings.
- Rust-backed component diagnostic: 20 compiled, 0 reused, 0 failed. Run exits 0 and prints
  `cfg blank-line regressions: 4 passed`. Log:
  `build/native_probe/phase2_parser/fixed_probe_build.log`.
- The same four exact-output cases are discoverable in
  `test/01_unit/compiler/semantics/preprocessor_when_cfg_spec.spl`, under
  `inactive declaration blank lines`. This SSpec wrapper was added after the
  Rust-backed component diagnostic passed; its full-suite execution remains pending.

Build command (with the reviewed Windows tool environment and
`SIMPLE_NO_STUB_FALLBACK=1`, `SIMPLE_NO_BOOTSTRAP_DELEGATE=1`):

```text
<admitted-producer> native-build --source src/compiler --source src/lib --entry-closure --entry test/fixtures/compiler/cfg_blank_line_probe.spl --cache-dir build/native_probe/phase2_parser/cache --output build/native_probe/phase2_parser/cfg_blank_line_probe.exe
```

Correction after route review: the frozen producer's `bootstrap_main.spl`
routes explicit `--entry` to `run_rt_native_build` when
`SIMPLE_BOOTSTRAP_STAGE3` and `SIMPLE_BOOTSTRAP_STAGE4` are unset. The reviewed
environment used here sets neither. `SIMPLE_NO_BOOTSTRAP_DELEGATE=1` does not
disable this embedded FFI route. Therefore the 20-module result is diagnostic
evidence only: it is **not pure-Simple Phase 2 verification or a qualification
PASS**. Preserve its log and cache as Rust-backed evidence; do not reuse that
cache for a pure compiler attempt. Corrected-source pure positional verification
remains pending. The suitable command shape omits both `--entry` and `--source`.

## Final bounded pure-route attempt

The final authorized attempt used positional entry only with immutable producer
SHA-256 `cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc`.
The producer hash, its existing hello PASS and all six bound runtime-authority
file hashes were checked before launch. Source HEAD was `06dc9880573`.
The attempt used its own `pure-final/cache/phase2/<producer-sha>/cfg-blank-line`
cache, no fallback, a 180-second wall deadline and no RSS cap.

It exited 1 before compiler dispatch with
`SCV-E-ADMISSION: compile-event-journal-missing`; the diagnostic requests
`SIMPLE_SCV_INVENTORY_COLD_INIT=1`, which this launch environment did not set.
No `PureCompilerDriver` trace or executable was produced. This is an admission
blocker, not a failure of the corrected preprocessor and not a verification PASS.
Owned process cleanup was proven. The attempt cap was reached; no retry ran.

Evidence under `build/native_probe/phase2_parser/pure-final/`: `launch.json`,
`result.json`, `compile.stdout.log` and `compile.stderr.log`. The diagnostic
launcher is `build/native_probe/phase2_parser/pure_probe.py`.

No full compiler rebuild, full suite, MCP/LSP gate, or original full CLI rerun
is claimed. The producer binary remains unchanged. The Linux DevHub
`src/lib/nogc_sync_mut/ffi/io.spl` failure is separate: that facade contains no
conditional directives in this revision, so this mechanism does not explain it.
