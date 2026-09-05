# SIMPLE_BOOTSTRAP=1 textually deleted every try-operator; builtin Result/Option unresolvable as qualified constructors under the interpreter

**Status:** FIXED (2026-07-30). Two independent defects found while
root-causing "Result-wrapped APIs are untestable under `bin/simple test`"
(reported by the bencode and json lanes).

## Defect 1: `strip_optionals` ate the `?` try-operator (BOTH engines)

`load_module_with_imports_for_target` applied a bootstrap-leniency TEXTUAL
preprocessor when `SIMPLE_BOOTSTRAP=1`: `strip_optionals` deletes `?`
before whitespace/delimiters to normalize legacy optional-type syntax
(`text?`). The patterns (`"? "`, `"?\n"`, `"?)"`, ...) also match the
try-operator in valid modern code — `val h = half(10)?` lost its `?`
BEFORE the (correct) parser ever ran.

Impact: with SIMPLE_BOOTSTRAP=1 — an env var routinely set just to
suppress the seed-banner warning — `?` was a silent NO-OP in every module
loaded: no unwrap, no Err/None propagation, in BOTH engines (parse-level,
engine-independent). Downstream symptoms looked engine-specific: the JIT
did arithmetic on the un-unwrapped enum pointer (varying garbage ints);
the interpreter errored "type mismatch: cannot convert enum to int".

PROVED by probe bracketing: parser unit test on identical source produces
`Expr::Try`; at runtime with the env set, `Parser::parse` output already
lacked Try (`SIMPLE_TRY_PROBE=1` instrumentation, kept env-gated), and the
postfix Question arm never fired — the token was textually gone.

Fix: the leniency is now FALLBACK-ONLY — the pristine source is parsed
first; only if that parse fails is the legacy `text?`-replace +
`strip_optionals` rewrite applied and reparsed. A source that parses
cleanly is never rewritten. Regression test:
`parser/src/try_probe_test.rs` pins that `?` after a call parses as Try.

## Defect 2: qualified `Result.Ok(x)` / `Option.Some(y)` unresolvable in the interpreter

Builtin Option/Result are compiler-special enums with no source
declaration, so they were absent from the interpreter's enum registries.
Qualified construction failed with "variable `Result` not found" (direct)
or "unknown class Result" (imported modules, e.g. `bencode_decode_value`,
whose dispatch reaches `handle_constructor_methods`' no-class tail — which
never consulted the enum registries at all).

Fix (two parts):
- `evaluate_module_impl` registers synthetic Option/Result `EnumDef`s
  (parsed from a tiny source snippet so the shape always matches the AST)
  into both the module-local map and the thread-local `GLOBAL_ENUMS`.
- `handle_constructor_methods`' no-class tail now performs the same
  qualified-enum-variant fallback the found-class branch already had
  (benefits user enums whose name has no same-named class, too).

Verification (rebuilt seed, forced-interpret lane): bare/qualified
construction, match, is_ok/unwrap, `?` unwrap AND Err/None propagation
all green in both engines with and without SIMPLE_BOOTSTRAP;
`bencode_decode_value("i42e")` matches Ok (the exact previously-failing
integration); spec `test/01_unit/bugs/result_interpret_lane_spec.spl`
(11 examples) runs under the test lane by construction; parser suite
240/240; json_unicode_escape_spec unchanged at its 5 pre-existing reds.

## Retroactive exposure audit (2026-07-30)

Two rewrite implementations exist; their exposure windows differ.

| Lane | Rewrite | `f(x)?` call-form | `r?` var-form | `xs[i]?` index-form | Window |
|---|---|---|---|---|---|
| run/test (module_loader `strip_optionals`) | blind textual strip | EATEN | EATEN | EATEN | 2026-07-01 (7241743871e) -> 2026-07-30 (d8822a3e337, now fallback-only) |
| native-build (`apply_bootstrap_rewrite`, native_project/compiler.rs) | 07-16 root fix preserves `)?` only | kept since 07-16 (eaten 07-01..07-16) | **STILL EATEN at tip** | **STILL EATEN at tip** | 07-16 partial fix; var/index gap OPEN |

PROVED (ad-hoc unit test calling `apply_bootstrap_rewrite` directly):
`CALL_FORM_KEPT=true`, `VAR_FORM_KEPT=false`, `INDEX_FORM_KEPT=false`.

Both rewrites fire only when `SIMPLE_BOOTSTRAP=1` — set both by genuine
bootstrap lanes AND by tooling that merely wants the seed banner
suppressed, which is why the blast radius is wide.

### Who sets SIMPLE_BOOTSTRAP=1 (75 files at tip d8822a3e337)

| Harness family | Files | Exercises `?`-bearing code? | Exposure verdict |
|---|---|---|---|
| `scripts/check` gates (7x check-simpleos-* QEMU evidence, check-stage4-selfhost-parse-memory-multifile, check-bootstrap-nonentry-module-global, bootstrap-stage3 self-test + manifest-verify) | 11 | YES — src/os (28 `?`-bearing files), src/compiler (53), src/lib (273) | EXPOSED 07-01..07-30 (PROVED env+code overlap); per-gate verdict impact UNVERIFIED |
| `.github/workflows` (build-binaries, release, t32-tools-build, t32-tools-release) | 4 | YES — release builds compile src/* | EXPOSED (PROVED overlap); artifacts built 07-01..07-16 had call-form `?` eaten, 07-16..now var/index only |
| `scripts/os` QEMU/OS harnesses | 21 | YES — src/os | EXPOSED (PROVED overlap), verdicts UNVERIFIED |
| `test/` harness wrappers | ~11 | YES | EXPOSED (PROVED overlap), verdicts UNVERIFIED |
| seed pipeline internals (module_loader, execution, native_project) | 3 | n/a | the defect sites themselves |

### Verdict flip actually observed (PROVED, concrete)

Not a named check-script re-run (see UNVERIFIED list below) — the flip
was measured at the API/lane level, which is where the gates' trust
comes from:

- **`bencode_decode_value("i42e")` under the forced-interpret test lane
  flipped FAIL -> PASS.** Before: `error: semantic: unknown class
  Result`, exit 1 — i.e. every spec targeting that Result API could only
  red, and the json lane had to retarget its spec at a lower-level
  Result-free function to get any coverage at all. After (d8822a3e337):
  matches `Ok`. Evidence: same probe file, same env, pre- and post-fix
  seed binaries.
- **`?` semantics flipped no-op -> correct under SIMPLE_BOOTSTRAP=1 in
  BOTH engines.** Before: `val h = half(10)?` bound the whole
  `Result::Ok(5)` enum and Err/None never propagated (JIT then did
  arithmetic on the enum pointer; interpreter errored "cannot convert
  enum to int"). After: unwraps and propagates. Evidence: probe
  `f_h.spl`/`f_err.spl` under both engines, pre/post binaries.

Consequence for the campaign: any gate verdict in the 07-01..07-30
window that depended on `?` behavior in seed-run/tested code is
untrustworthy in BOTH directions — fail-open (an error path whose `?`
never propagated looked clean) and false-red. This is the second
systemic fail-open class found in the verification layer after the
2026-07-28 five-way finding.

### UNVERIFIED-EXPOSED (not re-run this pass — visible, not implied-clean)

Each is a QEMU/stage3-scale job, beyond this pass's budget; re-run
opportunistically on the post-fix seed and record the verdict:

1. `scripts/check/lib/bootstrap-stage3/self-test.shs` (574 lines; sets the env on its seed invocations)
2. `scripts/check/lib/bootstrap-stage3/manifest-verify.shs` (626 lines)
3. `scripts/check/check-stage4-selfhost-parse-memory-multifile.shs`
4. `scripts/check/check-bootstrap-nonentry-module-global.shs`
5. `scripts/check/check-simpleos-memory-leveling-qemu.shs`
6. `scripts/check/check-simpleos-wm-visible-display-evidence.shs`
7. `scripts/check/check-simpleos-qemu-host-gpu-2d.shs`
8. `scripts/check/check-simpleos-x86-64-wm-hello-lifecycle-evidence.shs`
9. `scripts/check/check-simpleos-usb-xhci-qemu.shs`
10. `scripts/check/check-simpleos-servers-qemu.shs`
11. `scripts/check/check-simpleos-wm-fullscreen-evidence.shs`

### LIVE gap (open; owned by the native-build lane, NOT fixed here)

`apply_bootstrap_rewrite` still deletes variable-form (`r?`) and
index-form (`xs[i]?`) try operators at native-build time. Measured
genuine source exposure at tip: **4 sites** — 2 in
`src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl` (lines 355,
384: `val raw_response = read_result?`) and 2 in `src/os`; ZERO in
src/compiler and src/app (their `]?$` matches are `[u8]?` optional
TYPES, which the rewrite legitimately strips). Current bootstrap
artifacts therefore mis-execute `?` at exactly those 4 sites.
Recommended shape is the same fallback-only pattern now used in
module_loader: parse pristine first, rewrite only on parse failure.

### LIVE gap CLOSED (2026-07-30, same session) + exposure count CORRECTED

Fixed by applying the module_loader pattern to the native-build lane:
`compile_file_to_object` now routes bootstrap normalization through a new
`bootstrap_rewrite_if_unparseable(source, preserve)` helper that parses
the pristine source FIRST and calls `apply_bootstrap_rewrite_for_target`
only when that parse fails. The textual rewrite is left untouched — the
`[u8]?`-type vs `xs[i]?`-try ambiguity is not resolvable textually, so
the gate removes the need to resolve it.

**Correction to the exposure count above:** genuine exposure is **2**
sites, not 4. The two `src/os/crypto/ed25519_ops.spl` hits (lines 162,
1025) are COMMENTS (`# Check: r^2 == u?`) — a `?` in a comment is
semantically inert. The real sites are both in
`src/lib/gc_async_mut/gpu/browser_engine/net/h1_client.spl`:

- **line 355 (plain-TCP path)** and **line 384 (TLS path)**:
  `val raw_response = read_result?` where `read_result` comes from
  `read_tcp_response_bytes(...)`. With `?` deleted, `raw_response` held
  the whole `Result` wrapper, so (a) the `Err` from a failed/timed-out
  TCP or TLS read was **never propagated — it was silently swallowed**,
  and (b) the very next guard, `raw_response.len() == 0`, measured the
  wrapper instead of the payload, so the "no response" check could not
  fire either. This was a REAL defect in HTTP error handling under every
  bootstrap native-build, not a latent one.

PROVED (throwaway test against the real file, not landed):
`PARSES=true`, gated output keeps both `= read_result?` occurrences
(`GATED_KEEPS=2`) and is byte-identical to the source
(`gated_eq_src=true`), while the raw rewrite keeps neither
(`RAW_KEEPS=0`).

Landed regression tests (`bootstrap_rewrite_try_operator_tests`):
1. `parseable_source_keeps_all_try_operator_forms` — call, var and index
   forms all survive the gate;
2. `raw_textual_rewrite_still_eats_var_and_index_forms` — vacuity
   anchor proving the gate is load-bearing (same inputs, raw function,
   both eaten); if it ever passes it means the gate stopped mattering;
3. `unparseable_legacy_source_still_gets_optional_type_stripping` — the
   behavior the rewrite exists for is preserved: an unparseable legacy
   source still gets `[u8]?` stripped.

Regressions: all 8 pre-existing `bootstrap_rewrite_tests` still pass
(11/11 in the module, including the pre-existing
`dict_index_try_operator_currently_stripped_documented_gap`, which
documents the raw function's behavior and is unaffected by the gate);
`cargo build --release --bin simple` clean.
