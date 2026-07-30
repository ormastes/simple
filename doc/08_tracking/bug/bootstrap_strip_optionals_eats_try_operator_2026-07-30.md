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
