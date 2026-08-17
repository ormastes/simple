# native (entry-closure): class static-method calls silently lower to 0; class constructors never emitted

- **Date:** 2026-07-23  **Status:** OPEN (worked around in apps; structs fine)
- **Severity:** critical for any native app using `class` — silent nil at
  runtime, no compile error.

## Symptom
```
class Opts:
    log_mode: text
    static fn defaults() -> Opts: Opts(log_mode: "human")
var opts = Opts.defaults()     # lowers to `const 0` — call VANISHES
opts.log_mode = "llm"          # store through nil → SIGSEGV at address 0
```
Probe-verified in W82 IR (`/tmp/simple_llvm_2484761.ll`):
- call site: `%l4 = add i64 0, 0 ; const int` (no call emitted, no diagnostic)
- `define i64 @defaults()` EXISTS (bare name, alwaysinline) — resolution gap is
  at the call site, not the definition
- constructor is `declare i64 @Repro2Options(...)` — DECLARED only, never
  defined; whole chain then dead-stripped
- real-world hit: `simple_lsp_mcp_server` SIGSEGV at startup —
  `parse_log_options` returned nil (`SimpleLogOptions.defaults()` dropped,
  empty-args loop skipped all field writes, caller deref crashed)

## Class vs struct
`struct` + free-fn constructor works (campaign fix 0faa51502fd); only `class`
statics/ctors are broken in the bootstrap entry-closure path.

## Workaround applied
Apps converted the offending `class` to `struct` + module-level constructor fn
(simple_lsp_mcp/main.spl SimpleLogOptions).

## Fix direction
MIR lower_call/MethodCall: a MethodCall whose receiver is a CLASS NAME (not a
value) must resolve to the emitted static symbol (bare/qualified name parity
with the emitter), and bootstrap class lowering must emit constructor bodies
(currently declare-only). Any unresolved call must be a loud compile error,
never `const 0`.

Related: text.from_char_code static-call gap
(text_static_method_hir_lowering_2026-07-23.md) — same
"static call on type name" family.

## 2026-08-17 CRIT-C4 partial close (SOURCE READING, no execution)

The "Any unresolved call must be a loud compile error, never `const 0`" half of
the Fix direction IS now implemented in
`src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl`: `:3176`
`self.error(...)`, `:3185` a WARNING print, and `:3208` an `rt_panic` emitted
ahead of the retained const-0 placeholder — fail closed. The C4 TSV evidence
column ("no loud-error-on-unresolved-call guard found") is therefore stale.
The static-call RESOLUTION half also has an implementation now: the Unresolved
arm (`:2660-2692`) resolves `static::{recv}::{method}` via `struct_method_syms`,
then `symbols.lookup_method_in_type`, then
`symbols.lookup_unique_static_method(method)`.
STILL UNVERIFIED: whether class CONSTRUCTOR bodies are now emitted (the
"`declare i64 @Repro2Options(...)`, never defined" half). That needs an
entry-closure native build, which was not achievable on this host (load 66-90,
a native check script produced no output in 25 minutes).
