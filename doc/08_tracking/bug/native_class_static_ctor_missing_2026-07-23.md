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
