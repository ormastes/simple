# Flat --entry-closure lane: text module-global values lose textness through function returns (prints pointer as number)

Status: FIXED
Status re-verified 2026-08-17 by source inspection (triage shard 01).

**Date:** 2026-07-24
**Severity:** Medium (silent wrong output; no crash after the rt_env_get ABI fix)
**Lane:** seed `native-build --entry-closure` (SIMPLE_BOOTSTRAP=1)

## Fixed in the same change set

1. **llc duplicate `%lN`**: functions containing `LoadGlobal`/`StoreGlobal` were
   whole-function rejected by `ssa_instructions_supported_for_alloca`
   (var_reassign_ssa.spl knew neither kind), so branch-assigned locals like
   `val env_set = env_get(K) ?? ""` kept two SSA defs of one name. Fixed by
   teaching the alloca lane both kinds (gate exceptions, written-local id,
   operand collection, def rename, StoreGlobal operand rewrite) — the #135
   CallIndirect precedent.
2. **Slot typing**: `lower_static` (50.mir module_lowering.spl) mapped an
   UNANNOTATED `var X = "lit"` through `Infer -> MirType.i64()`, erasing
   textness at MIR; the i64 slot then took a `getelementptr` initializer that
   llc rejects (and reads stringified the address). A plain `StringLit` static
   now always slots `Opaque("str")` (ptr slot, valid gep constant).
3. **rt_env_get ABI crash**: the .spl extern `rt_env_get(key: text)` is 1-arg
   but the C ABI is `(const uint8_t*, uint64_t len)` — vararg declare hid it;
   len read garbage; memcpy SIGSEGV at startup for any env_get caller. Fixed
   native-only: new `rt_env_get_value(int64_t)` C shim (tag-sniffs heap-string
   handle vs raw rodata cstr) + backend remap of 1-arg `rt_env_get`/bare
   `env_get` calls to it (2-arg callers keep the real ABI).

## Still open (this bug)

Repro `src/app/staticrepro` (build-only app, mirrors `_mcp_init_tool_set`):
`_SR_MODE` written from a branch-assigned env/argv value, read back via
`fn _sr_get_mode() -> text: _SR_MODE`, printed with `"mode=" + ...`.

- Expected: `mode=core` / `mode=all`
- Actual: `mode=<large integer>` (pointer/handle value stringified as int),
  no crash. `src/app/staticrepro2` (const-only global printed DIRECTLY in
  main) prints correctly after fix 2 — the loss happens when the value flows
  through a FUNCTION RETURN (`-> text` return registers as i64 at the call
  site) and/or a stored dynamic value is read back without text marking.

Impact on MCP: `_MCP_TOOL_SET`/`_MCP_TRANSPORT_MODE` comparisons see wrong
text after dynamic stores, so env/flag overrides mis-select until this is
fixed; startup no longer crashes.

Note: `__module_init_*_dynamic` functions are emitted and collected on this
lane; the link shim (llvm_native_link.spl) is responsible for invoking them —
verify that path fires for flat-lane binaries when picking this up.

The mutglobal read/write hooks are documented as follow-up work in
50.mir module_lowering.spl's lower_static block comment; this is that gap.

## Addendum: ARRAY module globals have no storage at all on the flat lane

`var X: [T] = []` never reaches `MirModule.statics` (`lower_const_expr` cannot
fold the empty array literal and `runtime_module_initializer_supported`
rejects ArrayLit), so there is no `@g_...` global, `try_lower_global_read`
returns nil, and every read/method-call on such a global (e.g.
`DAP_SESSIONS.push(...)`, `for s in DAP_SESSIONS`) flows into the
"undefined variable" / #143 fallbacks. Those fallbacks previously emitted
UNDEFINED result locals (`ret %lN` / `use of undefined value` at llc —
gate rMCPR8's blocker); they now emit defined `Const 0` results and the
for-in stub returns its (defined) panic-message local, so such programs
BUILD and fail loudly at runtime when the affected function is actually
called. Real support needs: statics storage for array globals (ptr slot,
zeroinit) + a module-init `rt_array_new` store + receiver/read wiring.
Repro: `src/app/staticrepro` (`_SR_ITEMS` push + for-in; prints the #143
panic at runtime, builds clean).
