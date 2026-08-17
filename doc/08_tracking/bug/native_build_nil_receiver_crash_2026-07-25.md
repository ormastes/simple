# native-build lane crashes at startup: "field access on nil receiver" (SIGILL, zero output)

- **Date:** 2026-07-25 (evening)
- **Lane:** deployed stage4 `bin/simple native-build`, macOS
- Status: OPEN (P2)
- Status re-verified 2026-08-17 by source inspection (triage shard 02).

## Symptom
`bin/simple native-build --entry <any .spl> --output <bin>` exits 132 (SIGILL) printing
`runtime error: field access on nil receiver` before ANY compile output — even for a
3-line hello probe. The harness's `native-build.out` files are 0 bytes.

## CORRECTED analysis (07-26, after differential probes)
- The crash is **LLVM-backend-specific and LONGSTANDING**, not a same-day regression:
  every binary vintage (03:45, 13:12, tip) crashes identically in
  `MirToLlvm.llvm_type_text` (`udf 0xc11f` nil-receiver trap at the FIRST field access)
  because macOS-host default native-build selects the LLVM backend.
- `--backend=cranelift` native-build WORKS (compiles; separate host-lane `cc linking
  failed` gap + a stray `[DEBUG] 550670556` print left in the link path).
- A source-level nil-guard `if ty == nil: return ...` added before `ty.kind` did NOT
  prevent the trap — suspicion: `==` on a non-nilable struct param is elided or itself
  lowered to a field access, so the guard can't fire. Nil-slip root is upstream
  (`static_.type_`/`body.return_ty`/`local.type_` in core_codegen.spl callers).
- Harness runs 3-4 "timeouts" were MISDIAGNOSED as this crash: the kernel cranelift
  build was silently COMPUTING at 100% single-core CPU under `--log off` — 2700s is
  simply not enough from cold cache post-parser-fixes (run 2 "worked" only because
  parse errors abort early). Run 5 uses 7200s + preserved cache.

## Masked consequences (already burned today)
- SimpleOS WM harness runs 3-4 reported `wm-simple-web-build-timeout` (900s/2700s) with
  EMPTY build logs — the "timeout" was this crash/hang, not slowness. Run 3's
  "0 parser errors" was vacuous.
- MCP `node_repl` artifact rebuild died silently twice (agent lane), then reproduced
  attended: same nil-receiver crash.

## Gate gap (fix alongside)
The redeploy gate (`scripts/check/cert/redeploy_gate/`) runs NO native-build fixture, so
a binary with a dead native-build lane gates 10-11/11 and deploys cleanly — this shipped
twice today. Add a minimal `native-build --entry hello --output tmp && run it` check.
