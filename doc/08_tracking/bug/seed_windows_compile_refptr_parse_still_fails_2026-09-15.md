# Seed Windows `compile` still fails on COFF `.refptr` SMF preservation

Date: 2026-09-15
Status: **RESOLVED 2026-09-15** — stale deployed binary; source was already
fixed. See "Resolution" below.
Host: Windows 11, seed `bin/simple.exe` (16,347,136 bytes, mtime 2026-09-13 15:21)

## Resolution (2026-09-15)

Root cause was (2): the deployed `bin/simple.exe` predated the complete
`.refptr` fix. Rebuilt from current source
(`cd src/compiler_rust && cargo build --release --bin simple`, 3m54s,
39,274,496 bytes) and redeployed to `bin/simple.exe` / `bin/simple`
(21:15). Verified: `bin/simple compile <any .spl> -o *.obj` now succeeds
(llvm and cranelift), emitting a valid object (6,397 bytes for the minimal
env-vars probe). The `native-build` worker lane's `unknown extern function:
rt_env_vars` also disappeared with the rebuild. Remaining native-build
blocker is a separate, pre-existing ambiguity debt:
`doc/08_tracking/bug/jit_co_compiled_definition_ambiguity_debt_2026-09-15.md`.

## Symptom (historical)

Every `simple compile <any .spl> -o out.obj` on this host failed:

Every `simple compile <any .spl> -o out.obj` on this host fails:

```
error: compile failed (...): codegen: Failed to preserve SMF imports/relocations
from object code: Invalid data: Failed to parse object file: Invalid section:
relocation source section .rdata$.refptr is not executable code
```

Same for `--backend=cranelift`. The emitted object is deleted on failure
(`SIMPLE_KEEP_BUILD_INTERMEDIATES=1` did not retain it), so the escaping
stub shape is not yet captured.

## What already exists

`src/compiler_rust/compiler/src/linker/object_parser.rs` phase 0 recognizes
`.rdata$.refptr*` stub sections (prefix + exactly one Absolute relocation
targeting a symbol) and inverts them to GotPcRel; test
`coff_refptr_stub_becomes_gotpcrel_against_real_symbol` covers the shape.
`doc/08_tracking/bug/windows_mcp_native_build_blocked_at_hir_entry_2026-09-01.md`
records the original fix. The failure text it eliminated is back on the
current binary, so either:

1. the current LLVM 18.1.8 emission produces a stub variant phase 0 does not
   match (section name, relocation kind != Absolute, more than one
   relocation, or a non-symbol target — any of these falls through to the
   fail-closed error at object_parser.rs:304), or
2. `bin/simple.exe` predates the complete fix (source history for
   `runtime_sffi.rs`/`object_parser.rs` around 2026-09-08..13 needs a
   rebuilt seed to rule out).

## Reproduction

```bash
cat > /tmp/envvars_test.spl <<'EOF'
extern fn rt_env_vars() -> [(text, text)]
fn main() -> i64:
    val vars = rt_env_vars()
    print "env vars count: {vars.len()}"
    0
EOF
bin/simple compile /tmp/envvars_test.spl -o /tmp/ev.obj
# -> relocation source section .rdata$.refptr is not executable code
```

Interpreter lane is unaffected (`bin/simple run` prints the env count).

## Impact

- Blocks `native-build` on Windows together with the separately tracked
  worker-lane gap (`SCV-E-SNAPSHOT: snapshot-cache-root-not-owned` +
  `unknown extern function: rt_env_vars`, see
  `interpreter_extern_registry_gap_audit_2026-08-27.md` — 79 symbols still
  unresolved in that lane despite the interpreter table having them).
- Blocks the mold/MDSOC++ linker Gate 0 baseline: no real Simple object
  corpus can be produced on this host, so the baseline is recorded as
  blocked-with-reason rather than measured
  (doc/01_research/domain/simple_linker_mold_mdsocpp.md, Gate 0).

## Next steps

1. Rebuild the seed from current source (`src/compiler_rust`,
   `cargo build --release`) and re-run the reproduction — rules out a stale
   binary first.
2. If it still fails, add a keep-intermediates path for the emitted object
   (or a parser debug dump) and compare the stub section against phase 0's
   shape predicate (name prefix, relocation count == 1, kind == Absolute,
   symbol target).
3. Widen phase 0 to the observed shape; add a regression test with the
   captured object bytes.
