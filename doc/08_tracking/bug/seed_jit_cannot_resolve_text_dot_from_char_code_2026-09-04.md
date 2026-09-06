# Seed JIT cannot resolve `text_dot_from_char_code`, killing any `simple run` that calls slang's manifest parser

- **Filed:** 2026-09-04
- **Status:** Open
- **Severity:** blocks `simple run` for any program whose call graph reaches
  `text.from_char_code`, including the whole slang model-loader path.
- **Binary under test:** `src/compiler_rust/target/bootstrap/simple`
  (154,560,904 bytes, mtime 2026-09-04 09:47). `bin/simple` did not exist during
  this session -- `bin/release/aarch64-unknown-linux-gnu/` was emptied at 11:35
  by an in-flight bootstrap owned by another session -- so the seed was the only
  usable binary and every measurement below is from it.

## Symptom

```
$ src/compiler_rust/target/bootstrap/simple run /tmp/iso3.spl
PANIC can't resolve symbol text_dot_from_char_code
  location=src/compiler_rust/vendor/cranelift-jit/src/backend.rs:345:21
```

`/tmp/iso3.spl` is three lines: it imports
`std.gc_async_mut.slang.model_executor.model_loader.manifest.{parse_manifest}`
and calls it once with the text `"nonsense"`. Nothing else is needed to
reproduce.

## Why it matters here

`parse_manifest` is slang's phase-A1 manifest parser. It is reached from
`serving_models.discover_models`, which is reached from
`api_server.slang_api_dispatch`, which is the whole of slang's OpenAI-compatible
HTTP surface. So `simple run src/app/slang_server/main.spl` starts and listens
happily -- the panic is at JIT *compile* time for the function, and the function
is only compiled when first called -- and then dies on the first request that
reaches a model lookup. A server that starts cleanly and dies on request one is
strictly worse than one that refuses to start.

## Scope: JIT only, not the interpreter

The same code is green under the interpreter. Both slang specs pass:

```
$ SEED test test/01_unit/lib/gc_async_mut/slang/entrypoints/openai_api_spec.spl --mode=interpreter
Results: 18 total, 18 passed, 0 failed
$ SEED test test/01_unit/lib/gc_async_mut/slang/model_executor/native_formats_spec.spl --mode=interpreter
Results: 14 total, 14 passed, 0 failed
```

So this is not a defect in slang, in `manifest.spl`, or in the specs. It is a
gap in the seed's JIT symbol table, and it is invisible to the test suite
because the test suite does not use the JIT.

`simple run` has no interpreter escape hatch: `--interpret`, `--no-jit` and
`--mode=interpreter` are all parsed as input FILENAMES and fail with
`Cannot read "--mode=interpreter": No such file or directory`. That is a second,
smaller defect -- a flag the test runner accepts should not be silently
reinterpreted as a path by `run`.

## Cause

`text_dot_from_char_code` exists and is exported by the runtime crate:

- `src/compiler_rust/runtime/src/value/collections.rs:3743`
  -- `pub extern "C" fn text_dot_from_char_code(code: i64) -> RuntimeValue`

The cranelift backend declares it for import:

- `src/compiler_rust/compiler/src/codegen/instr/closures_structs.rs:2143`
  -- `declare_function("text_dot_from_char_code", Linkage::Import, &sig)`

But the JIT only registers symbols listed in `RUNTIME_SYMBOL_NAMES`
(`src/compiler_rust/common/src/runtime_symbols.rs:385`, consumed by
`register_runtime_symbols_from_provider` at
`src/compiler_rust/compiler/src/codegen/jit.rs:558-568`), and that table
contains **no `text_dot_*` entries at all**:

```
$ grep -c 'text_dot_' src/compiler_rust/common/src/runtime_symbols.rs
0
$ grep -c 'from_char_code' src/compiler_rust/common/src/runtime_symbols.rs
0
```

The fallbacks do not save it either: `elf_utils::resolve_runtime_symbol` and
`lookup_with_dlsym` both need the symbol to be dynamically visible in the
process, and it is statically linked into the seed without `-rdynamic`. So the
import resolves to nothing and cranelift-jit panics at finalize.

Note that `jit_import_resolves` (`jit.rs:576`) exists precisely to detect this
class of unresolvable import -- its own comment says an unresolved import "is
bound to a NULL GOT slot and would SIGSEGV when called". Something is declaring
this import without going through that check.

## Fix sketch (not applied)

Add `"text_dot_from_char_code"` to `RUNTIME_SYMBOL_NAMES` and rebuild the seed.
Deliberately NOT done in this session: a bootstrap
(`scripts/bootstrap/bootstrap-from-scratch.sh --stop-after-stage3`, pid 343001)
was running throughout and owns `src/compiler_rust/target/`; a concurrent
`cargo build` would have contended for that directory, for the 8 cores it was
using, and for memory on a host that was at 98 GB of 121 GB during the model
load. The one-line table addition is safe; the rebuild is what needs a quiet
machine.

Whoever applies it should check the whole `text_dot_*` family rather than this
one name -- a table with zero entries for a family that the codegen declares
imports from is unlikely to be missing exactly one.

## Reproduction

```bash
cat > /tmp/iso3.spl <<'EOF'
use std.gc_async_mut.slang.model_executor.model_loader.manifest.{parse_manifest}
fn main():
    match parse_manifest("nonsense"):
        Err(_): print "ERR-OK"
        Ok(_): print "OK"
EOF
src/compiler_rust/target/bootstrap/simple run /tmp/iso3.spl    # PANIC
```
