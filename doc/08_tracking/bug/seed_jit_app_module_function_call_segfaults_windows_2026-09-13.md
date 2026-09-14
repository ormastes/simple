# Seed JIT (Windows): calling any function from an `app.*` module segfaults

- **Date:** 2026-09-13
- **Component:** Rust seed JIT (`simple.exe run`, default execution mode)
- **Host:** Windows 11, x86_64-pc-windows-msvc, seed
  `C:/Users/ormas/dev/simple/bin/release/x86_64-pc-windows-msvc/simple.exe`
  (`Simple Language v1.0.0-rc.1`, seed banner)
- **Severity:** crash (rc 139, SIGSEGV), nothing on stderr
- **Status:** open (seed defect). Not fixable in `.spl` source: the crash
  happens on a one-line function with no body logic.

## Symptom

`cli_current_exe_path()` (`src/app/io/cli_ops.spl`) segfaults when called from
a script under `simple run`. It does not crash under `simple test`, because the
seed forces interpreter mode for the test-runner apps
(`test_daemon_app_requires_interpreter`, `src/compiler_rust/driver/src/main.rs:1498`).
Any other JIT caller of an `app.*` function (native build, JSON wrapper, compile
targets, Electron launcher, ad-hoc scripts) is exposed.

## Minimal repro

`src/app/zz_n/zz_nmod.spl`:

```simple
pub fn triv0() -> i64:
    42
```

`main.spl` (any location, run with an absolute path):

```simple
use app.zz_n.zz_nmod.{triv0}

fn main():
    print "n0 start"
    print "n1 {triv0()}"
```

```
simple.exe run C:/tool-fix/main.spl                      -> n0 start, then rc=139
SIMPLE_EXECUTION_MODE=interpret simple.exe run ...       -> n0 start, n1 42, rc=0
```

An existing module crashes the same way, 3/3 runs:

```simple
use app.io.env_ops.{cwd}

fn main():
    print "e0 start"
    print "e1 {cwd()}"
```

## Discrimination (all JIT unless noted; each a fresh process)

| Callee location | Callee | Result |
|---|---|---|
| `app.zz_n.zz_nmod` (new dir) | `pub fn triv0() -> i64: 42` | rc 139 |
| `app.io.zz_q0_mod` (new file) | `pub fn triv_k(a: text) -> text: a` | rc 139 |
| `app.io.env_ops` | `cwd()` | rc 139 (3/3) |
| `app.io.cli_ops` | `_cli_source_entry_executable(...)` | rc 139 |
| same `app.io` trivial module, **interpret** mode | `triv_k` | rc 0 |
| `std.zz_lib_mod` (`src/lib/`) | same `triv_k` | rc 0 (3/3) |
| root-level module (`use zz_mod`) | same `triv_k`, or a full copy of `cli_ops.spl` | rc 0 |
| inline in the script | the same string/`substring`/`starts_with`/`last_index_of` code as `_cli_resolve_argv0` | rc 0 |

So the crash is determined by the callee's module living under the `app.`
namespace, not by the function body, argument types, the module's imports and
externs, or the process-level cache var in `cli_ops.spl`. (All crashes in this
table predate or are independent of that cache.)

## Possibly related

`seed_jit_function_local_use_segfaults_2026-09-13.md` is the same crash
signature (JIT only, rc 139, silent, interpreter fine) for a different trigger.
They may share a root in how the JIT resolves or loads cross-module callees.

## Workaround

Run with `SIMPLE_EXECUTION_MODE=interpret`, or call `app.*` code only from the
interpreter-forced app entries (`simple test`, test daemon).

## Root cause — FIXED 2026-09-14

Shared root with `seed_jit_function_local_use_segfaults_2026-09-13.md`, as
suspected: `src/compiler_rust/compiler/src/codegen/jit.rs`'s
`dlsym_resolves`, the Windows half of the JIT's unresolved-import guard
(`first_unresolved_import_called` -> `jit_import_resolves` ->
`dlsym_resolves`), unconditionally returned `true` on Windows:

```rust
#[cfg(windows)]
fn dlsym_resolves(_name: &str) -> bool {
    // Conservative on Windows: assume resolvable ...
    true
}
```

The guard exists precisely to catch a cross-module Simple function symbol
that `cranelift-jit` cannot resolve to a real address at `finalize_definitions`
time (it falls through to a NULL GOT slot, which SIGSEGVs on first call — see
`compile_module`'s comment on `first_unresolved_import_called`). On Unix the
guard mirrors cranelift-jit's own fallback resolver (`dlsym(RTLD_DEFAULT,
name)`) and correctly answers `false` for an unresolvable name, so the module
de-JITs to the interpreter instead of finalizing. On Windows the guard always
answered `true`, so it could never fire: `triv0` (and any other `app.*`
function reached through a non-flattening cross-module call) resolves to
neither a registered runtime symbol nor a real process/CRT export, finalizes
with a NULL import slot, and SIGSEGVs silently on the first call — exactly
the symptom in this doc.

Fix: `dlsym_resolves` on Windows now genuinely probes resolvability via
`GetProcAddress`, mirroring cranelift-jit's own Windows fallback resolver
(`cranelift-jit-0.116.1/src/backend.rs::lookup_with_dlsym`: try the running
executable image, then `ucrtbase.dll`). With the real check in place, both
repros in this doc now correctly de-JIT with a loud, greppable
`[jit-fallback] unresolved external symbol '...'` message and finish with
`rc=0`, instead of SIGSEGVing.

Regression coverage: two new Rust tests in
`src/compiler_rust/compiler/src/codegen/jit_tests.rs` —
`dlsym_resolves_rejects_a_nonexistent_symbol_on_windows` (Windows-only, tests
the fixed resolver directly) and
`test_jit_unresolved_extern_call_refuses_to_finalize_instead_of_null_jumping`
(all platforms, end-to-end through `compile_module`).

Verified on `C:/tool-jit/target/release/simple.exe` (sha256 of the pre-fix
deployed binary `6094dcae291aa984973ccd681f956e67a7a60543ab99f76a29313fbbfdee96d1`
reproduces both crashes; the freshly rebuilt binary carrying this fix,
sha256 `e28df9022d3e97c13b6a55e7571195d8422e3df0733b03274fdbbb4a6792d263`,
answers `rc=0` for both this doc's repro and
`seed_jit_function_local_use_segfaults_2026-09-13.md`'s p6 repro).

**Status: FIXED**, pending PR landing.
