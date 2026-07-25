# Native codegen drops the receiver for non-`me` (`fn`) instance methods — SIGSEGV in `native-build --entry-closure`

- **ID:** native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25
- **Status:** OPEN (root-caused with disassembly, NOT fixed)
- **Severity:** high — silent ABI mismatch; any natively-compiled caller of a
  `fn`-declared instance method passes arguments into the `self` slot
- **Found via:** `native-build` crashing on a showcase entry (showcase was a red
  herring — see minimal repro)

## Symptom

A natively-compiled `simple` binary segfaults during `native-build --entry-closure`:

```
REAL_EXIT=139, core dumped, ZERO diagnostic output
```

## Minimal repro

An 82-byte file suffices — **any entry with ≥1 non-relative dotted `use`**, built
with `--entry-closure` by a **natively-compiled** CLI:

```
use std.io_runtime.{env_get}
fn main(): print("tiny")
```

`--entry-closure --source src/lib` → exit 139.
The **same file with zero `use`** builds fine (exit 0, artifact produced).
Closure size, `--source` count, and the GC-tier `std.gpu.engine2d` import are all
**irrelevant** — the original suspicion that this was 2D/GC-tier-specific is wrong.

## Root cause (proved by disassembly, not inference)

```
#0 HashMap_dot_contains_key+575   mov 0x8(%r9),%r9      <-- SIGSEGV
#1 io___CliCompile__compile_targets___native_build_entry_closure+2550
#2 cli_native_build  #3 main  #4 spl_main  #5 main
```

Callee `HashMap.contains_key` (`src/lib/nogc_sync_mut/src/collections/hashmap.spl:99`)
expects `self` in `%rdi` and `key` in `%rsi` — it tag-checks `%rsi` against the
text magic `0x53545231` (`"STR1"`).

The call site emits **one** register:

```
+2513  call _nb_join_segments      ; seg_key (a text)
+2518  mov  %rax,%r12
+2544  mov  %r12,%rdi              ; <-- text lands in the SELF slot
+2547  call *%r10                  ; %rsi never set
```

So `self` is a `text`. `self.buckets` loads word 0 of the text object =
`0x53545231`; its low 3 bits are `1`, exactly the heap-pointer tag, so codegen
untags to `0x53545230` and dereferences `+8` → SIGSEGV. `rcx` held
`0x7363696870617267` = `"graphics"`, confirming the receiver is the module-path
string.

**The discriminator is `me` vs `fn`.** Within the same caller:

| callee | declared | registers emitted | correct? |
|---|---|---|---|
| `HashSet.insert` (`hashset.spl:53`) | `me` | 2 (`%rdi` + `%rsi`) | yes |
| `HashSet.contains` (`hashset.spl:112`) | `fn` | 1 | **no** |
| `HashMap.contains_key` (`hashmap.spl:99`) | `fn` | 1 | **no** |

`src/compiler/50.mir/_MirLowering/function_lowering.spl:194` gates the receiver on
`fn_.is_mutable` (`is_me_receiver`) — consistent with the observed divergence.

Crash sites in the CLI: `src/app/io/_CliCompile/compile_targets.spl:673` and `:691`
(`resolve_cache.contains_key`); latent at `:648/:657/:666/:680` (`discovered.contains`).

## Scope

`bin/simple` → `bin/release/x86_64-unknown-linux-gnu/simple` is **Rust-built**, so
it runs this path interpreted and is **unaffected**. Only natively-compiled
self-hosted binaries are miscompiled. This is why the defect is invisible in
normal tooling use and only appears once a self-hosted CLI is built and used to
`native-build`.

**Not** related to `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`:
the crash is in the CLI's import-closure BFS, before any parsing (that doc has
zero hits for `contains_key|entry_closure|hashmap|HashMap`).

## Fix

**Correct fix:** pass the receiver for **all** instance methods, not just `me`
ones. This changes the calling convention for every non-`me` method in the
codebase — caller and callee must flip **atomically**, or every native binary
breaks. It needs its own bootstrap-verified change, not a patch tucked inside
unrelated work.

**Known stopgap, deliberately NOT applied:** changing `fn contains_key` → `me
contains_key` (`hashmap.spl:99`, `hashset.spl:112`) would unblock the immediate
crash. That is a workaround masking a general ABI defect — every other `fn`
instance method in the codebase stays miscompiled and will fail the same way.
Recorded here rather than normalized, per the project rule against silently
absorbing a broken form.

## Impact on current work

The showcase-matrix "compiled lane" does **not** need this fixed first: use the
Rust-built `bin/simple` for `native-build` instead of a session-built native CLI.
