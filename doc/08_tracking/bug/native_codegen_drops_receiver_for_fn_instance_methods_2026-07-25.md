# Native codegen drops the receiver for non-`me` (`fn`) instance methods — SIGSEGV in `native-build --entry-closure`

- **ID:** native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25
- **Status:** SOURCE FIXED; native self-host execution pending
- **Severity:** high — the defective compiler silently passed explicit
  arguments into the `self` slot for `fn`-declared instance methods
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

The historical lowering gated receiver emission on mutability. In current
source, `is_me_receiver` at
`src/compiler/50.mir/_MirLowering/function_lowering.spl:194` only controls
value-copy semantics; both method-call routes unconditionally prepend the
receiver operand.

Pre-bridge crash sites in the CLI were the `resolve_cache.contains_key` calls;
the `discovered.contains` calls carried the same latent receiver bug.

## Scope

Native artifacts produced by the defective compiler were miscompiled. The
interpreter path did not exercise this native calling convention, which is why
the defect was invisible there.

**Not** related to `bootstrap_stage4_selfhost_parse_memory_blowup_2026-07-20.md`:
the crash is in the CLI's import-closure BFS, before any parsing (that doc has
zero hits for `contains_key|entry_closure|hashmap|HashMap`).

## Source repair and pending execution

`lower_receiver_and_args` and the pre-lowered writeback route
`build_args_from_receiver` both explicitly push `mir_operand_copy(receiver_local)`
before explicit arguments. The existing source regression
`test/01_unit/compiler/backend/cranelift_aggregate_runtime_abi_spec.spl` pins
both routes and the cross-module `fn` fixture: zero-argument `read()` and
one-argument `matches(...)`. `scripts/check/check-native-immutable-fn-receiver.shs`
is the native execution receipt and forbids the Rust seed.

**Known stopgap, deliberately NOT applied:** changing `fn contains_key` → `me
contains_key` (`hashmap.spl:99`, `hashset.spl:112`) would unblock the immediate
crash. That is a workaround masking a general ABI defect — every other `fn`
instance method would have remained miscompiled under the defective compiler.
Recorded here rather than normalized, per the project rule against silently
absorbing a broken form.

**Bootstrap bridge (closure verified, full self-host pending):**
`_native_build_entry_closure` uses built-in `Dict<text, bool/text>` for its
discovery and resolution tables. This keeps hashed lookup while avoiding the
seed-generated `HashSet.contains` and `HashMap.contains_key` calls in this
bootstrap-only walker. A rebuilt generation-1 CLI traversed 908 closure sources
and entered generation-2 parsing instead of crashing. The full build remains
blocked by the separately tracked self-host parse performance problem. A
fresh admitted pure-Simple executable must run the existing native receipt
before this can be closed; the Rust seed is not valid evidence.

The walker retains an explicit `HashMap` import because built-in `Dict.entries`
currently lowers to that implementation. Removing the import omitted its object
from the entry closure and produced an undefined `HashMap.entries` at link; the
source contract protects this non-obvious closure root.

## Impact on current work

The showcase-matrix compiled lane requires an admitted pure-Simple executable.
Until that executable runs the native receipt, execution evidence remains
pending.
