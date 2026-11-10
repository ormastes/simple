# Native codegen drops the receiver for non-`me` (`fn`) instance methods — SIGSEGV in `native-build --entry-closure`

- **ID:** native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25
- **Status:** FIXED (2026-11-11 lane compiler5: source-fixed; the OPEN text below was a stale resurrection by merge 9e7e7a526edb — see addendum)
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

Pre-bridge crash sites in the CLI were the `resolve_cache.contains_key` calls;
the `discovered.contains` calls carried the same latent receiver bug.

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

**Canonical receiver-ABI remediation (current source):** plain `fn` in a class,
struct, enum, impl, or extension body is an immutable instance method even when
it has zero explicit source arguments. The Rust parser owns that classification
and emits the ABI-visible leading `self`; only explicit `static fn` is
receiver-less. Native import discovery carries both declared arity and an
explicit free/instance receiver kind, while Cranelift rejects missing metadata,
missing receiver slots, and contradictory linked signatures before argument
adaptation. Pure-Simple HIR/MIR retains the owner-context receiver and fails
closed if an instance method reaches MIR without it. No `me` source workaround
is part of this repair.

**Bootstrap bridge (closure verified, full self-host pending):**
`_native_build_entry_closure` uses built-in `Dict<text, bool/text>` for its
discovery and resolution tables. This keeps hashed lookup while avoiding the
seed-generated `HashSet.contains` and `HashMap.contains_key` calls in this
bootstrap-only walker. A rebuilt generation-1 CLI traversed 908 closure sources
and entered generation-2 parsing instead of crashing. The full build remains
blocked by the separately tracked self-host parse performance problem. This is
not the ABI fix: custom non-`me` instance methods remain affected, so this bug
stays OPEN until caller and callee ABI change atomically.

The walker retains an explicit `HashMap` import because built-in `Dict.entries`
currently lowers to that implementation. Removing the import omitted its object
from the entry closure and produced an undefined `HashMap.entries` at link; the
source contract protects this non-obvious closure root.

## Impact on current work

The showcase-matrix "compiled lane" does **not** need this fixed first: use the
Rust-built `bin/simple` for `native-build` instead of a session-built native CLI.

## Addendum 2026-11-11 — lane compiler5 (P3 batch-5 triage): FIXED (source)

- **This doc's "OPEN (NOT fixed)" text is stale.** It was reconciled to
  "SOURCE FIXED; native self-host execution pending" by `22a899d5968c`
  (2026-07-26, "docs(native): reconcile immutable receiver ABI status"), but
  merge `9e7e7a526edb` (PR #7597, 2026-11-07) re-created this file as a new file
  carrying the pre-2026-07-26 content, resurrecting the OPEN status. The source
  fix stands in current source.
- **Source verification (current tree):**
  - `src/compiler/50.mir/_MirLowering/function_lowering.spl:680-685` — a
    fail-closed gate: every non-static instance method (including immutable
    zero-argument `fn`) MUST have an ABI-visible receiver in parameter slot
    zero, else `error_fatal`. `is_me_receiver` now controls only value-copy
    semantics, not receiver emission.
  - Both MIR method-call routes prepend the receiver operand
    (`lower_receiver_and_args` and the pre-lowered writeback route, per the
    22a899d5968c reconciliation); test coverage added by `7554bc6ff18e`
    (2026-07-26) incl. `check-native-immutable-fn-receiver.shs` and
    `test/01_unit/compiler/native_immutable_fn_receiver.spl`.
- **Verification run on the fresh seed** (build-commit 46fe8f6b6def,
  `--mode=interpreter --no-cache`):
  `test/01_unit/compiler/hir/class_method_bodies_reachable_spec.spl` — 4/4 PASS,
  including "keeps the ABI receiver on an immutable zero-argument fn method"
  (`fn has_value() -> bool: self.value > 0` must lower with `self` as param 0).
- **Still pending (environmental, not a defect):** native self-host execution
  proof of the new ABI — blocked by the self-host parse-performance blocker
  (this doc's own "Bootstrap bridge" section) and, on this Windows host, by the
  known native-build hang (log completes, no binary, process never exits;
  confirmed with a trivial probe, not retried per lane rules).
