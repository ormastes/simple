# stage3 `native-build` SIGSEGV — historical stripped-artifact diagnosis

> **2026-08-14 correction:** the `si_addr=0x118` caller has since been mapped
> with a symbolized same-lineage build to `BorrowChecker.check_function`
> iterating `NLLChecker.errors`. The producer stores that field at slot 4, but
> the consumer was lowered with collided `MirLowering.errors` slot 11. The
> compiler owner is `MirLowering.resolve_field_index`, not the runtime iterable
> helper. Current source already prefers the module-qualified composite layout
> before the module-local numeric `field_map`; see
> `stage3_native_build_segv_generic_codegen_link_path_2026-08-06.md` and
> `test/01_unit/compiler/mir/struct_field_order_module_qualified_spec.spl`.
> The tracked Stage 1/2/3 binary remains stale and byte-identical, so its crash
> is retained diagnostic evidence, not evidence that the current source fix is
> absent. The direct baked `call 0` fault is independent and remains open.

- **Status:** SOURCE CORRECTION IMPLEMENTED; FRESH NATIVE VERIFICATION OPEN.
  The tracked stripped artifact still reproduces the 2026-08-11 SIGSEGV, but
  it predates the module-qualified field-layout correction and cannot establish
  current-source failure. The current prerequisite is completion of the fresh
  pure-Simple Stage 3 build tracked by
  `stage3_hir_contract_model_partial_integration_2026-08-14.md`, followed by
  the hello and module-qualified field-layout probes. The older
  `runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md`
  prerequisite is historical and no longer describes the active frontier.
- **Date:** 2026-08-11
- **Signal:** exit **139** / `SIGSEGV` / `SEGV_MAPERR` (confirmed via `strace`: `si_addr=0x118`, `killed by SIGSEGV (core dumped)`). **Not** 143, **not** 124.
- **Binary under test:** `bootstrap/stage3/simple`, md5 `2244f18ce2e694fb7ca395e9916404c3`, mtime `2026-08-10 12:09`, **stripped** (`nm` → 0 symbols).
  `bootstrap/stage1/simple` and `bootstrap/stage2/simple` are **byte-identical** to it (same md5) — all three are one artifact.
- **`bin/simple` is the RUST SEED** (`bin/release/x86_64-unknown-linux-gnu/simple`, prints the seed banner). There is currently **no working pure-Simple compile path on this host.**

## Minimal repro

```bash
printf '\n' > /mnt/data/nl.spl                 # a single newline — the smallest valid module
printf 'fn main():\n    print("hello")\n' > /mnt/data/hello.spl
cd /home/ormastes/dev/pub/simple
./bootstrap/stage3/simple native-build /mnt/data/nl.spl    ; echo $?   # 139
./bootstrap/stage3/simple native-build /mnt/data/hello.spl ; echo $?   # 139
```

Take `$?` from the command directly — a pipe launders it.

## Bisected trigger: NOT a language construct

| input | bytes | exit | note |
|-------|-------|------|------|
| (empty file) | 0 | **1** | `native entry source not found` — empty read is treated as missing, never reaches codegen |
| `x\n` | 2 | **1** | parse error reported cleanly, exits before the crash site |
| `\n` | 1 | **139** | **crash A** |
| `# nothing\n` | 10 | **139** | **crash A** |
| `fn main():\n    pass\n` | — | **139** | **crash B** |
| `fn main():\n    print(1)\n` | — | **139** | crash B |
| `fn main():\n    val s = "hi"\n` | — | **139** | crash B |
| `fn foo():\n    pass\n` | — | **139** | crash B |

**Every input that parses successfully crashes.** A module containing *only a newline* — zero declarations, nothing to lower — is enough. The trigger is therefore **not** any user-level construct; it is in the fixed prologue of the native-build pipeline.

## Two distinct faults (do not conflate them)

Backtraces (`gdb -batch -ex run -ex "bt 6"`, addresses are absolute; the binary is non-PIE):

**Crash A — declaration-free modules (`\n`, `# nothing`): indirect call through a NULL function pointer**
```
#0  0x0000000000000000
#1  0x000000000067076e
#2  0x0000000000670c39
#3  0x00000000006673e3
#4  0x00000000006683b2
#5  0x000000000040521a
```

**Crash B — any module with a function decl (incl. hello world): dereference of a tagged scalar**
```
#0  0x00000000005178e6
#1  0x00000000005183ae
#2  0x000000000067ac9c
#3  0x000000000066b368
#4  0x000000000040521a
```

## Root cause of crash B (the one that blocks hello world)

Faulting instruction and its guard, at `0x517880` (function entry) — disassembled from the shipped binary:

```
517891: call   517980                  ; produce a value
517899: call   519230                  ; -> r15 (the node)
5178aa: call   517e40
5178b2: call   5192c0                  ; kind/discriminant query -> rax
5178b7: cmp    $0x13,%rax              ; 20-variant enum, kinds 0..19
5178bb: ja     51793d
5178c1: mov    $0x80009,%ecx           ; bitmask = bits 0, 3 and 19
5178c6: bt     %rax,%rcx
5178ca: jae    51793d                  ; only kinds {0,3,19} take the list path
5178cc: and    $0xfffffffffffffff8,%r15
5178d0: mov    0x58(%r15),%rdi         ; read the LIST field at struct offset 0x58
5178d8: call   6a178b                  ; runtime sanitiser (see below)
5178dd: mov    %rax,%r15
5178e0: and    $0xfffffffffffffff8,%rax
5178e4: je     51792d                  ; <-- the ONLY guard: rejects 0..7 and nothing else
5178e6: mov    0x8(%rax),%r14          ; <-- SIGSEGV: reads list length
5178ea: test   %r14,%r14
5178ed: jle    51792d
517900: (loop) call 6a1151 ; index element i
517913: mov (%rbx),%rbp ; call 69d13f ; mov %rbp,(%rbx)   ; push into out-param accumulator
```

At the fault: `rax = 0x110`, `r15 = 0x111`, `si_addr = 0x118`. So the field at offset `0x58` held **`0x111`** — a tagged value with tag `1` whose "pointer" part is `0x110` (272), far below the first mapped page. It is not a list.

**The guard is inconsistent with the runtime's own validator.** The sanitiser the caller just invoked, at `0x6a178b`, performs the *full* three-part check before treating a value as a heap object:

```
6a17ab: cmp    $0x1000,%rbx      ; setb -> reject anything < 0x1000
6a17b7: and    $0x7,%ecx
6a17ba: cmp    $0x1,%ecx         ; setne -> reject tag != 1
6a17c2: jne    6a17ef            ; ...bail out, return the raw value unchanged
6a17d7: cmpl   $0x53545231,(%r14); magic "1RTS" -> reject non-string/non-object
```

It correctly declines to touch `0x111` and returns it verbatim. The **caller** then applies only `and $~7 ; je` — which rejects `0..7` and *nothing else* — and dereferences `0x110`. A value the runtime explicitly refused to treat as a pointer is dereferenced two instructions later.

Underlying defect class: **field-index collision between enum variants sharing one access path.** Offset `0x58` (~the 12th 8-byte slot) is a list-of-children in some of the three admitted kinds `{0, 3, 19}` and a small tagged scalar in at least one of them. This is the same *class* as the prior filings — `stage3_sigsegv_layer_dag_registry_edges_field_collision_2026-08-07.md`, `stage3_selfhost_vtable_field_offset_relro_segv_2026-08-06.md`, `stage3_selfhost_tuple_positional_field_segv_2026-08-02.md`, and the borrow-checker field-index-collision filing — but it is a **different site**: the prior hello-world SEGV was root-caused in the borrow checker, whereas this one faults in a 20-variant enum walker that collects children into an out-parameter list, reached *after* LLVM capability detection. **Same family, new site — not a verified regression of the earlier fix.**

## Where in the pipeline

`strace -f -e trace=execve` shows the crash lands immediately after LLVM toolchain discovery, with no syscalls in between:

```
... llvm-config-18 --version ; uname -s ; llvm-config-18 --libdir
    ; test -f '/usr/lib/llvm-18/lib/libLLVM.so' -o ... ; uname -m ; uname -s
--- SIGSEGV {si_signo=SIGSEGV, si_code=SEGV_MAPERR, si_addr=0x118} ---
```

That sequence is `detect_llvm_capabilities()` → `detect_libllvm_available()` in
`src/compiler/70.backend/backend/llvm_capability.spl:299-355`, followed by host-triple detection
(`detect_host_arch_string` / `detect_host_os_string`,
`src/compiler/95.interp/interpreter/llvm/target.spl:144-180`). The crash is in the first structural
walk after that point. Driver order is
`src/app/cli/bootstrap_main.spl:302-336` → `compiler_driver_run_compile` →
`src/compiler/80.driver/driver_source_pipeline_parsing.spl:262-300`.

Exact source function is **not** identified: the artifact is stripped, so the walker at `0x517880`
could not be mapped back to a `.spl` line. Identifying it requires an unstripped stage3 (see Unblock).

## REFUTED (2026-08-11): the mid-merge hypothesis below

The section that follows was written while the shared worktree held 12 unmerged (`UU`) files.
That state has since been resolved (`git status` reports **0** `UU`; `src/runtime/runtime.h`
no longer starts with `<<<<<<< HEAD`). Re-running the repro against the **same** stage3
artifact (`md5 2244f18ce2e694fb7ca395e9916404c3`) on the resolved tree still yields
**exit 139** for both `\n` and hello world. The half-landed merge was therefore *not* the
cause. The section is retained for the record; treat its conclusion as withdrawn.

The seed's *separate* failure did change: `src/runtime/runtime.h` no longer carries a conflict
marker, and the seed now fails with 63 `clang` errors from a never-implemented unsigned heap
box — see `runtime_native_c_uncompilable_unsigned_box_never_implemented_2026-08-11.md`.

## Strongly correlated (WITHDRAWN — see above): the working tree is mid-merge on exactly the value representation

`git status --porcelain` reports **12 unmerged (`UU`) files**, with **no `.git/MERGE_HEAD` and no `.git/rebase-merge`** — an abandoned merge state left in the shared index:

```
UU src/compiler_rust/compiler/src/codegen/llvm/functions/casts.rs
UU src/compiler_rust/compiler/src/codegen/runtime_sffi.rs
UU src/compiler_rust/runtime/src/value/collections.rs
UU src/compiler_rust/runtime/src/value/core.rs
UU src/compiler_rust/runtime/src/value/heap.rs
UU src/compiler_rust/runtime/src/value/mod.rs
UU src/compiler_rust/runtime/src/value/sffi/equality.rs
UU src/compiler_rust/runtime/src/value/sffi/value_ops.rs
UU src/runtime/runtime.h
UU src/runtime/runtime_native.c
UU src/runtime/simple_core/core_array_query.spl
UU test/01_unit/runtime/runtime_native_focus_test.c
```

Every one of these is a **tagged-value / heap / array representation** file — precisely the machinery
whose invariant crash B violates (tag bits, the `0x1000` floor, the `"1RTS"` magic, list length at
offset 8). The most economical explanation is that **an in-flight change to the tagged-value or
array representation is half-landed, and the stage3 artifact was built across the seam** — i.e. this
is likely a build-time artifact of an unfinished landing rather than a standing bug in committed
`src/compiler/**`. That is a hypothesis, not a diagnosis; it is recorded because it changes what a
fix attempt should do first (finish the merge, rebuild, re-measure) and because it means **any
bootstrap started right now would be invalid**.

**These 12 files were deliberately NOT touched** — they are another concurrent session's mid-flight
work (`.claude/rules/vcs.md`: do not touch a file another session is mid-flight on).

## Second, independent blocker (same cause, different victim)

The **Rust seed** `native-build` path is *also* down, for a different reason — and it is not a
compiler bug at all:

```
error: LLVM native linking failed: Runtime compilation failed: Failed to compile runtime.c:
src/runtime/runtime.h:1:1: error: version control conflict marker in file
```

`src/runtime/runtime.h` literally begins with `<<<<<<< HEAD`. So: seed `native-build` fails at
runtime.c compilation (exit 1), stage3 `native-build` segfaults before it ever reaches a compiler
invocation (exit 139). **Both** paths are down, from **two different causes**, and the runtime.h one
is pure working-copy state that resolving the merge will clear.

## Unblock condition

1. Another session finishes or aborts the abandoned merge — all 12 `UU` paths resolved,
   `src/runtime/runtime.h` no longer starts with `<<<<<<< HEAD`. Until then no bootstrap is valid
   and the seed cannot link a native binary either.
2. Re-measure the table above against a **freshly bootstrapped, unstripped** stage3. If crash B
   survives a clean tree, it is a standing compiler bug and the walker at `0x517880` must be mapped
   to source (build with symbols, or `SIMPLE_STAGE4=1` on an unstripped artifact) before any fix.
3. Independently of the above, the caller-side guard is wrong on its own terms and should be
   hardened to match `0x6a178b`: a `(v & ~7) == 0` test is **not** a sufficient pointer check when
   the runtime's own validator requires `v >= 0x1000`, `(v & 7) == 1`, and magic `"1RTS"`. Any
   codegen site that emits the two-instruction `and $~7 ; je` guard before a field load is
   dereferencing values the runtime has already refused.

## Landing record

An earlier session drafted a landing record here claiming all five guards passed and a
scoped-delta divergence step-over (baseline 856/857). **That landing never happened** — the
file was still untracked in the worktree when this session picked it up, and that draft
record described a push that was never made. It has been removed rather than corrected, to
avoid an unearned provenance claim.

Test-tree divergence is now GREEN (baseline 834), so this range uses a single
`check-test-tree-divergence.shs --ref <NEW>` and needs no scoped-delta escape.

## Evidence commands

```bash
md5sum bootstrap/stage*/simple                       # all three identical
./bootstrap/stage3/simple native-build /mnt/data/nl.spl ; echo $?          # 139
gdb -q -batch -ex run -ex "bt 6" --args ./bootstrap/stage3/simple native-build /mnt/data/hello.spl
strace -f -e trace=execve -o st.txt ./bootstrap/stage3/simple native-build /mnt/data/hello.spl
objdump -d --start-address=0x517880 --stop-address=0x517950 bootstrap/stage3/simple
objdump -d --start-address=0x6a178b --stop-address=0x6a1800 bootstrap/stage3/simple
git status --porcelain | grep '^UU'
```

`--version` and `--help` exit 0; `native-build` on a missing file exits 1 with a clean
`native entry source not found` — so argv handling, startup and error reporting are all intact.
Only the compile path is broken.
