# Self-hosted compiler SIGSEGVs in `load_sources`: tail-tuple method receiver lowered to a literal NULL

- **ID:** selfhost_load_sources_nil_receiver_tail_tuple_2026-08-17
- **Status:** ROOT-CAUSED BY DISASSEMBLY; fix not landed (verification requires a
  full bootstrap, and the seed's own `native-build` is currently red — see
  "Second, independent blocker" below)
- **Severity:** critical — stage 2 and stage 3 build 865 modules each but cannot
  compile *any* input, so nothing self-hosted can be deployed
- **Found via:** `native-build` of a two-line hello-world on stage 3

## Reproduction (exit status read directly into a variable, never through a pipe)

```
$ printf 'fun main()\n  print("hi42")\n' > p.spl
$ ./s3 native-build p.spl -o p.bin > out.txt 2> err.txt
$ rc=$?; echo "RC=$rc"
RC=139                       # Segmentation fault (core dumped)
```

`s3` = a private copy of
`/mnt/data/worktrees/simple-phase2/build/bootstrap/stage3/x86_64-unknown-linux-gnu/simple`
(35,307,368 bytes, 2026-08-17 12:42). Stage 2 (same size, 12:26) behaves
identically. Last stdout before the fault:

```
[build] load_sources unknown/unknown step 0/6 starting
[build] source_closure 1/1 step 1/6 complete
```

Not a stage-4-only defect: it reproduces on stage 2 and stage 3.

## Faulting frame

```
Program received signal SIGSEGV
#0  compiler__driver__driver_types__CompileContext_dot_has_errors+8
#1  compiler__driver__driver_source_pipeline_loading__CompilerDriver_dot_load_sources_impl+8068
#2  compiler__driver__driver_orchestration__CompilerDriver_dot_compile
#3  compiler.driver.driver.compiler_driver_run_compile
#4  app.cli.bootstrap_main.run_native_build_bootstrap
#5  spl_main   #6 main
```

`+8` is the first instruction of `has_errors` that dereferences `self`
(`fn has_errors() -> bool: self.error_count_value > 0`,
`src/compiler/80.driver/driver_types.spl:982`).

## Root cause — the receiver is a *literal zero*, not a corrupted pointer

Call site, `load_sources_impl+8056`:

```
+8056  48 31 ff     xor    %rdi,%rdi          <-- self := NULL, unconditionally
+8059  48 8d 15 ..  lea    0x18418(%rip),%rdx # CompileContext_dot_has_errors
+8066  ff d2        call   *%rdx              <-- SIGSEGV inside callee
+8068  4d 31 ed     xor    %r13,%r13          <-- tuple element 0 := NULL too
```

Source, `src/compiler/80.driver/driver_source_pipeline_loading.spl:297-303`:

```
        var loaded_ctx: CompileContext = self.ctx
        loaded_ctx.sources = all_sources
        if source_trace:
            print "[load_sources] total {all_sources.len()}"

        (loaded_ctx, not loaded_ctx.has_errors())
```

The same local resolves **correctly** one statement earlier. The field store
`loaded_ctx.sources = all_sources` at `+7900..+7946` loads the local from its
stack slot and stores through it:

```
+7908  mov 0x3b8(%rsp),%r10
+7916  and $-8,%r10                 ; strip tag
+7928  mov (%r10),%r14
+7938  mov 0x408(%rsp),%rax         ; all_sources
+7946  mov %rax,0x38(%rdx)          ; loaded_ctx.sources = all_sources
```

So `loaded_ctx` has a live stack slot at `0x3b8(%rsp)`, and the mutation is
lowered properly — but **both** of its mentions inside the function's
implicit-return tail tuple `(loaded_ctx, not loaded_ctx.has_errors())` are
lowered to constant `0` instead of a reload from that slot.

Note also `+7957 je +8059`: when `source_trace` is false the jump lands *past*
the `xor %rdi,%rdi`, so on that path `%rdi` is whatever the previous call left
behind. Either way the receiver is never `loaded_ctx`.

## Classification

Option **(a), a genuine miscompilation** — specifically a name-resolution /
operand-lowering hole in the *implicit-return tail expression*, which silently
emits a nil constant for an in-scope local rather than reloading it or raising a
diagnostic. It is **not** stack exhaustion (the fault is a null dereference at a
fixed instruction, not a guard-page hit) and **not** a recursion depth issue.

It is, however, *also* an instance of the (c) pattern in its consequences: the
silent nil masks the real failure. The secondary defect worth fixing on its own
is that lowering an unresolved local to `0` is never correct — it should be a
hard compiler error, which would have surfaced this in a build log years earlier
instead of as a core dump in a shipped stage binary.

Sibling prior art with the same shape (receiver not marshalled / dropped for
zero-arg and `fn` instance methods):
`native_zero_arg_method_receiver_not_marshalled_2026-07-19.md`,
`native_codegen_drops_receiver_for_fn_instance_methods_2026-07-25.md`.
Both were closed against *other* call shapes; the tail-expression shape is new.

## Second, independent blocker found while verifying

Verifying any fix needs a rebuilt stage; the Rust seed cannot currently produce
one. A freshly built seed
(`cargo build --release --bin simple`, exit 0, 6m24s, from
`bbbfb9e7608`) fails to `native-build` even a hello-world:

```
$ ./cargo-target/release/simple native-build p2.spl -o p2.bin > r3.txt 2>&1
$ echo $?
1
$ grep error r3.txt
error: semantic: method `compile` not found on type `object`
       (receiver value: CompilerDriver(ctx: CompileContext(...)))
error: native-build worker exited with code 1.
```

That is `compiler_driver_run_compile` (`src/compiler/80.driver/driver.spl:143`,
body `driver.compile()`), whose parameter is declared `driver: CompilerDriver`.
The *value* is a `CompilerDriver`; its type has been erased to `object`, so the
reopened-class method `me compile()` — defined in a different module,
`driver_orchestration.spl:91`, and imported by the wildcard
`use compiler.driver.driver_orchestration.*` (`driver.spl:48`) — is not found.

This is the same disease one frame up the stack from the segfault (frames #3/#2
above), and it matches the prior narrowing lead that shrinking `--source
src/app` to `--source src/app/cli` turns the crash into a clean diagnostic:
the receiver's method table depends on which modules the worker's source
closure happened to load. Under the interpreter the erasure is reported;
under native codegen it is silently lowered to a nil receiver and crashes.

## Next steps

1. Fix the tail-expression lowering so an in-scope local is reloaded, and make
   an unresolved operand a hard error instead of a nil constant.
2. Fix the `object` erasure of a class-typed parameter when the method comes
   from a reopened class in a wildcard-imported module — this is what makes the
   defect scale/ordering dependent, and it blocks the seed's `native-build`
   outright.
3. Only then re-bootstrap and re-run the reproduction above; RC must be 0.

Do not "fix" (1) by rewriting `driver_source_pipeline_loading.spl:297-303` into
the working shape used at line 136 (`return (self.ctx, not
self.ctx.has_errors())`). That is a workaround for a general codegen hole and
would leave every other tail-expression receiver in the tree miscompiled.
