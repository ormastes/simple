# native-build discovers ZERO sources (`source_closure 0/0`), and the `object` receiver-erasure hypothesis is refuted

- **Filed:** 2026-08-17
- **Status:** OPEN — primary failure not yet fixed. Two hypotheses refuted here.

## Binary identity for every measurement below

`bin/simple` -> `bin/release/x86_64-unknown-linux-gnu/simple`,
size **59537240**, mtime **2026-08-17 12:58:51 UTC**,
md5 `78ffcbcd3f4cfaa11e3d9c1db37bf0b2`. Self-reported as the Rust bootstrap seed.

Note this is **not** the binary a same-day lane note described (size 59617400,
mtime 12:54:48). A *later* redeploy replaced it. Any measurement attributed to
59617400 was taken against a binary that no longer exists at that path.

## REFUTED #1 — the receiver is not type-erased

The error that motivated this investigation:

```
error: semantic: method `compile` not found on type `object` (receiver value: CompilerDriver(...))
```

The `on type \`object\`` half was suspected to be a type-erasure defect — a
`CompilerDriver` receiver whose static type had been lost. **It is not.**

- The message is produced by the **Rust seed interpreter**, at
  `src/compiler_rust/compiler/src/interpreter_method/mod.rs:1654` (and the
  sibling arm at 1665, and the macro at `interpreter/error_macros.rs:82`). It
  interpolates `recv_val.type_name()`.
- `Value::type_name()` (`src/compiler_rust/runtime/src/value/core.rs:560-605`) is
  a **coarse heap-tag** mapping: `Some(HeapObjectType::Object) => "object"` at
  line 582. **Every** class instance reports `"object"` — there is no branch that
  returns a class name.

So `on type \`object\`` is the normal, expected rendering for any class instance
in this diagnostic. It carries **zero** information about erasure. The class
identity is in fact intact, which the same message proves in its own
`(receiver value: CompilerDriver(...))` suffix.

**Consequence for anyone reading that error:** it means "method lookup failed on
a correctly-identified class instance", not "the receiver's type was erased".
The diagnostic is misleading by construction and should print the class name.

## REFUTED #2 — `compile` is not a missing method

`me compile()` **is** defined, at `src/compiler/80.driver/driver_orchestration.spl:91`,
and its file **is** glob-imported by `src/compiler/80.driver/driver.spl:47`
(`use compiler.driver.driver_orchestration.*`) — precisely the pattern that
`driver.spl:41-45` documents as necessary to register `impl CompilerDriver:`
methods. Called from `driver.spl:59`, `driver.spl:143`,
`src/app/compile/test_check_mode.spl:19`.

(A `grep` for `fn compile` finds nothing on `CompilerDriver` and is a trap:
instance methods here are declared `me compile()`, not `fn compile()`.)

## The failure that actually reproduces now is different

`method \`compile\` not found` did **not** reproduce at all. Measured:

```
env -u SIMPLE_BOOTSTRAP SIMPLE_NO_STUB_FALLBACK=1 \
  <seed> native-build --source test/fixtures --entry-closure \
  --entry native_trailing_default_param.main --cache-dir <d> --output <o>
```

rc=**1** (read from a variable on the line after the command, not through a pipe).
Log shows:

```
[build] source_closure 0/0 step 0/6 pending
[build] source_closure 0/0 step 1/6 complete
[ERROR] phase 2 FAILED
[build] parse unknown/0 step 1/6 failed
error: native entry source not found: native_trailing_default_param.main
```

**`source_closure 0/0` — zero sources discovered.** The entry is then reported
missing because nothing was ever loaded. This is upstream of any method
resolution, which is why the `compile` error is no longer reached.

Controls:

| arm | result |
|---|---|
| original fixture `native_trailing_default_param.main`, from main worktree | rc=1, `source_closure 0/0` |
| original fixture, from a fresh isolated `git worktree` | rc=1, `source_closure 0/0` |
| a reduced 2-file fixture (`class Widget` + `me bump` + one `use`) | rc=1, `source_closure 0/0` |

The reduced fixture fails **identically to the original**, and the original fails
identically in two different worktrees. So this is not a fixture defect and not a
worktree artifact — source discovery itself yields nothing.

**This means the sibling row's shape can no longer be exercised at all.** The
defect recorded in
`native_build_entry_module_loses_own_class_methods_multimodule_2026-08-17.md`
(`unresolved method call: bump`, a MIR-lowering failure) is *masked* by this one:
lowering is never reached. That row's diagnosis is not contradicted here — it is
simply no longer reproducible until source discovery is fixed. Do not read its
absence from current logs as evidence it was fixed.

## A reporting defect fixed alongside this

The `TMPDIR` parse error that also appeared in these logs was a genuine but
*separate* defect on native-build's stderr-truncation path, and it was being
emitted **instead of** the real diagnostic. Fixed at the call site; the
underlying grammar defect is filed at
`doc/08_tracking/bug/fstring_nested_quoted_literal_in_interpolation_misparsed_2026-08-17.md`.

## Next step for whoever picks this up

Find why the source-closure walk returns 0 for `--source test/fixtures
--entry-closure`. Start at the `source_closure` / `load_sources` step emitters in
`src/compiler/80.driver/driver_source_pipeline_loading.spl` and the
`--entry-closure` argument handling in `src/app/cli/native_build_main.spl`. A
walk that finds nothing and reports `0/0` without erroring on its own emptiness is
also a fail-open worth closing on its own.
