# Linux native link passed an unconditional `-lSDL2`, failing every host without SDL2

- **Filed:** 2026-09-06
- **Severity:** blocker (release critical path — second blocker behind the capsule-receipt defect)
- **Status:** Linux arms FIXED; macOS and FreeBSD arms untouched and still suspect
- **Host:** aarch64-unknown-linux-gnu (no `libSDL2*.so*` anywhere on the filesystem)

## Symptom

With the capsule-receipt defect fixed
(`std_file_system_write_mocks_return_true_without_writing_2026-09-06.md`),
`native-build` reached the link step and failed there instead:

```
[build] native_compile 1/1 step 5/6 complete
[build] link 1/1 step 5/6 ...
error: LLVM native linking failed: Linking failed: cc linking failed:
       ld.lld: error: unable to find library -lSDL2
collect2: error: ld returned 1 exit status
```

Reproduced identically on the plain reproducer (default bundle, llvm backend)
and on `scripts/check/check-stage2-hello-world-native-build.shs`'s entry-form
arm (`--backend cranelift --runtime-bundle core-c-bootstrap --entry-closure
--mode one-binary`), i.e. it is not bundle- or backend-specific.

## Root cause

`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl` pushed
`-lSDL2` unconditionally on both Linux link paths:

- the direct-lld arm (`if os == "linux"`), and
- the cc-fallback arm, guarded only by `if not hosted_cross` — which does not
  help, because the failure is on the **native host** lane.

Nothing needs SDL2 at link time. `src/runtime/runtime_sdl2.c:11` states
"SDL2 is loaded DYNAMICALLY at first use (dlopen/dlsym,
LoadLibrary/GetProcAddress)", and every entry point is bound through
`SDL2_BIND_REQUIRED` -> `dlopen` (`:173`, `:263`, `:296+`). Measured:

```
nm -u .../libsimple_runtime.a | grep -c ' SDL_'   ->  0
```

Zero undefined `SDL_*` symbols, so `-lSDL2` contributes nothing and can only
fail.

`--as-needed` / `-Wl,--as-needed` does **not** rescue this. It only controls
whether the library is recorded in `DT_NEEDED`; the linker must still *find*
`libSDL2.so` to process the `-l` flag at all.

The repo had already reached exactly this conclusion elsewhere and simply never
applied it to Linux:

- `native_linking.spl:838-848` (Windows list): "SDL2.lib is deliberately ABSENT.
  src/runtime/runtime_sdl2.c binds every SDL symbol dynamically ... an
  unconditional SDL2.lib is a guaranteed LNK1181 on any host without SDL2
  installed."
- `src/compiler/70.backend/backend/runtime_compiler.spl:483-485`: runtime_sdl2
  "needs no SDL2 headers to compile and **no -lSDL2 to link**, so hosts without
  SDL2 still build."

The Linux arms contradicted the contract their own runtime declares.

## Fix applied

Removed `-lSDL2` from both Linux arms of
`src/compiler/70.backend/linker/_LinkerWrapper/native_linking.spl`, each with a
comment recording the dlopen contract, the `nm -u` measurement, and why
`--as-needed` is not a defence. A program that genuinely wants SDL2 linked
statically still gets it through `config.libraries`.

## Still open

- **macOS and FreeBSD arms still push `-lSDL2` unconditionally** (three further
  sites in the same file, plus the macOS cc-fallback list). The same dlopen
  argument applies verbatim, and the macOS sites are already carrying `-L`
  workarounds for exactly this failure (see
  `doc/08_tracking/bug/native_build_llvm_lane_4layer_stack_2026-07-26.md`
  item 3, which treated it as an env problem to be worked around rather than a
  stale link flag to be deleted). They were left alone here only because
  neither platform can be tested on this host — that is a limitation, not a
  judgement that they are correct.
- `src/compiler/70.backend/linker/_LinkerWrapper/shared_linking.spl` also names
  SDL2; not inspected, not touched.
- **No gate covers this.** A link-flag list that names a third-party SDK the
  runtime resolves at runtime is invisible to every existing check on a host
  that happens to have the SDK installed. The failure only appears on a clean
  host, which is where releases are built.
