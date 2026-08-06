# Trait method with a DEFAULT BODY segfaults when invoked through a trait object

- **Id:** trait_default_body_segfaults_via_trait_object_2026-08-06
- **Status:** Root-caused, not fixed — see "Investigation notes (2026-08-06)" below for the precise blocker
- **Severity:** High
- **Found:** 2026-08-06, during WS-C task C1 (input event-type unification)
- **Engine:** Cranelift JIT (`bin/simple run`, the default engine)
- **Binary:** `bin/release/x86_64-unknown-linux-gnu/simple` (self-hosted, not the seed)

## Summary

A `trait` method that carries a **default body** crashes the process with
SIGSEGV (exit 139) when it is called through a **trait-object-typed** binding
and its body calls the trait's own `fn`-declared methods. The identical logic,
moved verbatim into a **free function** that takes the trait object as a
parameter, returns the correct value.

This is not a link error and not a diagnostic: the program prints everything
before the call and then dies. Under a spec runner it presents as the whole
file dying with no verdict, which is easy to misread as a harness timeout.

## Reproduction

Two probes, byte-identical except for where the body lives.

`probe3.spl` — default body on the trait (**SIGSEGV, exit 139**):

```
trait InputBackend:
    me poll_key() -> KeyEvent?
    me poll_mouse() -> MouseEvent?
    fn alt_held() -> bool
    fn shift_held() -> bool
    fn ctrl_held() -> bool
    fn key_to_char(key: Key) -> text?

    me poll_event() -> HostInputEvent?:
        val key_opt: KeyEvent? = self.poll_key()
        if val key_event = key_opt:
            var ch = ""
            if val Press(pressed_key) = key_event:
                if val Some(c) = self.key_to_char(pressed_key):
                    ch = c
            return host_key_event_from_ps2(
                key_event, ch,
                self.shift_held(), self.ctrl_held(), self.alt_held()
            )
        val mouse_opt: MouseEvent? = self.poll_mouse()
        if val mouse_event = mouse_opt:
            return host_pointer_event_from_ps2(mouse_event)
        nil

fn main():
    val ib: InputBackend = SI(keys: [KeyEvent.Press(Key.T)], key_idx: 0, ch: "t")
    print("ctrl=" + ib.ctrl_held().to_text())     # prints: ctrl=true alt=true
    if val Some(c) = ib.key_to_char(Key.T):
        print("char=" + c)                        # prints: char=t
    val ev = ib.poll_event()                      # <-- SIGSEGV here
    ...                                           # nothing after this prints
```

```
$ bin/simple run probe3.spl
ctrl=true alt=true
char=t
Segmentation fault (core dumped)
EXIT=139
```

Note that the individual `fn`-declared trait methods (`ctrl_held`,
`key_to_char`) dispatch **correctly** through the same `ib` binding on the
lines immediately before. Only the default-bodied method crashes.

`probe4.spl` — same body as a free function (**works, exit 0**):

```
fn probe_poll(b: InputBackend) -> HostInputEvent?:
    val key_opt: KeyEvent? = b.poll_key()
    if val key_event = key_opt:
        var ch = ""
        if val Press(pk) = key_event:
            if val Some(c) = b.key_to_char(pk):
                ch = c
        return host_key_event_from_ps2(
            key_event, ch, b.shift_held(), b.ctrl_held(), b.alt_held()
        )
    val mouse_opt: MouseEvent? = b.poll_mouse()
    if val me2 = mouse_opt:
        return host_pointer_event_from_ps2(me2)
    nil
```

```
$ bin/simple run probe4.spl
ctrl=true alt=true
char=t
KEY code=84 ch=[t] down=true mods=6
EXIT=0
```

`mods=6` is CTRL|ALT (2|4) — the correct answer.

## Scope — what is NOT broken

A narrower earlier probe (`probe2.spl`) with a default body that calls only
`me`-declared trait methods plus a free function DID work and returned the
right value through a trait object. So the defect is not "default bodies are
unimplemented". The distinguishing factor in the crashing case is that the
default body calls the trait's `fn`-declared (non-`me`) methods. That is the
next thing to bisect; it has not been isolated further.

Also unaffected: `Optional<enum>` returned through trait dispatch works
correctly (verified separately), and a fixed-array ring of enum values with
`while val ev = q.pop():` at top level works.

## Impact

Any code that reaches for a trait default body to avoid editing every `impl`
site — which is the natural migration tool for widening a trait — will compile,
lint clean, and then die at runtime. WS-C C1 hit this while adding
`poll_event()` to `trait InputBackend` and had to ship the free function
`input_backend_poll_event(backend: InputBackend)` in
`src/os/compositor/input_backend.spl` instead. That file carries a comment
pointing here so the workaround is not "tidied" back into the trait.

## Suggested next steps

1. Bisect: default body calling `me`-only methods (works) vs `fn`-only methods
   (crashes) vs a mix, to confirm the `fn`-vs-`me` axis is the trigger.
2. Check whether the interpreter agrees — the crash above is JIT
   (`bin/simple run`). If the interpreter is fine, this is another entry for
   the run-vs-test engine divergence table.
3. Until fixed, the compiler should reject a default body it cannot lower
   rather than emitting a NULL jump.

## Related

- `doc/08_tracking/bug/run_vs_test_harness_divergence_2026-07-28.md`
- `src/os/compositor/input_backend.spl` — the workaround site
- `doc/03_plan/os/simpleos/screens/ws_c_input_hal_detail.md` — C1, which
  planned the default-body approach

## Investigation notes (2026-08-06)

### Repro fixtures reconstructed

`probe3.spl`/`probe4.spl` no longer existed on disk. Reconstructed
byte-faithful equivalents (self-contained, no `os.*` import dependency) at:

- `test/fixtures/repro/compiler/trait_default_body_segfault/probe3_trait_default_body_crashes.spl`
- `test/fixtures/repro/compiler/trait_default_body_segfault/probe4_free_function_ok.spl`

### Toolchain blocker — no working self-hosted JIT binary was available today

Before this could be root-caused at the IR level, I needed a genuinely
working self-hosted (not Rust-seed) `run`-capable binary to iterate against.
None was available in this shared working copy on 2026-08-06:

- `bin/release/x86_64-unknown-linux-gnu/simple` (the path this bug names as
  "self-hosted, not the seed") currently prints the Rust-seed warning banner
  — it IS the seed, mislabeled/misdeployed. Matches the standing memory note
  "`bin/simple` symlink → stale scratch build".
- `release/x86_64-unknown-linux-gnu/simple` (the other production-candidate
  location, wrapped by `bin/release/simple`) is a genuine self-hosted
  one-binary CLI (no seed banner, real `run` subcommand) but is currently
  **globally broken** — it SIGSEGVs on `print("hello")` alone, unrelated to
  this bug. It is correctly rejected by the repo's own production gate
  (`bin/release/simple`'s `--version`/`test --help` bounded probes: "refusing
  non-production Simple runtime" / "failed its bounded test ABI probe").
  (I did get one exit-139 hit through this binary on both `probe3` and a
  trimmed-down variant with NO default body and NO self-calls at all — i.e.
  it crashes on essentially anything, so that data point is **not** valid
  evidence for this specific bug and must not be read as a confirmation.)
- Every dynload-dispatch "stageN" self-hosted binary under `build/` I could
  find (`build/bootstrap/stage2/…`, `build/bootstrap-t3-redeploy-retry-*/stage2/…`,
  `build/aggfix/stage3/simple`, `build/coverage-bootstrap-586-pinned/…`,
  `build/bootstrap-segv-fix/stage3-fixed/simple`, etc.) is built from the
  minimal `src/app/cli/bootstrap_main.spl` entry — it only implements
  `compile`/`native-build`, no `run`/JIT.
- A fresh full bootstrap (needed to produce a new one-binary CLI with `run`)
  is currently blocked repo-wide by an unrelated, pre-existing compiler
  defect: `error: in-process native-build: HIR lowering error in
  src/compiler/mir/__init__.spl: enum payload dependency \`Effect\` conflicts:
  \`compiler.hir.hir_types::Effect::struct\` vs
  \`compiler.mir.mir_effects::Effect::enum\``. Confirmed live in current
  source (`src/compiler/20.hir/hir_types.spl:912` declares `struct Effect`,
  `src/compiler/50.mir/mir_effects.spl:62` declares `enum Effect`). Two other
  concurrent sessions independently hit and abandoned this exact failure
  today (`build/bootstrap-t3-redeploy-retry-20260806-cycle2` and `-cycle3`,
  both `milestone=exit-2` during stage3 HIR). This is a separate bug and out
  of scope here, but it blocks verifying ANY fix to the present bug until
  resolved (or until a healthy binary is redeployed by another session).

### What I could verify: AOT (native-build, Cranelift backend) does NOT reproduce

Using a healthy self-hosted `bootstrap_main`-based binary's `native-build
--backend cranelift`, I compiled several variants (the faithful probe3
reconstruction, and simpler int/bool-only versions of the same shape:
default body calling only a `me` method, only a `fn` method, and a constant
body with no `self` calls) as native executables and ran them directly —
**none crashed**. This rules out a simple, universal "default-body trait
methods can never codegen correctly" defect in the shared MIR→Cranelift-IR
lowering path (the AOT `ObjectModule` path and the JIT `JITModule` path
share `codegen/common_backend.rs`), and points at something specific to the
**JIT (`JITModule`) execution path** rather than `src/compiler/50.mir` or
`70.backend`'s IR shape itself being wrong for every consumer.

### Source-level candidates identified (Rust side — `src/compiler_rust`)

The MIR→Cranelift vtable lowering that actually matters here turned out to
live in `src/compiler_rust` (the pure-Simple `src/compiler` tree calls into
this same shared native codegen for both AOT and JIT), not in
`src/compiler/50.mir`/`70.backend` as originally guessed:

1. **`src/compiler_rust/compiler/src/codegen/common_backend.rs`,
   `emit_vtable_data_objects` (~line 1814-1926, shared by AOT and JIT):** for
   each vtable slot, if the impl's `method_fns[slot]` is `None`, the slot is
   left as 8 zero bytes (a null function pointer) — code comment at line
   1852-1859 explicitly names this case as "an unoverridden default trait
   method" and says a dispatch through it "would be a separate ... bug; it
   is not this out-of-bounds defect", and line 1894 says plainly "slot stays
   zero — runtime will fault." This is the exact SIGSEGV mechanism if
   anything ever reaches this code path with `None` for a default-bodied
   method's slot.

2. **`src/compiler_rust/compiler/src/hir/lower/module_lowering/module_pass.rs`,
   `Node::Impl` handling (~line 1505-1538):** there is already a targeted
   mitigation here — for every trait method with a default body that a
   concrete `impl` does *not* override, the compiler lowers a **fresh
   per-impl copy** of the default body (tagged with the concrete struct as
   `self`'s static type via `lower_function(&default_method, Some(type_name))`)
   and registers it into that impl's `methods_map` under
   `"{type_name}.{method_name}"`, specifically so slot (1) above is never
   `None` for this case. The comment there cites exactly this class of bug
   ("vtable slot reads out-of-bounds memory as a function pointer (crash)
   instead of dispatching to the default body").
3. **Vtable slot numbering** (`type_registration.rs::register_trait`, which
   assigns `vtable_slot` in trait-method declaration order via
   `trait_info.add_method`) iterates the same `t.methods`/`trait_def.methods`
   AST list, in the same order, as the per-impl default-body synthesis in
   (2) — I did not find an ordering/indexing mismatch between the two on
   inspection.

Given (2) already exists and looks structurally correct for the exact
"unoverridden default method, dispatched via trait object" case this bug
describes, the remaining defect is most likely narrower than "the vtable
slot is never filled" — e.g. specifically how `self.<fn-method>()` calls
**made from inside the freshly-lowered-per-impl default body** resolve
(static direct call vs. a second, possibly circular/misnumbered vtable
dispatch), which would explain the bug's own bisection result (default body
calling only `me` methods was fine; calling `fn` methods crashed). Pinning
that down requires live tracing (`SIMPLE_DEBUG_METHOD_DISPATCH=1` against
`mir/lower/lowering_expr_method.rs`'s `DispatchMode::Dynamic` branch, around
`find_trait_for_method_on_receiver`) against a real crash, which needs the
working JIT binary described above as unavailable today.

### Why I stopped here

This satisfies the "stop and document precise findings" condition: the
remaining work is Rust-side JIT/vtable-dispatch surgery in unfamiliar
territory, and cannot be safely iterated on or verified without a working
self-hosted `run`-capable binary, which does not currently exist in this
working copy for reasons independent of this bug (see toolchain blocker
above). I did not apply or land a speculative fix without the ability to
verify it crashes before and passes after, per the sabotage-check
requirement.

### Next steps for whoever picks this up

1. Get (or wait for) a healthy self-hosted, `run`-capable `bin/simple`
   (either resolve the unrelated `Effect` struct/enum symbol collision
   blocking full bootstrap, or obtain a clean redeploy from another
   session).
2. Confirm the two fixture files above still reproduce (`probe3_*` crashes,
   `probe4_*` exits 0) under `bin/simple run` before touching any code —
   this environment's binaries were unreliable enough that re-confirming
   first is essential.
3. Run with `SIMPLE_DEBUG_METHOD_DISPATCH=1` and compare the dispatch
   decisions for `self.key_to_char(...)` / `self.shift_held()` etc. inside
   the freshly-lowered default body between the crashing and non-crashing
   cases, focused on `mir/lower/lowering_expr_method.rs` around line
   1876-1931 and `find_trait_for_method_on_receiver`.
4. If a genuine vtable-slot mismatch or wrong dispatch mode is found there,
   fix it minimally in `src/compiler_rust`, add the regression system spec
   (shell to `find_simple_binary()` with `["run", <fixture path>]` via
   `rt_process_run`, following the pattern in
   `test/system/compiler/native_backend_e2e_system_spec.spl`), confirm it
   fails on the pre-fix binary and passes on the post-fix binary, then
   sabotage-check by reverting and confirming the crash returns.
