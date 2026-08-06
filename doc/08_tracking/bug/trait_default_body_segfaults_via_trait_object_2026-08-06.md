# Trait method with a DEFAULT BODY segfaults when invoked through a trait object

- **Id:** trait_default_body_segfaults_via_trait_object_2026-08-06
- **Status:** Open
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
