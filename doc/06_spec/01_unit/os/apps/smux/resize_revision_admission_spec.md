# Resize content revision admission

Source-authored manual, not generator-qualified. **NOT_RUN: eight authored cases, zero executed.** REQ-CMUX-004/005.

The explicit-state scenarios verify that unchanged viewport projection preserves an exhausted identity, changed projection refuses before retained-grid resize, the native transaction admission returns its original state without uncertainty, and direct pane planning propagates the refusal.

These controls use no real native handles. They cannot prove OS resize ordering, multi-participant compensation, process cleanup or screen behavior. Those require the real provider suite. Generated-manual review and SSpec maintenance remain pending with the admitted compiler.

Additional controls cover the final available identity followed by refusal, and a writable first participant followed by an exhausted second participant. The latter checks returned state preservation; it does not observe OS calls.

Presentation coverage rejects a border change that would shrink exhausted child content. Checkpoint coverage rejects restoration after a split participant exhausts its identity, preserving the added pane and current dimensions for later cleanup. Both remain explicit-state controls, not native terminal evidence.
