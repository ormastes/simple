# Native dynload build drops static initializers on module-level `var` globals

## Status
Source implemented for scalar initialization, load, and store. Strict
LLVM/Cranelift initialization and mutation execution remains pending; retain
the source workaround until that proof passes.

## Resolution (2026-07-15)

The pure-Simple Cranelift dynload adapter now declares writable scalar globals,
applies their initial values, and routes global loads/stores through the shared
SFFI bridge. The focused initialization/mutation regression was added but not
executed in this source-only audit.

## Severity
High — any zero/constant-initialized module-level mutable global comes up holding
uninitialized memory on the SimpleOS native `--mode dynload` path, silently
corrupting program state. Symptom is data corruption, not a crash, so it is easy
to miss.

## Summary
On the native-build path used by the x86_64 SimpleOS lane

```
bin/simple native-build --backend cranelift --cpu x86-64-v1 --opt-level=aggressive \
  --mode dynload --entry-closure --entry <entry>.spl \
  --target x86_64-unknown-none -o kernel.elf --linker-script linker.ld
```

the static initializer on a module-level `var` global is **not applied at load
time**. The global comes up holding whatever bytes occupy its slot (observed:
fragments of `.text`), so the first read returns garbage rather than the
declared value. Runtime stores to the same global *do* land — a subsequent
`g = g + 1` advances the (garbage) value correctly — which proves the address
resolution and load/store paths are fine; only the one-time static init is lost.

## Evidence
Repro: `scripts/check/check-simpleos-x86-64-wm-render-event-evidence.shs`
(examples/09_embedded/simple_os/arch/x86_64/wm_entry.spl).

Counters declared `var g_evt_key: u64 = 0` (and four siblings) print machine-code
garbage that then increments by one per event:

```
[wm-event] type=key   detail=scancode=15 count=-4369124742942603178   # = B
[wm-event] type=key   detail=scancode=50 count=-4369124742942603177   # = B+1
[wm-event] type=key   detail=scancode=9  count=-4369124742942603174   # = B+4
...
```

`B = -4369124742942603178` decodes to little-endian bytes
`56 48 89 e5 31 c0 5d c3` — x86-64 instruction bytes
(`push rsi; mov rbp,rsp; xor eax,eax; pop rbp; ret`), i.e. the counter's `.bss`
slot was never zeroed and reads leftover code bytes. The strictly-increasing
`B, B+1, B+4 …` progression confirms increments (runtime stores) work; only the
`= 0` static init was dropped.

The nonzero-initialized `g_mouse_initialized: u64 = 0` starting from garbage also
breaks the PS/2 mouse init gate (`if g_mouse_initialized == 1`), so no
`type=mouse_move` / `type=mouse_button` markers are emitted at all.

## Workaround (applied)
Re-seed the affected globals at runtime at the top of the entry function
(`fn spl_start()` in `wm_entry.spl`): explicit `g_evt_key = 0`, `g_mouse_x = 512`,
etc. Runtime stores land, so the marshaled values are then correct.

## Second facet: module-global reads arrive boxed in some contexts
Same build path, confirmed by QMP guest-memory dump (`pmemsave` of the
`wm_entry__g_*` slots) vs observed behavior:

- `if g_flag == 1:` is FALSE even when memory holds 1 (`g_minimize_active=1`,
  `g_mouse_initialized=1` verified in-guest), while `== 0` / `!= 0` compare
  correctly — a boxed/tagged read makes nonzero-literal equality fail (0 still
  boxes to 0). This silently dead-coded the whole PS/2 mouse poll and the
  minimize-animation tick (main loop kept spinning; RIP sampling showed it
  idling in the i8042 status poll).
- String interpolation of a global (`{g_evt_key}`, `{g_mouse_x}`) prints
  `<object>` or nil; `g & 1` from a re-read global also stayed boxed
  (`left=<object>`), while `g + 1` unboxed. `g & 0xFFFF` produced a stable
  garbage number (18516) rather than the coordinate — reads may unbox, keep
  the box, or mask box bits depending on the operator/context.

Source workarounds applied in wm_entry.spl: flag gates use `!= 0` /
difference-vs-zero, counters are hoisted through `+` arithmetic into typed
locals, `left_pressed` derives from the local packet byte. Residual known-wrong
values: mouse marker x/y still print the masked box value (18516), not real
coordinates — needs the compiler fix.

## Next Step
Fix the native `--mode dynload` code generator / loader to emit and apply the
static initializer for module-level `var` globals (or emit them into a
zero-filled/`.data` section the loader honors). Until then, entries on this path
must runtime-initialize any mutable module global they depend on. Likely related
to the previously noted "seed segfault on uninit module var" and "zero-store
array inits" observations.
