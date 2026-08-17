# ByteSpan.starts_with dropped from the SimpleOS kernel closure and silently replaced by a nil-returning WEAK stub

Status: **RETIRED 2026-08-17 — fixed in current source.** Both defects (D1
cache key, D2 fabrication fail-open) are present as landed code in the tree
today; what remained on 07-28 was a *deployment* gap in a stale
`bin/release/**` binary, and CLAUDE.md forbids this lane from redeploying it.
See "Re-triage 2026-08-17" below.
Status re-verified 2026-08-17 by source inspection (triage shard 00).
  (That stamp said OPEN; content grep says otherwise — see the re-triage.)

## Re-triage 2026-08-17 (content grep of CURRENT source, not SHA ancestry)

Classified by CONTENT. Each of the four claimed fixes was re-grepped; all four
are present:

| claimed fix | proving symbol / evidence in current source |
|---|---|
| D2 pure-Simple guard, channel 3 | `simpleos_undefined_simple_module_symbols` — 2 occurrences in `src/compiler/70.backend/backend/llvm_native_link.spl` |
| D2 shrink-only ratchet | `config/simpleos_fabricated_lib_baseline.sdn` exists (1873 bytes) |
| D2 seed-side backstop | `stale_module_move_report` (`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs:392`), called at line **561** — i.e. before the `FreestandingUnresolvedMode` match, as designed; `simple_module_symbol_tail` at line 374 excludes `rt_*` by construction (asserted at line 1367) |
| D1 root: `GlobalBuildFingerprint` ungated | `src/compiler_rust/compiler/src/pipeline/native_project/mod.rs:910-913` carries the explicit comment "This is deliberately NOT gated on `incr_hardening`. The dependency-blind [key] ... `incr_hardening` now only controls the ..."; the remaining `if incr_hardening` at line 1120 gates something else |

Unit coverage for D2's backstop is in-tree at `stubs.rs:1353-1372`
(`stale_module_move_is_detected_and_rt_channels_are_untouched`), including the
negative controls: an `rt_*` symbol must NOT be reported (1367-1368) and a live
symbol must NOT be reported (1372).

Binary identity caveat, stated rather than hidden: this triage did **not** and
could not rebuild the SimpleOS WM kernel — `bin/simple` here is the stale Rust
seed (mtime 2026-08-16 22:59) and ~15 lanes share the checkout, so a redeploy
is prohibited. The row is retired on the strength of the source containing the
fixes plus in-tree unit coverage with negative controls, **not** on a fresh ELF.
If a future SimpleOS WM ELF again shows an 8-byte WEAK `lib__*` / `os__*`
`FUNC`, that is a NEW regression against a guard that now exists — file it
fresh rather than reopening this row.

- **Filed:** 2026-07-28
- **Severity:** high (silent wrong answer, no diagnostic, in the WM render path)
- **Component:** native-build entry-closure / per-function emission + seed freestanding stub fail-open
- **Artifact:** `build/simpleos_wm_fullscreen_evidence/simpleos_wm_production_desktop.elf`

## Symptom (PROVEN)

In the SimpleOS WM production desktop kernel ELF:

```
08023e4f T lib__common__bytes__span__ByteSpan_dot_get
08023e1a T lib__common__bytes__span__ByteSpan_dot_len
08023fa0 T lib__common__bytes__span__ByteSpan_dot_slice
08844960 W lib__common__bytes__span__ByteSpan_dot_starts_with
```

`ByteSpan_dot_starts_with` is an 8-byte WEAK body — `push rbp; mov rsp,rbp;
xor eax,eax; pop rbp; ret` — i.e. it unconditionally returns nil/false.
`ByteSpan_dot_equals`, which `starts_with` calls, is not present in the ELF at
all.

Three sibling methods from the SAME module (`src/lib/common/bytes/span.spl`)
ARE present as real `T` definitions, so the module was compiled — only
`starts_with` and `equals` were dropped from its object.

## It is reached (PROVEN)

21 references, all `movabs $0x8844960,%reg` (there is no relative
`call <symbol>` form, so a naive `grep 'call.*starts_with'` reports a false
"never called"). Enclosing functions:

| refs | caller |
|------|--------|
| 7 | `lib__gc_async_mut__gpu__browser_engine__style_block_parse__sb_background_shorthand_color_value` |
| 4 | `lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer_style___bg_layer_is_direction` |
| 4 | `lib__gc_async_mut__gpu__browser_engine__dom_color__parse_color_value` |
| 3 | `os__tools__pkg__pkg_repository__load_repositories` |
| 2 | `lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer_declarations__apply_decls` |
| 1 | `lib__nogc_sync_mut__ui__theme_package___wm_window_gradient_from_css` |

Every CSS colour / background-gradient decision on the desktop path therefore
takes the "prefix does not match" branch unconditionally.

Disassembly note: the kernel ELF header says `ELF32 / Intel 80386` but the code
is x86-64. `objdump -d` MUST be given `-m i386:x86-64`; without it the REX
prefixes decode as `dec %esp` and the output is plausible-looking garbage.

## The source is fine (PROVEN)

Compiled on its own the same source emits real bodies for both:

```
bin/simple native-build --emit-archive --target x86_64-unknown-none \
  --source src/lib/common/bytes --entry src/lib/common/bytes/span.spl -o span.a
nm span.a | grep ByteSpan_dot
  ... T span__ByteSpan_dot_equals
  ... T span__ByteSpan_dot_starts_with
```

So this is not a source bug and not a "chained method on an erased receiver"
limitation — it is a kernel-build closure/emission miss.

## Why nothing failed the build (root cause of the silence)

`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` fabricates a
weak nil-returning definition for **any** symbol left undefined in the link
set. Its filters exclude system, dyld, C++, compiler-rt and linker-provided
names, but nothing excludes pure-Simple `lib__*` / `os__*` symbols.

The freestanding fabrication guard that would otherwise catch this —
`simpleos_check_no_fabricated_rt_stubs` in
`src/compiler/70.backend/backend/llvm_native_link.spl` (approx. lines
2266-2433) — is scoped to `rt_*` externs only. A fabricated pure-Simple method
body is outside its remit, so the link succeeds and the guest silently gets
`false` from 21 call sites.

`ByteSpan_dot_starts_with` is the only `lib__` weak symbol in this ELF, so the
blast radius today is exactly this one method — but the fail-open is general.

## Hypotheses already refuted

- **Not an entry-closure file-level miss.** Rebuilding the same module with
  `--emit-archive --entry-closure --target x86_64-unknown-none` still emits
  real `T` bodies for both `starts_with` and `equals`. The drop needs the full
  kernel context to reproduce.
- **Not the second `ByteSpan`.** `src/lib/nogc_sync_mut/db/accel.spl:31`
  declares a same-named `ByteSpan`, but no `db__accel` symbol appears anywhere
  in this ELF, so a global struct-registry collision with that module is not
  the mechanism here.

## Suggested fixes

1. **Root:** find why the kernel entry-closure records the 21 calls to
   `starts_with` yet never schedules its body (and consequently never
   discovers `equals`). Bare-method-name collision is the leading suspect:
   `starts_with` also exists as `rt_string_starts_with`,
   `Path_dot_starts_with`, `_text_starts_with_slash` and
   `_bytes_starts_with` in this same ELF.
2. **Guard (defence in depth):** extend the fabrication refusal so that a
   `lib__*` / `os__*` symbol resolving to a fabricated weak nil body fails the
   freestanding link, exactly as a novel fabricated `rt_*` extern already does.
   A pure-Simple method must never be papered over by a stub.

## ROOT CAUSE — PROVEN 2026-07-28 (stale object-cache reuse across a module move)

The mechanism is not closure discovery and not name resolution. It is the
native-build **object cache** keeping an object compiled against a mangled name
that no longer exists, combined with the fabrication fail-open.

Evidence chain for the currently-live instance (the ByteSpan pair is already
real `T` in the 2026-07-28 10:40 kernel; this is the same defect, next symbol):

1. `readelf -sW` on `simpleos_wm_production_desktop.elf`: exactly ONE 8-byte
   WEAK `FUNC` with a `lib__`/`os__` prefix —
   `lib__gc_async_mut__gpu__browser_engine__simple_web_html_layout_renderer_layout__skip_wrap_spaces`
   at `0x08863010`, body `push rbp; mov rsp,rbp; xor eax,eax; pop rbp; ret`.
2. The real body IS in the same ELF, under a different module prefix:
   `..._foundation__skip_wrap_spaces` at `0x08126080` (`T`).
3. Reached: 3 `movabs $0x8863010,%reg` sites, all inside
   `..._style__parse_font_shorthand_family` — text wrapping and the CSS font
   shorthand path.
4. `skip_wrap_spaces` is defined exactly once in the tree, in
   `..._foundation.spl:302`. It was MOVED there by `365a643236b` (07-28 04:46);
   `..._layout.spl:241-246` carries the comment recording the move.
5. A fresh compile resolves correctly. With `--emit-archive --entry-closure
   --target x86_64-unknown-none` and `SIMPLE_LIB=src`, the style module emits
   `parse_font_shorthand_family` referencing
   `lib__..._foundation__skip_wrap_spaces`, and no `_layout__` name exists.
   `SIMPLE_DEBUG_IMPORT_SYMBOL=skip_wrap_spaces` prints exactly one candidate:
   the foundation one.
6. The linked object is stale. In the gate's cache dir
   (`build/simpleos_wm_fullscreen_evidence/native-cache/x86_64-unknown-none-elf/objects`)
   the only object defining `..._style__parse_font_shorthand_family` was
   `7446a1d1cef9e76e.o`, mtime 2026-07-26 23:47 — **before** the 07-28 04:46
   move — and it carries `U ..._layout__skip_wrap_spaces`. The 07-28 10:38
   build wrote 8 new objects and reused 679; none of the 8 contains any
   style/`skip_wrap_spaces` symbol. Seven cached objects in total still
   referenced the dead name and have been purged.

So: module A's function moves to module B; unchanged caller module C keeps its
cached object, which still references `A__f`; `A__f` no longer exists; the stub
generator fabricates a weak nil `A__f`; the link succeeds; every call site in C
silently gets `false`/`0`.

### Two separate defects

- **D1 (cache): ISOLATED AND PROVEN 2026-07-28.** The gap is not a missing field
  in `cross_module_layout_fingerprint` — the digest is correct and does change on
  a module move. The gap is that the DEPLOYED binary still gates the entire
  `GlobalBuildFingerprint` (layout digest, target, opt-level, linker script)
  behind `incr_hardening`, which is OFF by default. `35dbbf8ce85` (07-28 00:12)
  ungates it in source; the deployed
  `bin/release/x86_64-unknown-linux-gnu/simple` (07-28 05:45) predates that
  behaviour and therefore still uses the dependency-blind content-only key. So
  the key fix is landed but INERT until a bootstrap redeploy — the same
  deployment gap as the pure-Simple guard channels.

  Minimal reproduction (4 modules, freestanding archive, ~10 s/build):
  `caller.spl` bare-calls `helper_moved`, resolved through the closure import
  map; move `helper_moved` from `prov_a.spl` to `prov_b.spl` leaving
  `caller.spl` byte-identical (`md5sum -c` OK), then rebuild against the same
  `--cache-dir`.

  - default (deployed behaviour): caller's object is REUSED; the emitted archive
    carries `UND prov_a__helper_moved` (dead) alongside `FUNC prov_b__helper_moved`
    (real) — exactly the `skip_wrap_spaces` shape.
  - `SIMPLE_NATIVE_INCREMENTAL=1` (source behaviour after `35dbbf8ce85`):
    `[native-incremental] 0 reused / 4 rebuilt (full rebuild: cross-module type
    layout / signatures changed)` and the archive references only
    `prov_b__helper_moved`.

  The same lever also proves a pure ARITY change in an unrelated function fails
  to invalidate dependents under the deployed binary. Until the redeploy lands, a
  module move or signature change must be followed by a cache purge, or the build
  must set `SIMPLE_NATIVE_INCREMENTAL=1`.

  Hit-rate impact of the unconditional key (measured on the reproduction):
  warm no-op 3/4 reused; body-only edit 2/4 reused (only the edited module plus
  the always-rebuilt entry); signature / module-membership change full rebuild.
  Body edits — the common case — keep hitting; only structural changes pay the
  full-closure cost.
- **D2 (fail-open):** nothing failed the link. FIXED here by channel 3 of
  `simpleos_check_no_fabricated_rt_stubs`.

### Guard landed

`src/compiler/70.backend/backend/llvm_native_link.spl` gains
`simpleos_undefined_simple_module_symbols` + channel 3: any `lib__*` / `os__*`
name the closure references and nothing defines refuses the freestanding link.
Staged ratchet via `config/simpleos_fabricated_lib_baseline.sdn` (shrink-only,
separate from the `rt_*` baseline, currently EMPTY — the one known instance is
being fixed, not baselined). The `rt_*` channels are untouched.

### Caveat — the guard is not live yet

The deployed `bin/release/x86_64-unknown-linux-gnu/simple` (2026-07-28 05:45)
contains neither `SimpleOS freestanding link refused` nor
`simpleos_fabricated_rt_baseline` (`strings` count 0 for both), but does contain
the Rust `Freestanding unresolved symbol check`. The pure-Simple guard —
including the `rt_*` channels landed on 07-28 — therefore does NOT run in the
SimpleOS WM gate today. It becomes effective only after a bootstrap redeploy of
the self-hosted binary. Until then the equivalent refusal would have to live in
`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs`.

### Seed-side backstop landed (runs today, once the seed is rebuilt)

`generate_stub_object_freestanding` in
`src/compiler_rust/compiler/src/pipeline/native_project/stubs.rs` now runs
`stale_module_move_report` on the about-to-be-stubbed set, BEFORE the
`FreestandingUnresolvedMode` match so `DeferToLinker` / `EmitStubs` cannot
swallow it. Any undefined `lib__*` / `os__*` symbol whose bare function name (the
segment after the LAST `__`) is DEFINED in the same link under a different module
prefix aborts the link and names both the dead symbol and the module it moved to.
This is the seed complement to channel 3 — it lives in the binary the SimpleOS
gate actually executes, and it is the backstop for D1 in case a future cache-key
change regresses. `rt_*` symbols are excluded by construction
(`simple_module_symbol_tail` returns `None` for them), so the `rt_*` channels are
untouched. Unit test:
`stubs::tests::stale_module_move_is_detected_and_rt_channels_are_untouched`.
