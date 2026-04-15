# Hosted WM / Cocoa Runtime — Session Findings 2026-04-15

Catalogue of every defect, dead code path, and runtime crash uncovered while
trying to open the Obsidian-themed window manager on a macOS host. Some are
already fixed (commits called out below), the rest are filed for follow-up.

| # | Area                            | Status      | Severity |
|---|---------------------------------|-------------|----------|
| 1 | Vendor tree corruption          | Workaround  | High     |
| 2 | Parser: named-field match arm   | Fixed       | Medium   |
| 3 | `bin/simple <file.spl>` dispatch fallthrough | Open | High     |
| 4 | `bin/simple_mac` silent exit    | Open        | Low      |
| 5 | `text_arg_indices` missing entries | Fixed    | Medium   |
| 6 | `strip_llvm_constructors` kills ObjC | Fixed | High     |
| 7 | `cocoa.rs` API drift vs objc2-app-kit 0.2.2 | Fixed | High |
| 8 | Hosted runtime stubs in deployed `libsimple_native_all.a` | Open | High |
| 9 | NSApplication sharedApplication crashes from Simple-built binary | Open | High |
| 10 | Rust seed lacks `gui` feature by default | Open  | Medium   |
| 11 | `simple_stage3` is x86-64 ELF on arm64 macOS | Open | Low |
| 12 | `cocoa.rs` cosmetic warnings   | Open        | Trivial  |

---

## 1. Vendor tree corruption

**Where:** `src/compiler_rust/vendor/`

`cargo build --profile bootstrap -p simple-driver` fails immediately with:
```
error: no matching package found
searched package name: `log`
```

Investigation showed multiple vendored crates were missing files:
- `log` crate not vendored at all
- `thiserror/build/probe.rs` missing (referenced by checksum)
- `object-0.36.7/src/build/error.rs` missing
- `ab_glyph` missing (transitive via `sctk-adwaita` → `winit`)

`.cargo-checksum.json` listed dead entries (`target/coverage/*.profraw`) from
a previous CI build that no longer exist on disk, so cargo refuses to use the
vendored copy.

**Workaround** (this session, uncommitted):
```bash
cd src/compiler_rust && cp .cargo/config.toml /tmp/cfg.bak
echo '[build]\njobs = 8' > .cargo/config.toml
cargo vendor /tmp/vendor_fresh
cp /tmp/cfg.bak .cargo/config.toml
mv vendor vendor.broken
mv /tmp/vendor_fresh vendor
```

**Proper fix:** check the freshly populated vendor in once it is reviewed.
The diff vs. the old vendor is mostly metadata (`.cargo-checksum.json`
regeneration, `.gitignore` removal, `.cargo-ok` removal) — only ~119 file
changes outside metadata. No source changes inside vendored crates.

---

## 2. Parser rejects named-field match-arm destructuring

**Where:** Self-hosted Simple parser (currently in `bin/simple` and
`src/compiler/...`).

**Symptom:**
```
Build failed: failed to parse src/lib/common/ui/session.spl during discovery:
Unexpected token: expected Comma, found Colon
```

**Repro:**
```
match event:
    UIEvent.KeyPress(key: key):   # rejected — colon in pattern
        ...
```

Positional bindings work:
```
    UIEvent.KeyPress(key):        # OK
```

Named-args inside a *constructor expression* (`UISession(state: ..., ...)`)
parse fine; the bug is specific to match-arm patterns.

**Status:** Worked around in commit `451aea67` (session.spl + access.spl
rewritten to positional patterns). The underlying parser still rejects the
named form — a full fix would land a `parse_match_pattern` extension that
accepts `Variant(field: binding)`.

---

## 3. `bin/simple <file.spl>` always errors out

**Where:** `src/app/io/cli_commands.spl:64-101` (`cli_run_file`)

**Symptom:** Every `.spl` file produces:
```
[STDERR] Error running <path>
```
with exit `1`. The file's own `print` statements never fire, so the failure
is not in user code.

**Diagnosis:** `cli_run_file` matches on `CompileResult` from
`interpret_file()`. The match has explicit cases for `Success`, `ParseError`,
`TypeError`, `BlockError`, `ResolveError`, `BorrowError`, `CodegenError`,
`RuntimeError` — every variant of the enum (`driver_core_types.spl:145`).
The `case _:` fallthrough should never fire, yet it always does. Most likely
the embedded interpreter (`CompilerDriver.run_compile`) returns a value that
doesn't deserialize as a `CompileResult` enum at the self-hosted runtime
boundary — or `interpret_file()` traps and the panic produces a sentinel value.

**Reproducer:**
```
echo 'fn main() -> i64: print "hi"; return 0' > /tmp/h.spl
bin/simple /tmp/h.spl    # → "Error running /tmp/h.spl", exit 1
```

The Rust seed at `src/compiler_rust/target/bootstrap/simple` runs the same
file fine — only the self-hosted `bin/simple` is broken.

**Severity:** High — the entire interpreter UX is unusable from the deployed
binary.

---

## 4. `bin/simple_mac` exits silently

**Where:** `bin/simple_mac` (Mach-O 64-bit arm64, dated 2026-03-21)

`./bin/simple_mac /tmp/hello.spl` produces no stdout, no stderr, exits `0` (or
silently closes). Probably an older self-hosted build with the same dispatch
break as #3 but failing earlier. Recommend deleting it once #3 is fixed and
the canonical `bin/simple` works.

---

## 5. `text_arg_indices` missing `rt_cocoa_*` / `rt_win32_*` entries

**Where:** `src/compiler_rust/compiler/src/codegen/instr/calls.rs:119`

**Symptom:** A native-built `.spl` calling `rt_cocoa_window_new(W, H, "title")`
crashes inside `rt_cocoa_window_new` because the title arg is passed as a
single tagged-`i64` RuntimeValue while the C ABI declares `*const c_char`.

The compiler maintains a list of FFI symbols whose `text` parameters need to
be expanded to `(ptr, len)` pairs at call sites. The Cocoa / Win32 hosted
window functions were missing.

**Status:** Fixed in commit `084d33dd`. Added:
```rust
"rt_cocoa_window_new" | "rt_win32_window_new" => Some(&[2]),
```

The companion change in `src/runtime/hosted/cocoa.rs` makes
`rt_cocoa_window_new` accept a tagged-i64 RuntimeValue and decode it via
`rt_string_data` / `rt_string_len` so it works either way.

---

## 6. `strip_llvm_constructors` kills ObjC class registration on macOS

**Where:** `src/compiler_rust/compiler/src/pipeline/native_project/tools.rs:200`

**Symptom:** Any native-built Simple binary that touches Cocoa segfaults
inside `dyld strlen` from this stack:
```
sel_registerName(NULL)
___forwarding___
_CF_forwarding_prep_0
NSApplication::sharedApplication
rt_cocoa_window_new
spl_main
```

**Root cause:** `strip_llvm_constructors` runs `llvm-objcopy` on
`libsimple_native_all.a` to strip LLVM static constructors (LIM-010). The
macOS branch additionally stripped `__DATA,__mod_init_func` and
`__DATA,__mod_term_func`. Those sections also contain ObjC class
registration thunks; without them the `NSApplication` class lookup returns
`nil` and the first method dispatch goes through CF forwarding, which
eventually calls `sel_registerName(NULL)` and crashes.

**Status:** Fixed in commit `b1ee41a2`. The macOS-specific
`--remove-section` flags have been removed — LIM-010 only affects
`--backend=llvm-lib` (opt-in), so the Cranelift default path is unaffected.

---

## 7. `cocoa.rs` API drift vs objc2-app-kit 0.2.2

**Where:** `src/runtime/hosted/cocoa.rs`

When built with `--features cocoa-real`, the runtime had 6 Rust compile errors
plus 4 warnings against the current vendored `objc2-app-kit 0.2.2`:

- `unresolved imports`: `NSApplicationActivationPolicy`,
  `NSBackingStoreType`, `NSBitmapImageRep`, `NSImageView` not exported from
  the crate root — the underlying types existed but the crate's
  `#[cfg(feature=…)]` gates required additional features
  (`NSGraphics`, `NSControl`, `NSImageRep`, `NSBitmapImageRep`,
  `NSRunningApplication`).
- `NSWindow::alloc(mtm)` / `NSImageView::alloc(mtm)` / `NSImage::alloc()`
  were the wrong shape — `ClassType::alloc` takes no args and requires
  `IsAllocableAnyThread`. For main-thread-only classes the correct call is
  `mtm.alloc::<NSWindow>()` (free fn on `MainThreadMarker`).
- `mask.0` on `NSEventMask` should just be `mask` — the API expects the
  newtype directly, not its inner `u64`.
- 4 `unused unsafe` warnings on AppKit calls that are no longer marked
  `unsafe` in 0.2.2.

**Status:** Fixed in commits `5b96901f` (initial alignment) and `084d33dd`
(text marshalling). Cargo.toml feature additions in `5b96901f` opt the
runtime into the right objc2-app-kit features. `cargo build -p
simple-native-all --features cocoa-real` now succeeds with only the two
deprecation warnings noted in #12.

---

## 8. Hosted runtime stubs in deployed `libsimple_native_all.a`

**Where:** `src/compiler_rust/target/{release,bootstrap}/libsimple_native_all.a`
on disk (and any release artifact built before 2026-04-15).

**Symptom:** A binary linked against the deployed runtime gets all
`rt_winit_*`, `rt_cocoa_*`, `rt_hosted_*` symbols compiled to:
```asm
mov  x0, #0x3   ; the Simple `nil` tag
ret
```
i.e. they always return nil. The Simple side checks `if win == 0` (zero) so
the nil sentinel slips past the guard, and the next FFI call dereferences
`0x3` as a handle — quiet success followed by SIGSEGV later.

**Diagnosis:** `simple-native-all` was last built without the `gui` /
`cocoa-real` / `win32-real` features. The hosted SFFI module is shipped as
"stubs only" and only flips to real implementations when those features are
opt-in.

**Status (this session):**
- Added `cocoa-real` / `win32-real` features to `native_all/Cargo.toml`
  (commit `5b96901f`).
- Rebuilt `libsimple_native_all.a` locally with `--features cocoa-real` after
  the vendor repair (#1). Real `_rt_cocoa_window_new` is now in the
  bootstrap archive.

**Remaining work:** the released artifacts under `bin/release/<triple>/`
were produced by the older self-hosted compiler and still ship stubs. A full
`scripts/bootstrap/bootstrap-from-scratch.sh --deploy` is needed to refresh
them.

---

## 9. NSApplication crash even with the real cocoa runtime

**Where:** Native-built Simple binary calling `rt_cocoa_window_new`.

**Symptom:** Even after bugs #5–#8 are fixed and a binary links against a
freshly-built `libsimple_native_all.a` with `cocoa-real`, the first call
into `NSApplication::sharedApplication(mtm)` still crashes the same way
described in #6 — `sel_registerName(NULL)`. The strip is no longer the
culprit (the strip flags have been removed) but the class lookup still
fails.

**Hypothesis:** The Simple-compiled binary's startup misses some ObjC
runtime initialization that a normal Rust `main()` performs (libobjc
constructors, `__objc_init`, framework `+load` methods). Possible fixes:

1. **Rust shim main:** ship a tiny `main()` in C/Rust that calls
   `objc_init()` (or just `[NSApplication sharedApplication]` once) before
   delegating to the Simple `spl_main`.
2. **Bypass objc2 lazy classes:** rewrite `cocoa.rs` to call `objc_msgSend`
   / `objc_getClass("NSApplication")` directly, no `cached_class!`,
   matching what AppKit examples do.
3. **Full bootstrap rebuild** may surface a different startup path that
   already initializes ObjC.

**Status:** Open. Not investigated further this session; needs a focused
ObjC/Mach-O ABI session.

---

## 10. Rust seed lacks the `gui` feature by default

**Where:** `src/compiler_rust/compiler/src/interpreter_extern/mod.rs:1247`

```rust
#[cfg(feature = "gui")]
_ if name.starts_with("rt_winit_") => winit_ffi::dispatch(name, &evaluated),
```

Without the `gui` feature, the seed binary's interpreter says "unknown extern
function: rt_winit_event_loop_new" for any `.spl` calling the winit FFI.
Building the seed with `cargo build --profile bootstrap -p simple-driver
--features gui` is blocked by the `log` crate gap from #1; once #1 is
addressed we should add `gui` to the bootstrap script's default features.

---

## 11. `bin/simple_stage3` is x86-64 ELF on macOS arm64

**Where:** `bin/simple_stage3` (84 MB, dated 2026-03-08).

```
$ file bin/simple_stage3
ELF 64-bit LSB executable, x86-64
$ bin/simple_stage3 --help
exec format error
```

Stale Linux artifact checked into a macOS-deployed bin/. Either remove it,
gate behind a per-platform symlink, or rebuild for the host triple.

---

## 12. `cocoa.rs` cosmetic warnings (cocoa-real build)

```
warning: use of deprecated method `objc2_app_kit::NSApplication::activateIgnoringOtherApps`:
         This method will be deprecated in a future release. Use NSApp.activate instead.
warning: unnecessary `unsafe` block
```

Trivial follow-up: replace the two `app.activateIgnoringOtherApps(true)`
call sites with `app.activate(...)` once the minimum objc2-app-kit version
is pinned high enough.

---

## Reproducer reference

| Bug | Reproducer |
|-----|-----------|
| 1 | `cd src/compiler_rust && cargo build --profile bootstrap -p simple-driver` |
| 2 | Re-introduce `UIEvent.KeyPress(key: key)` in `src/lib/common/ui/session.spl` and run `bin/simple native-build --entry-closure --entry session_test.spl ...` |
| 3 | `echo 'fn main() -> i64: return 0' > /tmp/h.spl && bin/simple /tmp/h.spl` |
| 4 | Same as #3 with `bin/simple_mac` |
| 5 | Pre-fix: any `extern fn rt_cocoa_window_new(_,_,title: text)` call segfaults; post-fix: `nm bin/simple \| grep text_arg_indices` references include `rt_cocoa_window_new` |
| 6 | Pre-fix: `bin/simple native-build --entry tests/cocoa_smoke.spl` then run → strlen NULL crash via `___forwarding___`; post-fix: build no longer passes `--remove-section=__DATA,__mod_init_func` (verify with `strings src/compiler_rust/target/bootstrap/simple \| grep mod_init_func`) |
| 7 | Pre-fix: `cd src/runtime/hosted && cargo build --release --features cocoa-real` → 6 errors |
| 8 | `otool -tv <binary> \| grep -A1 '^_rt_cocoa_window_new:'` shows `mov x0, #0x3; ret` |
| 9 | Build a `.spl` that calls `rt_cocoa_window_new` against a `cocoa-real` runtime, run, observe `dyld strlen` crash with the backtrace shown in §6 |
| 10 | `cd src/compiler_rust && cargo build --features gui` (also requires #1 to land) |
| 11 | `file bin/simple_stage3` |
| 12 | `cd src/runtime/hosted && cargo build --release --features cocoa-real 2>&1 \| grep warning:` |

## Commits referenced

- `451aea67` `fix(ui): harden ui access and web wm startup` — match-arm rewrites for #2 (originally authored by user; my session/access fixes were folded in by the user).
- `5b96901f` `fix(runtime/cocoa): align cocoa-real with objc2-app-kit 0.2.2 API` — #7 + Cargo.toml feature wiring for #8.
- `084d33dd` `fix(runtime/cocoa+codegen): pass title via runtime-value decode + register text_arg_indices` — #5 + the runtime-side text decoder for #7.
- `b1ee41a2` `fix(native-build): stop stripping __mod_init_func/__mod_term_func on macOS` — #6.
