# Cocoa frame objects leak under manual reference counting

Date: 2026-09-23. Base: `6d33ed254d4`.

## Cause and change

`src/runtime/hosted_cocoa.c:rt_cocoa_layer_present` creates an owned
`NSBitmapImageRep` and `NSImage` with `alloc/init`. Its build does not enable ARC.
The autorelease pool does not release those ownership claims. Every replaced
image and its full bitmap therefore remain allocated: a 3840 × 2160 frame has
33,177,600 bytes of bitmap storage, before object overhead.

The fix releases local ownership after `addRepresentation:` and `setImage:`
have retained their arguments. It also releases the bitmap when bitmap storage
is absent or image initialization fails. A nil bitmap safely accepts `release`.
Pixel conversion, allocations, copying, and the presentation API are unchanged.

## Evidence

The native regression is
`test/01_unit/runtime/hosted_cocoa_frame_ownership_test.m`. It includes the real
runtime source, substitutes allocation subclasses that count actual `dealloc`
calls, and uses the real AppKit `NSImageView` and retaining setters. It requires
macOS, creates no visible window, and is compiled explicitly without ARC:

```sh
clang -fno-objc-arc -framework Cocoa -Werror \
  test/01_unit/runtime/hosted_cocoa_frame_ownership_test.m \
  -o /tmp/cocoa-ownership
/tmp/cocoa-ownership
```

- Final regression against the unmodified base: FAIL on the second frame,
  `live objects: bitmap=2 image=2; expected 1 1`, exit 134.
- Patched regression: PASS for 100 replacements, exact RGBA pixel preservation,
  bitmap allocation failure, absent bitmap storage, failed image initialization,
  subsequent successful presentation, and final zero live image/bitmap objects.
- Patched run: 0.39 seconds wall time, 21,479,424 bytes maximum RSS reported by
  `/usr/bin/time -l`. This is a bounded lifecycle check, not a throughput claim.
- Clang ownership analysis went from three diagnostics to one unrelated window
  diagnostic; no diagnostic remains in `rt_cocoa_layer_present`.

```sh
clang --analyze -x objective-c -Xanalyzer -analyzer-output=text \
  src/runtime/hosted_cocoa.c -o /dev/null
```

The first test build used AddressSanitizer, but it spun before `main` in
`__asan::InitializeShadowMemory` / `__sanitizer::StaticSpinMutex::LockSlow`.
The owned process was terminated; a sample is retained locally under
`build/evidence/cocoa-frame-ownership/baseline-sample.txt`. ASan coverage is
unverified. The unsanitized regression and Clang ownership analysis completed.

## Separate remaining defect

Window creation also combines `alloc/init` ownership with `CFRetain` for
`ns_window` and `ns_view`, while close only balances the extra retain. Its
`calloc` failure path does not release the created AppKit objects. The residual
Clang diagnostic is the potential `ns_view` leak on that failure path.
Window ownership and close/error behavior require a separate lifecycle fix and
test. This frame fix does not establish leak-free window creation/destruction.
