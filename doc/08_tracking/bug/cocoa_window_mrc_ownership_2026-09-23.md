# Cocoa window ownership leaks and close lifetime

Date: 2026-09-23. Base: `d832604d7a2` (Cocoa frame ownership fix).

## Cause and change

`rt_cocoa_window_new` retained `NSWindow` and `NSImageView` a second time after
`alloc/init`, but close balanced only one reference. The record-allocation
failure leaked both objects; handle-table exhaustion also retained both. Nil
window/view initialization was not rejected before storing the handle.

The record now receives the existing `alloc/init` ownership. Allocate the record
before creating AppKit objects, unwind failed initializers, and show the window
only after handle insertion succeeds. A failed title allocation returns the
invalid handle; undecodable UTF-8 titles fall back to `untitled`.

Set `releasedWhenClosed:NO` because the runtime handle owns the window even
after a user closes it. Runtime close removes the handle, closes the AppKit
window, and releases both owned objects inside the autorelease pool. Close now
requires the main thread, matching creation, resize, and presentation; a rejected
worker-thread close leaves the handle intact. This prevents worker teardown
from racing these main-thread operations.

## Native regression and evidence

`test/01_unit/runtime/hosted_cocoa_window_ownership_test.m` includes the production
implementation, uses real AppKit windows and retaining setters, counts subclass
allocations/deallocations, and injects allocation failures. Run in a macOS GUI
login session; windows briefly appear. AppKit keeps display/animation references
past immediate pool draining, so each cycle permits up to 100 bounded event-loop
turns of 10 ms before requiring zero live windows/views and zero handles.

```sh
clang -fno-objc-arc -framework Cocoa -Werror \
  test/01_unit/runtime/hosted_cocoa_window_ownership_test.m -o /tmp/cocoa-window
for mode in normal record-failure table-full window-failure view-failure user-close thread; do
  /tmp/cocoa-window "$mode" || exit
done
```

- Baseline with the final event-draining test: normal close FAIL, exit 134,
  `live windows=1 views=1; expected 0 0`.
- Earlier baseline failure injection: record allocation and table-full each
  leave one window and one view; window/view initialization failures exit 133.
- Patched normal, user-close, and worker-thread scenarios: PASS, 20 cycles each,
  including resize, frame presentation, layer release, and duplicate close.
  User-close exercises the real close-button action before further handle use.
- Patched record allocation, full table, and both initializer failures: PASS;
  invalid handle returned, no remaining owned objects or handles.
- Timed lifecycle runs: normal 4.97 s / 50,823,168-byte max RSS; user close
  2.61 s / 50,921,472 bytes; worker close 5.43 s / 50,872,320 bytes. These are
  bounded lifecycle checks, not a throughput benchmark.
- Frame ownership regression: PASS, 100 replacements and three failure paths.
- Clang ownership analysis: baseline one `osx.cocoa.RetainCount` window-path
  diagnostic; patched zero diagnostics. Non-macOS stub compilation and
  `git diff --check` also pass.
- Independent Astra source/test review: ACCEPT, no blocking findings.

Local logs/binaries are under `build/evidence/cocoa-window-ownership/`.
ASan was not rerun: the predecessor frame task documented sanitizer startup
failure before main. No full compiler rebuild or deployment was performed.

Integration order: frame fix `d832604d7a2`, then this window fix. Unrelated
golden-image worktree changes are excluded.
