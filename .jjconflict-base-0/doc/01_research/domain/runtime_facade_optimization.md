<!-- codex-research -->
# Runtime Facade Optimization - Domain Research

## Ruby

Ruby exposes native optimization through extension libraries and VM hooks while
keeping Ruby source code on ordinary Ruby APIs. The Ruby extension guide
documents defining Ruby classes and methods from C with `rb_define_method`, and
calling Ruby methods through APIs such as `rb_funcall`; extension authors are
also warned that `rbimpl_` and `RBIMPL_` symbols are implementation details.

Ruby Fiber scheduling follows the same shape for I/O optimization: normal
`IO#read`, `IO#write`, and sleep-style calls can invoke scheduler hooks in
non-blocking fibers. The program calls Ruby-level APIs; the optimized scheduler
or VM hook is selected behind that interface.

Sources:
- https://docs.ruby-lang.org/en/master/extension_rdoc.html
- https://docs.ruby-lang.org/en/master/Fiber/Scheduler.html

## Python

Python's standard library describes built-in modules written in C that expose
system functionality such as file I/O through portable Python APIs. User code
imports and calls the Python module, not the internal C entrypoint.

CPython's vectorcall protocol is a call optimization behind callable objects.
The C API documentation says CPython prefers vectorcall internally when a
callable supports it, but callers still use the normal call API surface.

Sources:
- https://docs.python.org/3/library/index.html
- https://docs.python.org/3/c-api/call.html

## Implication For Simple

Simple should mirror this pattern:

- User/app code imports `std.*` APIs.
- Runtime symbols are private implementation details of std facades or generated
  binding modules.
- The compiler or startup cache may choose a faster runtime-backed path after it
  validates compatible signatures.
- Tests should assert both sides: app code has no direct `rt_*` usage, and the
  deployed optimized binary still starts and answers representative requests.
