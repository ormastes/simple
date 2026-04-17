# Bug Report: Generic Guest JS Runtime Bootstrap Faults on x86_64 QEMU

**Date:** 2026-04-16
**Bug ID:** `js_runtime_guest_001`
**Status:** open
**Severity:** P1

## Summary

The remaining guest browser-runtime blocker is now below the browser layer. Direct QEMU probes show the generic bare-metal `JsRuntime` bootstrap faults during object-store and environment-stack setup, before a normal guest JS/browser path can be considered reliable.

## Reproducers

- `test/system/js_runtime_in_qemu_spec.spl`
- `test/system/js_browser_host_in_qemu_spec.spl`
- manual QEMU logs:
  - `build/os/js_runtime_probe_manual.log`
  - `build/os/js_browser_host_probe_manual.log`

## What Is Still Green

- Hosted browser/session specs remain green:
  - `test/unit/lib/common/web/browser_session_spec.spl`
  - `test/unit/lib/common/web/browser_session_async_spec.spl`
- The browser runtime probe path in `BrowserSession` is green only via the explicit guest fast path already documented in the session report.

## Current Fault Evidence

Resolved serial RIPs and logs place the failures in:

- `lib__common__js__engine__vm__ObjectStore_dot_allocate`
- `lib__common__js__engine__vm__ObjectStore_dot_set_property`
- `lib__common__js__engine__interpreter_types__EnvironmentStack_dot_define_var`
- bare-metal `rt_array_push`

This indicates a generic guest runtime/bootstrap storage bug rather than a remaining lexer/parser/member-access issue.

## Scope

This bug blocks:

- generic bare-metal `JsRuntime` parity in QEMU
- generic browser host-object integration on the guest
- removal of the guest-only browser runtime fast path

This bug does **not** block:

- hosted browser-session behavior
- deterministic browser guest flow already using the documented fast path

## Recommended Next Work

1. Add an isolated QEMU probe for `EnvironmentStack.new() -> create_env() -> define_var()`.
2. Add an isolated QEMU probe for `ObjectStore.new() -> create_object() -> set_property()`.
3. Instrument bare-metal `rt_array_push` in `examples/simple_os/arch/x86_64/boot/baremetal_stubs.c` with pointer, header type, len/cap, and growth-path logging.
4. Fix the generic runtime/bootstrap bug first, then remove the guest-only browser fast path.

## Related Report

- `doc/09_report/session/browser_runtime_heap_bug_2026-04-16.md`
