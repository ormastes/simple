# Tautology-shell spec dispositions — final 5

**Date:** 2026-08-09
**Context:** A census found 27 env-gated specs whose gates fail OPEN. 12 were
"tautology shells": every `it` asserted only that its own gate was closed, e.g.

```simple
expect(test_env_require("SIMPLE_GPU_TEST")).to_equal("blocked:SIMPLE_GPU_TEST")
```

That asserts nothing about the code under test. A sibling stream resolved 7.
This record covers the remaining 5, which were deferred because none of them
carried a false `@cover` claim.

## `@cover` verification

**None of the five declares `@cover` at all** — verified by grepping `@cover`
across all five files (and their duplicate copies under `test/feature/` and
`test/unit/`): zero hits. So there was no false coverage claim to retract. The
problem was purely that the specs asserted nothing.

## What was explicitly NOT done

The tempting "fix" — flipping the expected value from `"blocked:X"` to
`"ready"` — was rejected. It turns the shell green while still testing nothing,
and additionally makes the spec fail on any host where the gate is closed. Each
spec below got a *reasoned* disposition instead.

## Dispositions

| Spec | Disposition | Justification |
|---|---|---|
| `test/03_system/feature/usage/vulkan_spec.spl` | **(a) real assertion, gate kept for device work** | Nine describe-blocks collapsed to three real ones. `vulkan_loader_init()` is a host-independent probe: it returns a structured `VulkanLoaderResult` whether or not an ICD exists, so the loader *contract* is assertable everywhere and now is — success implies `handle > 0`, failure implies `handle == 0` **and** a non-empty `error`, and two consecutive probes must agree. Actual device work still requires `SIMPLE_GPU_TEST=1`; when closed the spec prints `SKIP (no device assertion made): ...` so the skip is visible rather than disguised as a pass. |
| `test/03_system/feature/usage/vhdl_spec.spl` | **(a) real assertion + bug filed** | The `VhdlToolResult` record contract (exit code, stdout, stderr fidelity) is pure data and is now asserted unconditionally. The availability probes could **not** be asserted: writing a real call to `ghdl_available()` immediately exposed `semantic: unknown extern function: rt_process_run_capture` — the extern is declared in `src/app/io/vhdl_sffi.spl` but implemented in neither the Rust seed nor `src/runtime/`, making the entire GHDL/Yosys wrapper dead code. Filed as `doc/08_tracking/bug/vhdl_sffi_rt_process_run_capture_extern_missing_2026-08-09.md`; the probe calls live in the gate-open branch so an operator who opens the gate sees the real defect. This defect is exactly what eight tautology shells had been hiding. |
| `test/03_system/feature/usage/vhdl_golden_spec.spl` | **(a) real assertion, gate REMOVED entirely** | The gate was wrong on its face. `VhdlBuilder` (`src/compiler/70.backend/backend/vhdl/vhdl_builder.spl`) is pure Simple text generation — it needs no GHDL, no Yosys, no hardware — yet it sat behind `SIMPLE_VHDL_TEST=1` and so was exercised on no host at all. Now ungated and asserting library-header emission, a balanced `entity ... end entity x;` block with its ports, the no-trailing-semicolon rule on the final port (`is_last: true`, whose absence would be a VHDL syntax error), and that two builders do not share a buffer. |
| `test/03_system/feature/usage/tensor_interface_spec.spl` | **(a) real assertion, gate narrowed to the torch half** | `SIMPLE_GPU_TEST` gated the *whole* file, including `PureTensor`, which needs no GPU, no CUDA and no libtorch. The core half is now ungated: shape/`numel` agreement, `zeros()` genuinely zero-filled and `ones()` genuinely one-filled (not merely allocated), get/set round-trip leaving neighbours untouched, and reshape preserving element count. Only torch-backed parity — which needs an external runtime — stays gated, with a visible skip. |
| `test/01_unit/app/serial_mcp/serial_mcp_spec.spl` | **(c) gated shells KEPT and documented; a separate real tautology fixed** | This one is not like the others. Only 4 of its 12 examples are gate-shells, and the other 8 are real assertions against real dispatch/protocol code — the module is not coverage-starved. The 4 shells guard `serial_open` / `ssh_serial_connect`, which touch a physical `/dev/ttyUSB*` that this host does not have, and opening the gate is not merely unavailable but **unsafe**: a USB replug caused a SIGSEGV that cascaded through `systemd exit.target` and killed an entire tmux session on 2026-05-30 (bug `serial_usb_sigsegv_cascade`). The honest unblock is the SIGSEGV guard plus a pty/loopback fixture, not a rewritten assertion; that reasoning is now recorded in the spec header so the next reader does not "fix" it. **Separately**, a genuine vacuous assertion was found and fixed in the same file: `expect(found or not found).to_equal(true)` held for every possible return value; it now asserts `get_arg(...) == "val"`, plus a new example pinning the missing-argument case. |

## Duplicate trees

Each spec exists twice — `test/03_system/feature/usage/` and `test/feature/usage/`,
`test/01_unit/app/` and `test/unit/app/` — as byte-identical copies (verified
with `diff -q`). Both copies were updated together. The duplication itself is
pre-existing and out of scope here, but is worth collapsing: it doubles the cost
of every future spec edit and lets the two copies drift apart silently.
