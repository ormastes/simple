# `bin/simple run` corrupts extern-returned `text`, turning a working 3-device Vulkan host into a silent `skip:` that specs record as a PASS

**Status:** OPEN
**Found:** 2026-08-20
**Component:** `bin/simple run` value path (JIT/native codegen) for `extern fn … -> text`
returns. NOT a Vulkan, ICD, loader, or device-enumeration defect — those are all healthy.
**Attribution:** measured on a private build
(`cargo build --release --bin simple --features simple-compiler/vulkan`), host with
NVIDIA RTX A6000 + TITAN RTX, `vulkaninfo --summary` apiVersion 1.4.312, driverName NVIDIA,
`/usr/share/vulkan/icd.d/nvidia_icd.json` present.
**Discovered while:** resolving
`vulkan_submit_and_wait_fence_blocks_unconditionally_no_nonblocking_submit_2026-08-07.md`,
where `simple run` reported `skip:vulkan-physical-device-required` while `simple test`
used both GPUs successfully in the same tree, same binary, same session.

## What was found

`VulkanLaneSession.probe()` returns `skip:vulkan-physical-device-required` under
`bin/simple run` on a host with three enumerable Vulkan devices. The skip is produced by
the LAST check in `probe()`
(`src/lib/gc_async_mut/gpu_lane/vulkan_lane_session.spl`):

```
val device_type = vulkan_sffi_device_type(self.device_ordinal)
if device_type != "discrete" and device_type != "integrated":
    return "skip:vulkan-physical-device-required"
```

Everything before it succeeds — loader available, instance init OK, `device_count` = 3,
`select_device(0)` = true. The runtime genuinely returns `"discrete"`. The CONSUMER sees a
corrupt string.

## Evidence — identical source, identical device, two execution paths

Same helper, same extern, same machine, run minutes apart:

| path | `t.len()` | `t == "discrete"` |
|------|-----------|-------------------|
| `simple test` | **8** | **true** |
| `simple run`  | **-1** | **false** |

`len() == -1` is the known native-codegen corruption sentinel — the same signature
documented for `Dict.len()` in `.claude/rules/code-style.md` ("Native-Codegen Dict
Pitfalls"). It is not an empty string: an empty string has len 0 and would still be a
legitimate (if wrong) value. `-1` means the value is not a valid string at all.

Under `run` the corruption is **shape-dependent**, which is why it went unnoticed:

- `val t = vulkan_sffi_device_type(0)` used inline in `main()` → `len=8`, correct.
- The same value passed across a function-parameter boundary → `len=-1`.
- `print("literal" + vulkan_sffi_device_type(0))` → prints an **empty line**: the whole
  concatenation collapses, silently discarding the literal prefix too.
- Some call shapes (`vulkan_sffi_selected_device_name()`) silently ended all further
  output from the script with exit code 0.

Under `test` both the inline and the cross-function shapes are correct.

## Why this matters more than one skipped lane

**A false skip is worse than a red test, because it is recorded as a PASS.** The
established spec idiom is:

```
if probe_result.starts_with("skip:"):
    step("No usable Vulkan device/ICD on this host: " + probe_result)
    assert_true(probe_result.starts_with("skip:"))
```

The assertion succeeds *because* the probe skipped. The example is counted green, and the
file verdict reports `skipped=0` — the runner never learns a skip happened. So on a
GPU-capable host, a lane whose device coverage is entirely fictional reports exactly the
same verdict as one that genuinely exercised the hardware.

Scope of the idiom: **27 spec files** match `starts_with("skip:")`, of which **12** use the
`assert_true(probe_result.starts_with("skip:"))` shape that converts a skip directly into a
pass (`/usr/bin/grep -rn 'assert_true(probe_result.starts_with("skip:"))' test/ | wc -l`).
They span the Vulkan, CUDA and Metal gpu_lane conformance suites plus remote-baremetal.

**Stated plainly: any GPU lane that probes via the `run` path has never actually exercised
a device on this host.** Its greens attest to nothing. This is the automated form of the
same false belief that, earlier in this same session, wrongly wrote off the machine as
having no GPU at all.

## What is NOT the cause (ruled out by measurement, not assumption)

- Not a missing/!invisible ICD — `nvidia_icd.json` is installed and 3 devices enumerate.
- Not loader resolution — `vulkan_sffi_is_available()` and `vulkan_sffi_init()` both return
  true on the `run` path.
- Not enumeration — `vulkan_sffi_device_count()` returns 3 on the `run` path.
- Not device selection — `vulkan_sffi_select_device(0)` returns true on the `run` path.
- Not the extern being unbacked — it is registered in all four tables and
  `check-unbacked-extern-ratchet.shs` reports `0 new, 0 stale`; an unbacked extern fails
  loudly with `semantic: unknown extern function`, which is not what happens here.
- Not ordering — `device_type` is corrupt both before and after `select_device`.

## Suggested fix

Fix `text` return-value handling for `extern fn … -> text` on the `run` path's
JIT/native-codegen route so a returned string survives (a) assignment, (b) being passed as a
function argument, and (c) concatenation with a literal. The `test` path already does this
correctly and can serve as the reference behaviour. This is the same defect family as the
resolved native Dict `.len()`/`.get()` decode bugs, so that fix is likely the right place to
look first.

Separately, and independently of the codegen fix, the spec idiom should be hardened: a
`skip:` on a host that can be shown to have a device must not be recorded as a pass. Either
report it through the runner's real skip channel (so `skipped=N` is non-zero and visible in
the verdict) or fail closed when a capability probe skips on hardware that other paths can
demonstrably drive.

## Reproduce

```bash
cd src/compiler_rust && cargo build --release --bin simple --features simple-compiler/vulkan
```

Then a script calling `vulkan_sffi_device_type(0)`, storing it in a `val`, and passing it to
a helper that prints `value.len()`:

- via `simple run <script>.spl`  → `len=-1  discrete=false`
- via `simple test <spec>.spl`   → `len=8   discrete=true`
