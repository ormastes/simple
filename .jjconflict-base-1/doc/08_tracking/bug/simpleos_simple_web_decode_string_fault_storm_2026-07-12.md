# SimpleOS Simple Web `decode_string` Fault Storm

**Status:** decode-string fault fixed live; canonical renderer now stalls before first frame
**Component:** stage3 freestanding Simple Web HTML/CSS rendering
**Evidence:** `build/simpleos_wm_simple2d_goal/serial.log`

The production SimpleOS WM reaches the 3840x2160 scanout, creates three
process-owned surfaces, and enters canonical Simple Web content production.
The first content render then repeatedly faults in baremetal
`decode_string`, reached through `rt_string_contains`/`rt_string_starts_with`.
Observed invalid values decode as heap-like pointers including
`0x8100000000`, `0x1400000000`, and `0x1100000000`.

This remains after:

- replacing recursive 16-argument/seven-array layout calls with one
  heap-backed `HtmlLayoutContext` and scalar height returns;
- removing the wide root layout call/return boundary;
- replacing the 15-argument WM content-frame implementation boundary with a
  heap-backed `SimpleWebContentFrameRequest` for the SimpleOS caller.

The first root cause is an array-return ABI mismatch in bare-metal
`rt_string_split`: it returned the encoded handle produced by `rt_array_new`,
while hosted `runtime_native.c` and generated `[text]` indexing expect the raw
`RuntimeArray*`. `_html_scan_events` indexed the encoded header at the wrong
offset and passed bogus tagged values to `starts_with`, matching the observed
fault addresses. The bare-metal implementation now retains the encoded handle
only for `rt_array_push_handle` and returns `DECODE_PTR(arr)` on every exit.

The offline contract is covered by
`test/01_unit/runtime/baremetal_string_split_abi_spec.spl`. A fresh session must
run the live gate; if a second fault appears, add allocation-free scalar phase
markers around request/full-HTML/parse/CSS/style/layout/paint before changing
the parser. Do not weaken the zero-fault gate or substitute the native-safe/
tag-strip compatibility renderer.

Acceptance requires zero exception frames, three valid nonzero-checksum
`WmContentFrame` values, a later Simple 2D presented frame, and post-input QMP
readback from the same guest run.

The first attempted follow-up reused an ELF older than `baremetal_stubs.c`
because the evidence wrapper watched only `*.spl`. The wrapper now treats C,
headers, assembly, and linker scripts as kernel dependencies. A rebuilt ELF
contains a strong `rt_string_split` plus tag clearing on all four returns, and
the subsequent guest run produced zero exception frames.

The remaining first-frame failure is a stall inside the canonical renderer:
the latest serial reaches `canonical-render-begin` for window 1 (452x264, 78
HTML bytes) but not `canonical-render-complete`. This is no longer evidence of
a decode-string fault. The next bounded diagnostic should route that call
through the existing stage-traced canonical renderer to distinguish parse,
CSS, style, layout, framebuffer initialization, and paint latency. Visible
QEMU remains gated until canonical rendering and Engine2D presentation pass.

Later pure-DrawIR live evidence refined this further. The stale split fault is
still gone, and the production shell now reaches canonical DrawIR generation.
Three bounded QEMU cycles exposed two independent stage3 aggregate hazards:

- missing `HtmlLayoutContext` helpers were auto-stubbed and returned nil;
- after restoring the real `layout(...)`, `compute_styles(...) -> [Style]`
  preserved array shape but yielded nil `Style` elements at the first layout
  access (`layout` RIP `0x597690`).

The renderer now fills caller-owned `[Style]` storage through
`compute_styles_into` and returns only a scalar count. This final ABI fix is
offline-only for this turn because the mandatory three-cycle QEMU cap was
reached; the next fresh session must test it before visible launch.

Fresh-turn evidence showed caller-owned mutation was also copy-isolated and
that local `styles.push(...)` calls were discarded under stage3. The canonical
cascade is now inlined into the DrawIR producer and default-style allocation
uses explicit copy-commit (`styles = styles.push(...)`). The same first-layout
RIP persisted until that final copy-commit correction; it has not yet had a
fresh QEMU run because this turn also reached the three-cycle cap.

The next bounded run proved the first nil was actually `HNode`, not `Style`:
inlining canonical parsing moved the first fault from `layout` to the first use
of the returned `HtmlChildIndex` inside `build_selector_context`. The DrawIR
producer now keeps AST construction, child-index construction, selector-index
construction, style cascade, layout, and projection in one freestanding frame.
This final child/selector-index inlining is offline-only after the turn's third
QEMU cycle.

After AST inlining, scalar markers showed `allocated=1 populated=1` and
`first_child[0]=3` despite explicit local initialization to `-1`. The immediate
corruption is the array-field copy into `HtmlChildIndex`, not HNode indexing.
The in-frame selector builder now consumes raw `first_child`/`next_sibling`
arrays directly, and the event-count marker was moved from unused `parse_html`
to the actual inlined parser. This correction is offline after the third cycle.

The correctly placed marker exposed the systemic runtime contract: `html=644`
but both nested event-array lengths read as `1153202240580805315`, while an
explicitly assigned `first_child[0]` read back as `NIL_VALUE` (`3`). Hosted
`runtime_native.c` uses raw `SplArray*` for `rt_array_new/get/set`, but the
x86_64 bare-metal runtime returned and required tagged handles. The bare-metal
array constructor/access/mutation ABI now uses raw pointers and accepts legacy
tagged handles internally. This fix supersedes further renderer-specific
inlining, but is offline after cycle 3.

Further runtime/source correlation found the direct cause: pure-Simple MIR
lowers `[value; count]` to `rt_array_repeat`, while x86_64 bare-metal implemented
`rt_array_repeat` as an unconditional `NIL_VALUE` stub. That exactly accounts
for nil text event arrays, nil HNode/Style arrays, and `first_child[0] == 3`.
The stub now implements the hosted semantics (tagged array allocation, known
length, repeated runtime values). Constructor/push representation remains
tagged; accessors accept tagged or decoded pointers. This definitive fix is
offline after the third cycle and must be tested before removing diagnostics
or renderer-local containment.

## 2026-07-13 — ROOT CAUSE NAMED + FIX VERIFIED (decode storm eliminated)

Marker-bisect on the FULL harness (build/simpleos_wm_ds_diag) + ELF symbolization
named the exact chain:

- `decode_string` faults at `s->hdr.type` on values like `0x1400000001` = a
  `RuntimeString` header `{u32 type=1, u32 size}` dereferenced one level too deep
  and mistaken for a tagged handle.
- caller = C `rt_string_starts_with`; its caller (via `__builtin_return_address(1)`,
  both frames keep rbp) = Simple `Path.starts_with` (fs_driver/types.spl:190).
- ELF: `Path.starts_with`'s address is indirect-called from ~20 PURE-`text`
  functions that never import Path — `simple_web_html_layout_renderer`
  (`_html_scan_events` line 522 `seg.starts_with("!--")`, line 570
  `parts[j].starts_with(closer)`) and `ui.theme_package._root_value/_section_value/
  _section_items/_strip_value/_argb_from_css`.

ROOT: stage3 loses the `text` element type of `split(...)` results and
`line.trim()` chains; `.starts_with` on the type-erased receiver statically
resolves to the only user method named `starts_with` = struct `Path.starts_with`,
which dereferences the receiver as a Path struct (`self.raw`) → RuntimeString
header → fault. Statically-typed `text` receivers inline `rt_string_starts_with`
(26 refs) and never fault.

FIX (live-proven, bad-call count 16 → 2 → 0, zero exception frames): force the
receiver to a concrete `text` type via interpolation — `val x: text = "{expr}"`
then `x.starts_with(...)`. A bare local annotation (`var seg: text = parts[k]`)
does NOT re-bind (proven; count stayed 16). Applied to `_html_scan_events`
(522, 570) and all `theme_package` `line.trim()`/`value.trim()`/`line.starts_with`
sites. Re-apply script (sweep-proof): scratchpad .../decode-string/reapply_fixes.py.

TRUE durable fix (compiler, out of scope this turn): stage3 method resolution /
element-type inference must prefer the string builtin and never bind an
incompatible struct method to an unresolved/`text` receiver.

NEXT BLOCKER (separate, pre-existing, exposed once decode storm cleared): full
first-frame render allocates past the 144MB heap-debug watermark (~154MB of
192MB); `malloc()` logged every alloc past the mark (~11800 `[heap] alloc` serial
lines) → `guest-serial-fault-storm`. FIX applied in baremetal_stubs.c: log ONCE at
watermark crossing (keep ≥1MB alloc logging). Unverified for PPM — see below.

ENV BLOCKER (2-run PPM verification could not complete): a peer session left
`.jjconflict` markers in 19 working-tree files (build closure incl. backend_cuda,
font_registry, font_atlas_composite, font_sffi, spl_fonts, font_renderer +
compiler expr_dispatch/backend) and repeatedly swept my .spl fixes and this doc.
After restoring the conflicted files to HEAD, the build hit a further
compiler/source incompatibility: committed `src/lib/common/encoding/sfnt_glyf.spl`
fails to parse with the current stage3 binary (`expected Comma, found Plus`).
The decode fix itself is verified GREEN (0 decode-string-bad, 0 exception frames)
from the last clean build (diag7).
