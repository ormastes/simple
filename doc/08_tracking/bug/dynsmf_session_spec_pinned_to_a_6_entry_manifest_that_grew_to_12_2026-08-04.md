# `dynsmf_session_unload_reload_spec` pins a 6-entry manifest that the product grew to 12 — red since the 2026-07-17 toolchain additions (2026-08-04)

Status: RESOLVED (2026-11-25) — see verification note at bottom.
Status re-verified 2026-08-17 by source inspection (triage shard 01).
`SIMPLE_TIMEOUT_SECONDS=190 bin/simple test
test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl
--no-cover-check` → `Results: 4 total, 0 passed, 4 failed`, same 4 examples,
same causes as originally recorded. Fix requires a requirements decision
(whether `ui_html` belongs in startup autoload) plus a `build/dynsmf/*.smf`
build step — both out of scope for this session.
**Found:** 2026-08-04
**Class:** spec/product drift + missing build prerequisite. 4 of 4 examples in
`test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl` fail.

## Symptom

```
$ SIMPLE_TIMEOUT_SECONDS=0 bin/simple test \
    test/03_system/stdlib/dynload/dynsmf_session_unload_reload_spec.spl --no-cover-check
  ✗ autoloads the six selected stdlib-like precompiled SMF libraries by default
    semantic: array index out of bounds: index is 0 but length is 0
  ✗ honors per-library dynSMF disable policy while loading other defaults
    expected 5 to equal 4
  ✗ unloads records stale symbol evidence and reloads with a newer generation
    expected symbol to equal reload
  ✗ unloads and reloads every selected default dynSMF library
    expected 1 to be greater than 1
Results: 4 total, 0 passed, 4 failed
```

## Root cause (what is PROVEN)

Two independent causes; neither is a defect in the policy/session logic, which a
direct probe shows is **correct**:

```
$ cat p1.spl        # calls the same public API the spec calls
val p = dynsmf_policy_from_args_env(["--disable-dynsmf=web_renderer,tui_renderer"], "", "")
...
source=arg:--disable-dynsmf disabled_all=false n=2
  id[0]='web_renderer'
  id[1]='tui_renderer'
disabled(web_renderer)=true
disabled(tui_renderer)=true
loaded=5 evidence=7
  ev[0] file_io      load
  ev[1] net_io       load
  ev[2] render2d     load
  ev[3] web_renderer skip     <-- exactly what the spec asserts
  ev[4] gui_renderer load
  ev[5] tui_renderer skip     <-- exactly what the spec asserts
  ev[6] ui_html      load     <-- the 7th autoload entry the spec does not know about
```

**Cause 1 — the manifest grew, the spec did not.**
`src/os/smf/dynsmf_session.spl:69 dynsmf_default_manifest()` now returns **12**
entries: 7 with `default_autoload: true` (`file_io`, `net_io`, `render2d`,
`web_renderer`, `gui_renderer`, `tui_renderer`, **`ui_html`** at `:77`) and 5
on-demand toolchain entries added by the 2026-07-17 qualification audit
(`:78-88`, `mcp_diag_tools`, `fmt_tool`, `lint_tool`, `fix_tool`, `todo_scan`,
all `default_autoload: false`).

The spec was written against the original six and hard-pins the count:
- `:47 expect(manifest.len()).to_equal(6)` — actual 12.
- `:61 expect(session.loaded.len()).to_equal(4)` — 7 autoload minus 2 disabled
  is **5**, hence `expected 5 to equal 4`.
- `:76-78` index `evidence[7]`/`evidence[8]` by absolute position, which the
  extra `ui_html` row shifts — hence `expected symbol to equal reload`.
- `:88` iterates a hardcoded 6-id list, so the 7th library's generation is never
  bumped — hence `expected 1 to be greater than 1`.

The requirements do **not** cap the manifest at six.
`doc/02_requirements/feature/low_dependency_ui_dynsmf.md:44` (REQ-004) says the
manifest "must **include** stable ids for `file_io`, `net_io`, `render2d`,
`web_renderer`, `gui_renderer`, and `tui_renderer`" — an inclusion floor, not an
exact count. So the product growth is legitimate and the spec's equality
assertions are the stale side.

**Cause 2 — the checked path needs build artifacts that do not exist here.**
`build/dynsmf/` is absent in this tree. Examples 1 and 4 call
`dynsmf_session_autoload_checked` (`:522`), which routes through
`dynsmf_session_load_impl(..., require_artifact: true)` (`:486-489`) and fails
every load with `artifact_*`. `session.loaded` is then empty, so `:50
session.loaded[0].id` raises `array index out of bounds: index is 0 but length
is 0`. This is a missing build prerequisite, not a logic defect — the spec has
no guard that turns it into a readable skip/diagnostic.

## Why not fixed now

Cause 1's fix is a spec edit, and the correct edit is not mechanical: the spec's
whole narrative ("the **six** selected stdlib-like precompiled SMF libraries",
its absolute `evidence[N]` indices, its hardcoded id list) has to be re-derived
from whatever the intended autoload set now is. Deciding whether `ui_html`
(`:77`, source `src/lib/common/ui/html_ui/dynsmf_entry.spl`) genuinely belongs
in the **startup autoload** set or should be `default_autoload: false` like the
other five later additions is a requirements question for the
`low_dependency_ui_dynsmf` owner — and it sits in the HTML/UI area this lane was
scoped away from. Rewriting the assertions to whatever the code happens to do
today would convert a real drift signal into a rubber stamp.

Cause 2 needs `build/dynsmf/*.smf` produced (the plans are already emitted by
`dynsmf_build_plans`, `:144`), i.e. a build step, plus a decision on whether the
spec should hard-fail or report a missing-artifact precondition.

## Verification note (2026-11-25)

STALE — fixed on release/1.0.0 before this verification.

- **Cause 1 (spec pinned to 6)** — fixed by spec rewrite. Commits
  `e0057bbe194` ("derive lifecycle coverage from explicit startup
  selections"), `245295340b6` ("exercise real admitted fixtures across
  manifest exports"), and `51937f7cd58` replaced every hard-pinned count:
  the spec now asserts `manifest.len()).to_be_greater_than(0)`, derives
  loaded/evidence counts from `manifest.len()`, and uses a copied
  `startup_manifest()` instead of absolute `evidence[N]` indices and a
  hardcoded 6-id list. The requirements question (does `ui_html` belong in
  startup autoload) was decided by `fef46c5dd3c`: production bundles are
  demand-loaded — every `dynsmf_default_manifest()` entry in
  `src/os/smf/dynsmf_session.spl:105-128` is now `default_autoload: false`,
  and the spec's first example asserts exactly that fail-closed policy.
- **Cause 2 (missing `build/dynsmf/*.smf`)** — fixed by the same rewrite:
  positive lifecycle cases now build host-target fixtures through the
  admitted-byte API (`test.helpers.dynsmf_admitted_startup_fixture`,
  `dynsmf_session_load_admitted`), so the spec no longer depends on a
  `build/dynsmf/*.smf` build step; compatibility autoload fails closed and
  the spec asserts `status == "failed"`, `reason` starts with `artifact_`
  instead of indexing an empty `loaded` array.

Limit: a live spec run on this host is blocked by the known release/1.0.0
source/binary inconsistency — the pinned Rust seed rejects
`@representation_boundary` (added by cfd89933699) while parsing
`src/app/test_runner_new/test_runner_client.spl`, so `bin/simple.exe test`
errors out repo-wide at HEAD. Verified by source inspection of the current
spec and manifest as cited above.
