# `renderdoc-export-events.shs` dispatched a `renderdoccmd` subcommand that does not exist (2026-09-12)

**Status:** fixed in PR #644. Filed because the defect was latent and silent,
and because the same shape (a tool wrapper calling a subcommand nobody ever
ran) can recur.

## Defect

`scripts/tool/renderdoc-export-events.shs` picked its replay host like this:

```sh
case "$RENDERDOCCMD" in
    *qrenderdoc*) set -- "$RENDERDOCCMD" --python "$EXPORTER" ;;
    *)            set -- "$RENDERDOCCMD" python "$EXPORTER" ;;
esac
```

**`renderdoccmd` has no `python` command.** Checked against the RenderDoc
v1.44 source the repo's own builder pins (`RENDERDOC_REF=v1.44`), not assumed —
`renderdoccmd/renderdoccmd.cpp` registers exactly:

```
vulkanlayer  version  help  capture  inject  thumb  remoteserver
replay  capaltbit  test  convert  embed  extract
```

The `#if PYTHON_AVAILABLE == 1` guards in that same file gate the `test`
command's `functional` mode. They do not gate a `python` command, and there is
no `"python"` string in the command table at all.

So the fallback branch could never have worked. Every export on a host without
`qrenderdoc` reported `renderdoc_status=blocked:export-failed`.

## Why it stayed invisible

The lane that consumes this exporter had never reached it. RenderDoc itself was
never provisioned — see
`doc/10_metrics/ui/renderdoc_first_captures_2026-09-12.md` for that separate
pair of defects — so the exporter was never called with a real capture on CI,
and the `qrenderdoc` branch is the one a developer with a desktop RenderDoc
install happens to take. A wrapper whose only exercised path is the one that
works will not report that its other path is fiction.

Note the interaction that made this worth catching *before* the first green
run: the provisioning fix was about to give the lane a working `renderdoccmd`
for the first time. The lane would then have produced two valid `.rdc` files
and reported `renderdoc_diff_status=blocked` — and the obvious reading of that
(“the Python bindings failed to build”) would have been wrong, sending the next
investigation at swig instead of at a call that was never real.

## Fix

The supported headless path is the pyrenderdoc swig module
(`qrenderdoc/Code/pyrenderdoc`, building `_renderdoc` plus a generated
`renderdoc.py`), gated by `ENABLE_PYRENDERDOC`. Two gaps had to close together:

1. `scripts/setup/build-renderdoc-linux-vulkan-only.shs` hardcoded
   `-DENABLE_PYRENDERDOC=OFF`, so the module was never built.
   `RENDERDOC_ENABLE_PYTHON=1` now requests it, falling back to a
   bindings-less build if that configure fails (the bindings drag in a swig
   build, and an exporter-only capability must not cost the captures). The
   resolved mode is recorded as `renderdoc_vulkan_only_python_bindings=on|off`
   so a fallback is visible rather than silent.
2. The module has **no `install()` rule** — it is left in the build tree,
   outside the install prefix and outside the CI cache. `install_tree` now
   stages it into `$RDOC_HOME/pymodules`.

The exporter then puts that directory on `PYTHONPATH` and runs the script under
the system `python3`. The script was already compatible: it does a plain
`import renderdoc as rd` (never `qrenderdoc`, whose `_qrenderdoc.so` is not
staged) and reads `RDOC_EXPORT_RDC` / `RDOC_EXPORT_OUT` / `RDOC_EXPORT_THUMBS`
from the environment rather than from a host-supplied argv.

Fails closed: a missing module reports
`renderdoc_status=blocked:pyrenderdoc-module-missing` and names the rebuild
command, instead of invoking something that cannot work. The module directory
resolves from `RDOC_PYMODULE_DIR`, then `RENDERDOC_HOME`, then the prefix
derived from the `renderdoccmd` path — `RENDERDOC_HOME` is empty when
`renderdoccmd` was found on `PATH`.

## Not yet verified

The fix has **no local test coverage** on macOS: `check-renderdoc-web-diff.shs
--selftest` correctly ERRORs `no-simple-binary` there. Its first real execution
is CI run `34692788301`. Until that run reports a
`renderdoc_diff_status` other than `blocked`, treat the fix as reasoned from
source rather than demonstrated.
