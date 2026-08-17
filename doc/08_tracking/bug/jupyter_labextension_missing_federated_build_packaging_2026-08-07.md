# JupyterLab labextension has no installable federated-extension build pipeline

Status: OPEN (P3)
Status re-verified 2026-08-17 by source inspection (triage shard 02).

**Found:** 2026-08-07, during notebook-lanes X2 implementation (extension core + LSP
wiring), blocking galata/browser verification.

## Symptom

`tools/jupyter/labextension/` (scaffolded in X1, extended in X2) has a working
TypeScript build (`tsc -b` clean) and a passing Jest unit suite, but cannot be loaded
into a real JupyterLab instance as a federated extension:

```bash
jupyter labextension develop --overwrite .
# FileNotFoundError: The Python package '.' is not a valid package,
# it is missing the setup.py file
```

`jupyter labextension list` confirms the extension is never actually loaded by
JupyterLab. The package is missing `pyproject.toml` / `hatch-jupyter-builder` /
`@jupyterlab/builder` wiring — the standard packaging JupyterLab requires to build and
install a labextension as a federated extension.

## Impact

Any browser-driven (galata/Playwright) verification for X2, X3 (lane picker + math
outputs), and X4 (SDoctest export command) is blocked until this is closed — those
tasks' plan-specified verify step ("a `jupyter lab` smoke script using a headless
galata test") cannot run. X2 substituted unit-level plugin-registration tests (19/19
passing) as a documented fallback, per the task's host-unavailable-is-a-real-status
convention; X3/X4 will need the same workaround, or this packaging gap closed first.

Installing the missing toolchain (`hatch`, `hatch-jupyter-builder`, `@jupyterlab/
builder`) was not done unilaterally in the agent sandbox because the host's Python
environment is externally managed and installing packages requires `pip install
--break-system-packages` or a venv — a environment change out of scope for a single
task agent.

## Status

**Fixed 2026-08-08.** Standard JupyterLab 4.x federated-extension packaging added to
`tools/jupyter/labextension/` (modeled on the official extension-template, frontend-only
variant, minimal — no cookiecutter/CI/binder cruft):

- `pyproject.toml` — hatchling + `hatch-jupyter-builder` build hook (`npm_builder`,
  `build_cmd = "build:prod"`), wheel shared-data mapping to
  `share/jupyter/labextensions/@simple-lang/jupyterlab-simple`. Carries the Stream P /
  P0 sanctioned-Python-exception header (same exception as `kernel_wrapper.py`).
- `install.json` + `simple_labextension/__init__.py` (packaging glue only:
  `_jupyter_labextension_paths`, needed by `labextension develop`).
- `package.json` — added `@jupyterlab/builder ^4.0.0` devDependency and
  `build:prod` / `build:labextension[:dev]` scripts; `clean` also removes the
  federated output dir; `.gitignore` covers `simple_labextension/labextension/`.

Verified end-to-end in the host user env (jupyterlab 4.5.5 in `~/.local`, PEP 668
externally-managed → `pip3 install --user --break-system-packages`, matching how
jupyterlab itself was installed):

1. `npm run build` (tsc -b) clean; Jest 48/48 (6 suites) green.
2. `npm run build:prod` — webpack federated bundle compiled successfully into
   `simple_labextension/labextension/` (static/style.js + package.json present);
   `pip3 install --user --break-system-packages -e .` → "Successfully installed
   simple_labextension-0.1.0".
3. `jupyter labextension develop . --overwrite` then `jupyter labextension list`:
   `@simple-lang/jupyterlab-simple v0.1.0 enabled OK (python, simple_labextension)`,
   installed at `~/.local/share/jupyter/labextensions/@simple-lang/jupyterlab-simple`.
   (Develop emits a harmless `PermissionError: /usr/share/jupyter` warning while
   probing the sys-prefix location before falling back to the user dir.)

Remaining gap narrowed to: actually running the galata/browser smoke for X2/X3/X4 —
the packaging blocker itself is closed.

## Content re-verification 2026-08-17 (app-rest lane) — CLOSE candidate

Classified by CONTENT only (no SHA/ancestry reasoning). The packaging pipeline
this record says is missing now exists in-tree:
`tools/jupyter/labextension/pyproject.toml`, `tools/jupyter/labextension/install.json`,
and `tools/jupyter/labextension/simple_labextension` are all present, which
matches this doc's own "Fixed 2026-08-08" line. The source file this row was
filed against, `src/app/jupyter_kernel/main.spl`, is unrelated to federated
extension packaging and needs no change. **Recommend CLOSED.**
Not proven: that the extension actually builds/installs — no `jupyter
labextension build` was run (host at load 346, bootstrap live).
