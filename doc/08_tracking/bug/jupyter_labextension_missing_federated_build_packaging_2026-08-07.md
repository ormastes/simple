# JupyterLab labextension has no installable federated-extension build pipeline

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

Open. Recommend: add `pyproject.toml` + `hatch-jupyter-builder` config to
`tools/jupyter/labextension/` (standard JupyterLab 4.x extension packaging) in a
dedicated task before X3/X4's galata verification is attempted, or set up an isolated
venv for the labextension build/test toolchain.
