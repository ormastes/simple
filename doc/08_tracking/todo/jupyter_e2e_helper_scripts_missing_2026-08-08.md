# Jupyter E2E helper scripts referenced but never built

`doc/07_guide/app/tools/jupyter.md` documents two local E2E test helpers,
`test/03_system/tools/jupyter/helpers/run_server_check.py` (full server E2E
over HTTP + ZMQ) and `run_notebook_server_test.py` (notebook execution via
nbconvert). Neither exists; the only helper actually present is
`wrapper_transport_roundtrip.py`. Worse, this isn't just a doc-staleness
issue: the system spec `test/03_system/tools/jupyter/
jupyter_notebook_server_system_spec.spl` itself calls these two scripts by
name via `rt_process_run("python3", [helper, ...])`, but at the even-older
path `test/system/jupyter/helpers/...` (missing the `03_` and `tools/`
segments), so those spec scenarios can never have found the helper even if
it existed.

# TODO: [test][P2] Build (or restore) the Jupyter full-server and notebook-exec E2E helpers
Implement `run_server_check.py` (starts a real `jupyter notebook`/kernel
server and exercises it over HTTP + ZMQ) and `run_notebook_server_test.py`
(runs a `.ipynb` fixture through `nbconvert --execute` and checks outputs),
under `test/03_system/tools/jupyter/helpers/`, and fix the stale
`test/system/jupyter/helpers/...` path used in
`jupyter_notebook_server_system_spec.spl` to point at the real
`test/03_system/tools/jupyter/helpers/...` location. Until then, those spec
scenarios do not exercise real server/notebook-execution behavior.
