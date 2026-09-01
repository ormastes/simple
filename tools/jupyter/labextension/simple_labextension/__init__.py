# Sanctioned Python-ecosystem exception (see doc/03_plan/agent_tasks/
# notebook_lanes_parallel_plan_2026-08-07.md, Stream P / P0, and the header of
# pyproject.toml): JupyterLab's `labextension develop` imports this module to
# locate the prebuilt federated bundle. Packaging glue only — no logic.
__version__ = "0.1.0"


def _jupyter_labextension_paths():
    return [{"src": "labextension", "dest": "@simple-lang/jupyterlab-simple"}]
