#!/usr/bin/env python3
import os

out_path = os.environ.get("RDOC_QRENDERDOC_SMOKE_OUT", "build/renderdoc/qrenderdoc-python-smoke.env")
os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
with open(out_path, "w", encoding="utf-8") as f:
    f.write("rdoc_qrenderdoc_python_smoke_status=pass\n")
os._exit(0)
