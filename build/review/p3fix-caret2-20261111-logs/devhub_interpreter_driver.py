"""Run the fresh secured DB fixture under the interpreter, reusing
test/fixtures/devhub/fresh_secured_db/provision.py canonical provisioning.

Only the child command line is adapted (interpreter run of the .spl fixture);
all input generation, environment binding, and post-run hash/metadata checks
are provision.py's own.
"""
import importlib.util
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[3]
SIMPLE = ROOT / "bin" / "simple.exe"
FIXTURE_MAIN = ROOT / "test" / "fixtures" / "devhub" / "fresh_secured_db" / "main.spl"
PROVISION = ROOT / "test" / "fixtures" / "devhub" / "fresh_secured_db" / "provision.py"

spec = importlib.util.spec_from_file_location("fresh_provision", PROVISION)
provision = importlib.util.module_from_spec(spec)
spec.loader.exec_module(provision)

env = dict(os.environ)
env["SIMPLE_LIB"] = str(ROOT / "src")
env["DEVHUB_FRESH_TIMEOUT_SECONDS"] = "600"

real_run = subprocess.run

def patched_run(cmd, *args, **kwargs):
    adapted = [str(SIMPLE), str(FIXTURE_MAIN), "--mode=interpreter"]
    print("DRIVER adapted command:", adapted[0], "<fixture main> --mode=interpreter")
    return real_run(adapted, *args, **kwargs)

subprocess.run = patched_run
sys.argv = ["provision.py", "--native", str(SIMPLE), "--seed-interpreter",
            "--parent", tempfile.mkdtemp(prefix="devhub-fresh-parent-")]
raise SystemExit(provision.main())
