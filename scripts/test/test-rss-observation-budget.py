#!/usr/bin/env python3
"""Exercise the watchdog's exact platform/override budget policy."""
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[2]
source = (root / "scripts/resource/process-tree-rss-watchdog.pl").read_text()
start = source.index("sub resolve_observation_budget_ms {")
end = source.index("my ($sample_duration_max_ms", start)
# Keep the production call and validation. Substitute only the OS input so
# FreeBSD and other platform paths can be tested without starting a workload.
policy = source[start:end].replace("$^O", "$ARGV[0]")
program = "use strict; use warnings;\n" + policy + '\nprint "$observation_budget_ms\\n";'


def resolve(platform, override=None):
    env = {"PATH": "/usr/bin:/bin"}
    if override is not None:
        env["SIMPLE_PROCESS_TREE_OBSERVATION_BUDGET_MS"] = override
    return subprocess.run(["perl", "-e", program, platform], env=env,
                          capture_output=True, check=False)


for platform in ("freebsd", "linux", "darwin", "msys", "cygwin", "MSWin32"):
    result = resolve(platform)
    assert result.returncode == 0, result.stderr
    assert int(result.stdout) == (5000 if platform == "freebsd" else 1000)
    for explicit in ("1000", "5000", "30000"):
        result = resolve(platform, explicit)
        assert result.returncode == 0 and int(result.stdout) == int(explicit)
    for invalid in ("", "0", "999", "30001", "-1000", "auto", "1.5", "5000ms"):
        result = resolve(platform, invalid)
        assert result.returncode != 0, (platform, invalid)
        assert b"observation budget must be between 1000 and 30000" in result.stderr

print("PASS: FreeBSD default 5000 ms, other defaults 1000 ms, explicit bounds preserved, invalid values refused")
