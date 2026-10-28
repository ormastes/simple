"""Build the real mail SDN bridge with a pinned, already-built Phase-2 producer.

MAIL_CI_PHASE2_PRODUCERS_JSON maps host triples to immutable producer bundles.
No compiler is rebuilt and no seed/interpreter/parser substitute is admitted.
"""
from __future__ import annotations

import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import urllib.request
import zipfile


def refuse(message: str) -> None:
    raise SystemExit("MAIL_CI_PHASE2_UNAVAILABLE: " + message)


def sha256_file(path: Path) -> str:
    with path.open("rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def contained(root: Path, relative: str) -> Path:
    target = (root / relative).resolve()
    if not target.is_relative_to(root.resolve()):
        refuse("producer bundle path escapes its staging directory")
    return target


def provision(entry: dict, destination: Path) -> Path:
    if entry.get("phase") != 2:
        refuse("the pinned producer must declare phase 2")
    digest = entry.get("sha256", "")
    if not re.fullmatch(r"[0-9a-f]{64}", digest):
        refuse("a pinned producer bundle SHA-256 is required")
    url = entry.get("url", "")
    if not isinstance(url, str) or not url.startswith("https://"):
        refuse("the existing producer bundle requires an HTTPS URL")
    archive = destination / "producer.download"
    request = urllib.request.Request(url, headers={"User-Agent": "simple-mail-ci"})
    with urllib.request.urlopen(request, timeout=120) as response, archive.open("wb") as output:
        shutil.copyfileobj(response, output)
    if sha256_file(archive) != digest:
        refuse("the downloaded producer bundle checksum does not match")
    bundle = destination / "producer"
    bundle.mkdir()
    kind = entry.get("format", "file")
    executable = entry.get("compiler", "simple.exe" if os.name == "nt" else "simple")
    compiler = contained(bundle, executable)
    if kind == "file":
        compiler.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(archive, compiler)
    elif kind == "tar.gz":
        with tarfile.open(archive, "r:gz") as source:
            source.extractall(bundle, filter="data")
    elif kind == "zip":
        with zipfile.ZipFile(archive) as source:
            for member in source.infolist():
                contained(bundle, member.filename)
                if (member.external_attr >> 16) & 0o170000 == 0o120000:
                    refuse("producer ZIP contains a symbolic link")
            source.extractall(bundle)
    else:
        refuse("producer format must be file, tar.gz, or zip")
    if not compiler.is_file():
        refuse("the pinned bundle does not contain its declared compiler")
    compiler.chmod(compiler.stat().st_mode | 0o700)
    asset_root = contained(bundle, entry.get("asset_root", "."))
    os.environ["SIMPLE_ASSET_ROOT"] = str(asset_root)
    os.environ["PATH"] = os.pathsep.join([str(asset_root / "bin"), str(asset_root / "lib"), os.environ["PATH"]])
    return compiler


def main() -> None:
    machine = platform.machine().lower()
    machine = {"amd64": "x86_64", "aarch64": "arm64"}.get(machine, machine)
    system = {"Windows": "windows", "Darwin": "darwin", "Linux": "linux"}.get(platform.system())
    host = f"{system}-{machine}"
    try:
        profiles = json.loads(os.environ.get("MAIL_CI_PHASE2_PRODUCERS_JSON", "{}"))
    except json.JSONDecodeError:
        refuse("MAIL_CI_PHASE2_PRODUCERS_JSON is not valid JSON")
    entry = profiles.get(host) if isinstance(profiles, dict) else None
    if not isinstance(entry, dict):
        refuse(f"no existing producer is configured for {host}; set MAIL_CI_PHASE2_PRODUCERS_JSON with url, sha256, phase=2, format and compiler")
    checkout = Path.cwd().resolve()
    destination = Path(os.environ.get("RUNNER_TEMP", str(checkout / "build"))) / "mail-config-helper"
    destination.mkdir(parents=True, exist_ok=False)
    compiler = provision(entry, destination)
    producer_digest = sha256_file(compiler)
    helper = destination / ("simple-mail-credentials.exe" if os.name == "nt" else "simple-mail-credentials")
    environment = dict(os.environ, SIMPLE_NO_STUB_FALLBACK="1", SIMPLE_NO_BOOTSTRAP_DELEGATE="1", SIMPLE_NATIVE_BUILD_THREADS="2")
    arguments = [str(compiler), "native-build", "src/app/mail_credentials/main.spl"]
    roots = ["src/app", "src/lib", "src/os", "src/compiler"]
    if os.name == "nt":
        roots.insert(0, "src/providers/windows_native/lib")
    for root in roots:
        arguments.extend(["--source", root])
    arguments.extend(["--backend=llvm", "-o", str(helper)])
    with (destination / "helper-build.log").open("wb") as log:
        result = subprocess.run(arguments, cwd=checkout, env=environment, stdout=log, stderr=subprocess.STDOUT, timeout=1200)
    if result.returncode != 0 or not helper.is_file():
        refuse(f"the existing producer could not build the real helper; see {destination / 'helper-build.log'}")
    # Exercise the compiled production parser before exporting it to fixtures.
    document = destination / "probe.sdn"
    document.write_text('default_account: "ci"\naccounts:\n  ci:\n    protocol: pop3\n    provider: other\n    email: "ci@example.test"\n    pop3_server: "127.0.0.1"\n    tls: implicit\n', encoding="utf-8")
    parsed = subprocess.run([str(helper), "config-json", str(document)], capture_output=True, text=True, timeout=20, env=environment)
    try:
        actual = json.loads(parsed.stdout)
    except json.JSONDecodeError:
        refuse("the compiled helper returned invalid JSON for the SDN control")
    if parsed.returncode != 0 or actual.get("accounts", {}).get("ci", {}).get("protocol") != "pop3":
        refuse("the compiled helper did not pass the actual SDN parser control")
    document.write_text('accounts: [\n', encoding="utf-8")
    rejected = subprocess.run([str(helper), "config-json", str(document)], capture_output=True, text=True, timeout=20, env=environment)
    if rejected.returncode == 0 or rejected.stdout.strip():
        refuse("the compiled helper accepted malformed SDN")
    helper_digest = sha256_file(helper)
    (destination / "evidence.json").write_text(json.dumps({"platform": host, "producer_sha256": producer_digest, "helper_sha256": helper_digest, "compiler_rebuilt": False, "actual_parser_controls": 2}, indent=2) + "\n")
    with Path(os.environ["GITHUB_ENV"]).open("a", encoding="utf-8") as output:
        output.write(f"MAIL_CONFIG_BIN={helper.as_posix()}\n")
    print(f"Prepared real mail SDN helper for {host}; producer={producer_digest}; helper={helper_digest}")


if __name__ == "__main__":
    main()
