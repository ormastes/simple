#!/usr/bin/env python3
"""Exercise the WM gate's real ELF-to-Image and ESP handoff shell fragments.

The ESP boundary captures its input; it does not construct FAT media, launch
QEMU, or qualify firmware/GPU execution.
"""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

root = Path(__file__).resolve().parents[2]
source = (root / "scripts/check/check-simpleos-arm64-wm-vulkan-pixel-evidence.shs").read_text()
conversion = source[source.index('KERNEL_IMAGE_ABS=$(abspath'):source.index('# ---------------------------------------- build the host GPU')]
handoff_start = source.index('set +e\nenv KERNEL_ELF="$KERNEL_IMAGE_ABS"')
handoff = source[handoff_start:source.index('\nAAVMF_VARS_RUN=', handoff_start)]
compiler = shutil.which("clang")
linker = shutil.which("ld.lld")
assert compiler and linker, "clang and ld.lld are required for real ELF fixtures"

with tempfile.TemporaryDirectory(prefix="arm64 wm 'image ") as temp:
    fixture = Path(temp)
    build = fixture / "build space"
    evidence = build / "evidence"
    esp = build / "esp"
    evidence.mkdir(parents=True)
    esp.mkdir()
    builder = fixture / "scripts/os/build-simpleos-aarch64-efi-esp.shs"
    builder.parent.mkdir(parents=True)
    builder.write_text('''#!/bin/sh
set -eu
test "$BOOT_PROTOCOL" = linux
test "$KERNEL_ELF" = "$EXPECTED_IMAGE"
printf called > "$FIXTURE/called"
if [ "${FIXTURE_ESP_FAIL:-0}" = 1 ]; then exit 17; fi
cp "$KERNEL_ELF" "$FIXTURE/esp-input"
printf image > "$OUT_DIR/esp.img"
''')
    raw_copy = fixture / "raw-copy"
    raw_copy.write_text('#!/bin/sh\ncp "$3" "$4"\n')
    raw_copy.chmod(0o755)

    def make_elf(name, magic="ARMd", size=1088, target="aarch64-none-elf", truncated=False):
        assembly = fixture / (name + ".S")
        body = '.byte 0\n' if truncated else f'.long 0,0\n.quad 0,{size}\n.zero 32\n.ascii "{magic}"\n.long 0\n.zero 1024\n'
        assembly.write_text('.section .text\n.global _start\n_start:\n' + body)
        obj = fixture / (name + ".o")
        elf = fixture / (name + ".elf")
        subprocess.run([compiler, "--target=" + target, "-c", str(assembly), "-o", str(obj)], check=True)
        subprocess.run([linker, "-Ttext=0x40000000", str(obj), "-o", str(elf)], check=True)
        return elf

    setup = '''
set -eu
abspath() { printf '%s\\n' "$1"; }
error_verdict() { printf 'ERROR: %s\\n' "$1"; exit 2; }
'''

    def run(elf, **extra):
        (fixture / "called").unlink(missing_ok=True)
        env = dict(os.environ, ROOT_DIR=temp, FIXTURE=temp, BUILD_DIR=str(build),
                   EVIDENCE_DIR=str(evidence), ESP_DIR_ABS=str(esp), ESP_IMG=str(esp / "esp.img"),
                   KERNEL_ELF_ABS=str(elf), AAVMF_CODE="fixture-firmware",
                   EXPECTED_IMAGE=str(build / "kernel.Image"))
        env.update(extra)
        return subprocess.run(["sh", "-c", setup + conversion + handoff], env=env, capture_output=True)

    good = make_elf("valid")
    result = run(good)
    assert result.returncode == 0, (result.stdout, result.stderr)
    payload = (fixture / "esp-input").read_bytes()
    assert payload == (build / "kernel.Image").read_bytes()
    assert len(payload) == 1088 and payload[56:60] == b"ARMd" and payload[:4] != b"\x7fELF"
    assert good.read_bytes()[:4] == b"\x7fELF"

    for name, options in (("bad-magic", {"magic": "xxxx"}), ("zero-size", {"size": 0}),
                          ("short-image", {"truncated": True}),
                          ("wrong-machine", {"target": "x86_64-none-elf"})):
        result = run(make_elf(name, **options))
        assert result.returncode == 2 and b"header invalid" in result.stdout, (name, result.stdout, result.stderr)
        assert not (fixture / "called").exists(), name + " reached ESP builder"
    result = run(good, LLVM_OBJCOPY=str(raw_copy))
    assert result.returncode == 2 and not (fixture / "called").exists()
    result = run(good, LLVM_OBJCOPY="/missing/objcopy")
    assert result.returncode == 2 and b"llvm-objcopy missing" in result.stdout
    alias = build / "kernel.Image"
    original = good.read_bytes()
    alias.write_bytes(original)
    result = run(alias)
    assert result.returncode == 2 and b"output aliases kernel input" in result.stdout
    assert alias.read_bytes() == original and not (fixture / "called").exists()
    result = run(good, FIXTURE_ESP_FAIL="1")
    assert result.returncode == 2 and b"ESP build failed (rc=17" in result.stdout

print("PASS: real ARM64 ELF becomes flat Image at ESP boundary; quoted paths, malformed headers, wrong machine, raw ELF, missing tool and builder failure refused")
print("Firmware/GPU admission: NOT RUN")
