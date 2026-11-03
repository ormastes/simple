#!/usr/bin/env python3
"""Exercise the production firmware preparation and QEMU argv without booting."""
from pathlib import Path
import os
import subprocess
import shutil
import struct
import tempfile

root = Path(__file__).resolve().parents[2]
source = (root / "scripts/check/check-simpleos-arm64-unified-live.shs").read_text()
prepare = source[source.index('objcopy=${LLVM_OBJCOPY:-llvm-objcopy}'):source.index('\nrm -f "$serial"')]
argv = source[source.index('set -- -no-user-config'):source.index('\nqemu_args=')]
guard = source[source.index('test "$firmware_hashes" ='):source.index('\nqemu-system-aarch64 "$@"')]

with tempfile.TemporaryDirectory(prefix="arm64 firmware '") as temp:
    fixture = Path(temp)
    compiler = os.environ.get("CLANG", shutil.which("clang"))
    linker = os.environ.get("LLD", shutil.which("ld.lld"))
    assert compiler and linker, "clang and ld.lld required for actual ELF fixture"
    assembly = fixture / "header.S"
    assembly.write_text('.section .text\n.global _start\n_start:\n.long 0,0\n.quad 0,64\n.zero 32\n.ascii "ARMd"\n.long 0\n')
    subprocess.run([compiler, "--target=aarch64-none-elf", "-c", str(assembly), "-o", str(fixture / "header.o")], check=True)
    subprocess.run([linker, "-Ttext=0x40000000", str(fixture / "header.o"), "-o", str(fixture / "kernel file.elf")], check=True)
    assert (fixture / "kernel file.elf").read_bytes()[:4] == b"\x7fELF"
    env = dict(os.environ, fixture=temp)
    setup = '''
set -eu
esp_dir="$fixture/efi media"
esp_log="$fixture/build.log"
kernel="$fixture/kernel file.elf"
kernel_image="$fixture/kernel flat.Image"
serial="$fixture/serial"
font_disk="$fixture/fonts.img"
shm="$fixture/shared memory"
qmp="$fixture/qmp.sock"
fail() { echo "$1" >&2; exit 23; }
sh() {
    test "$BOOT_PROTOCOL" = linux
    test "$KERNEL_ELF" = "$kernel_image"
    test "$(od -An -tx1 -j56 -N4 "$KERNEL_ELF" | tr -d ' \n')" = 41524d64
    test "$(wc -c < "$KERNEL_ELF")" -eq 64
    test "$OUT_DIR" = "$esp_dir"
    test "$1" = scripts/os/build-simpleos-aarch64-efi-esp.shs
    mkdir -p "$OUT_DIR"
    printf fresh > "$OUT_DIR/esp.img"
    printf firmware > "$OUT_DIR/AAVMF_CODE.fd"
    printf nvram > "$OUT_DIR/AAVMF_VARS.fd"
}
'''
    def run(body):
        return subprocess.run(["sh", "-c", setup + body], env=env, capture_output=True)

    result = run(prepare + '\n' + guard + '\n' + argv + '\nprintf "%s\\0" "$@"')
    assert result.returncode == 0, result.stderr
    flat = (fixture / 'kernel flat.Image').read_bytes()
    assert flat[56:60] == b'ARMd' and struct.unpack_from('<Q', flat, 16)[0] == 64
    args = result.stdout.decode().split('\0')[:-1]
    assert '-kernel' not in args and '-bios' not in args
    drives = [args[i + 1] for i, arg in enumerate(args) if arg == '-drive']
    assert f'if=pflash,format=raw,readonly=on,file={temp}/efi media/AAVMF_CODE.fd' in drives
    assert f'if=pflash,format=raw,file={temp}/efi media/AAVMF_VARS.fd' in drives
    assert f'if=none,file={temp}/efi media/esp.img,format=raw,id=esp' in drives
    assert 'virtio-blk-pci,drive=esp,bootindex=0' in args
    assert 'virtio-blk-device,drive=fontdisk' in args
    assert 'virtio-keyboard-device' in args and 'virtio-mouse-device' in args
    assert 'virtio-sound-device,audiodev=audio0' in args

    result = run('sh() { return 9; }\n' + prepare)
    assert result.returncode == 23 and b'real-firmware-image-build-failed' in result.stderr
    result = run('sh() { rm -rf "$OUT_DIR"; mkdir -p "$OUT_DIR"; }\n' + prepare)
    assert result.returncode == 23 and b'real-firmware-input-missing' in result.stderr
    result = run(prepare + '\nprintf changed > "$esp_dir/esp.img"\n' + guard)
    assert result.returncode == 23 and b'prelaunch-real-firmware-mutated' in result.stderr

    result = run('LLVM_OBJCOPY=raw_copy\nraw_copy() { cp \"$3\" \"$4\"; }\n' + prepare)
    assert result.returncode == 23 and b'flat-image-header-invalid' in result.stderr

print('PASS: real ELF-to-Image extraction, raw ELF rejection, production firmware argv, quoted paths, builder failure, missing inputs, prelaunch mutation')
print('Native firmware boot and physical-board qualification: NOT RUN')
