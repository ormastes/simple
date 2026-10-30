"""Host/provider shell contracts with fixture tools; no Cargo/C compiler runs."""
import hashlib
import os
from pathlib import Path
import shlex
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[3]
HELPER = ROOT / "scripts/check/lib/host-gpu-provider.shs"
WRAPPER = ROOT / "scripts/check/build-simple-web-server-native.shs"


class HostGpuProvider(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory(prefix="host-gpu-contract-")
        self.addCleanup(self.tmp.cleanup)
        self.base = Path(self.tmp.name)
        self.tools = self.base / "tools"
        self.tools.mkdir()
        self.prefix = self.base / "openssl with spaces"
        (self.prefix / "lib").mkdir(parents=True)
        (self.prefix / "include/openssl").mkdir(parents=True)
        for header in ("evp.h", "rand.h"):
            (self.prefix / "include/openssl" / header).write_text("fixture header\n")
        self.provider = self.prefix / "lib/libcrypto.3.dylib"
        self.provider.write_bytes(b"fixture provider, not executable\n")
        (self.prefix / "lib/libcrypto.dylib").symlink_to(self.provider.name)
        (self.prefix / "lib/libcrypto.so").symlink_to(self.provider.name)
        self.tool("uname", "printf '%s\\n' \"${FIXTURE_HOST:-Darwin}\"")
        self.tool("pkg-config", "exit 1")
        self.tool("brew", "exit 1")
        self.tool("cc", "echo 'unexpected compiler invocation' >&2; exit 99")
        self.tool("nm", "cat \"$FIXTURE_NM\"; exit \"${FIXTURE_NM_STATUS:-0}\"")
        self.nm_output = self.base / "nm-output"
        self.nm_output.write_text("00000000 T _rt_present\n         U _rt_missing\n         w _rt_weak_missing\n")

    def tool(self, name, body):
        path = self.tools / name
        path.write_text("#!/bin/sh\n" + body + "\n")
        path.chmod(0o700)

    def run_shell(self, code, **extra):
        env = {"PATH": str(self.tools) + os.pathsep + os.defpath,
               "FIXTURE_NM": str(self.nm_output), "HOST_CC": "cc", "HOST_NM": "nm"}
        env.update(extra)
        return subprocess.run(["sh", "-c", 'set -eu; . "$1"; host_gpu_host_init; ' + code,
                               "contract", str(HELPER)], env=env, capture_output=True,
                              text=True, timeout=10)

    def explicit(self):
        return dict(SIMPLE_WEB_CRYPTO_LIBRARY=str(self.provider),
                    SIMPLE_WEB_OPENSSL_INCLUDE_DIR=str(self.prefix / "include"))

    def test_supported_hosts_and_windows_refusal(self):
        for host in ("Darwin", "Linux"):
            self.assertEqual(self.run_shell(":", FIXTURE_HOST=host).returncode, 0)
        result = self.run_shell(":", FIXTURE_HOST="MINGW64_NT")
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("unsupported hosted web runtime host", result.stderr)

    def test_symbol_definition_and_macho_prefix(self):
        self.assertEqual(self.run_shell('host_gpu_require_symbols unused rt_present').returncode, 0)
        for symbol in ("rt_missing", "rt_weak_missing", "absent"):
            self.assertNotEqual(self.run_shell('host_gpu_require_symbols unused ' + symbol).returncode, 0)
        self.assertNotEqual(self.run_shell('host_gpu_require_symbols unused rt_present', FIXTURE_NM_STATUS="1").returncode, 0)
        self.assertNotEqual(self.run_shell('host_gpu_require_symbols unused rt_present', FIXTURE_HOST="Linux").returncode, 0)
        self.nm_output.write_text("00000000 T rt_present\n")
        self.assertEqual(self.run_shell('host_gpu_require_symbols unused rt_present', FIXTURE_HOST="Linux").returncode, 0)

    def test_explicit_provider_and_headers_are_bound(self):
        result = self.run_shell('host_gpu_resolve_crypto; printf "%s\\n%s\\n" "$CRYPTO_PROVIDER" "$CRYPTO_PROVIDER_SHA256"', **self.explicit())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.splitlines(), [str(self.provider.resolve()), hashlib.sha256(self.provider.read_bytes()).hexdigest()])
        (self.prefix / "include/openssl/evp.h").unlink()
        self.assertNotEqual(self.run_shell('host_gpu_resolve_crypto', **self.explicit()).returncode, 0)

    def test_pkg_config_and_brew_discovery(self):
        self.tool("pkg-config", 'case "$1" in --exists) exit 0;; --variable=libdir) printf "%s\\n" "$FIXTURE_PREFIX/lib";; --variable=includedir) printf "%s\\n" "$FIXTURE_PREFIX/include";; *) exit 1;; esac')
        code = 'host_gpu_resolve_crypto; printf "%s\\n" "$CRYPTO_PROVIDER"'
        result = self.run_shell(code, FIXTURE_PREFIX=str(self.prefix))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), str(self.provider.resolve()))
        self.tool("pkg-config", "exit 1")
        self.tool("brew", '[ "$1" = --prefix ] && [ "$2" = openssl@3 ] || exit 1; printf "%s\\n" "$FIXTURE_PREFIX"')
        result = self.run_shell(code, FIXTURE_PREFIX=str(self.prefix))
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), str(self.provider.resolve()))

    def test_driver_search_and_missing_provider(self):
        self.tool("cc", '[ "$#" -eq 1 ] && [ "$1" = -print-file-name=libcrypto.so ] || exit 99; printf "%s\\n" "$FIXTURE_PROVIDER"')
        result = self.run_shell('host_gpu_resolve_crypto', FIXTURE_HOST="Linux", FIXTURE_PROVIDER=str(self.provider))
        self.assertEqual(result.returncode, 0, result.stderr)
        result = self.run_shell('host_gpu_resolve_crypto', FIXTURE_HOST="Linux", FIXTURE_PROVIDER="libcrypto.so")
        self.assertNotEqual(result.returncode, 0)
        result = self.run_shell('host_gpu_resolve_crypto', SIMPLE_WEB_CRYPTO_LIBRARY="/missing/provider")
        self.assertNotEqual(result.returncode, 0)

    def test_actual_wrapper_passes_selected_library_as_provider(self):
        source = WRAPPER.read_text()
        start = source.index('WEB_LINK_OBJECTS=')
        end = source.index('. "$ROOT_DIR/scripts/lib/simple-compiler-select.shs"', start)
        recipe = source[start:end]
        code = 'host_gpu_resolve_crypto; TLS_PROVIDER_OBJECT=/fixture/tls.o; ' + recipe + '\nprintf "%s\\n" "$WEB_LINK_OBJECTS"'
        result = self.run_shell(code, **self.explicit())
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertEqual(result.stdout.strip(), "/fixture/tls.o:" + str(self.provider.resolve()))
        self.assertIn('SIMPLE_LINK_OBJECTS="$WEB_LINK_OBJECTS"', source)
        self.assertNotIn('SIMPLE_LINK_LIBRARIES=', source)

    def test_actual_wrapper_rejects_wrong_crypto_manifest(self):
        source = WRAPPER.read_text()
        start = source.index('host_gpu_resolve_crypto || exit 8')
        end = source.index('host_gpu_require_symbols "$RUNTIME_ARCHIVE"', start)
        manifest = self.base / "capsule.manifest"
        rows = ["host_os=Darwin", "host_provider_helper_sha256=" + hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                "crypto_provider=" + str(self.provider.resolve()),
                "crypto_provider_sha256=" + hashlib.sha256(self.provider.read_bytes()).hexdigest()]
        code = f'ROOT_DIR={shlex.quote(str(ROOT))}; TLS_SUPPLEMENT_MANIFEST={shlex.quote(str(manifest))}; ' + source[start:end]
        manifest.write_text("\n".join(rows) + "\n")
        self.assertEqual(self.run_shell(code, **self.explicit()).returncode, 0)
        manifest.write_text("\n".join(rows[:-1] + ["crypto_provider_sha256=" + "0" * 64]) + "\n")
        self.assertEqual(self.run_shell(code, **self.explicit()).returncode, 8)

    def test_actual_cargo_recipe_uses_vendor_cwd_and_explicit_toolchain(self):
        producer = (ROOT / "scripts/check/build-host-gpu-runtime-capsule.shs").read_text()
        start = producer.index("(\n    # Cargo discovers")
        end = producer.index("CARGO_STATUS=$?", start)
        root = self.base / "source tree"
        (root / "src/compiler_rust/.cargo").mkdir(parents=True)
        (root / "src/compiler_rust/.cargo/config.toml").write_text("# vendor fixture\n")
        self.tool("chosen-cargo", 'test -f .cargo/config.toml || exit 91; printf "%s\\n" "$PWD" "$CARGO_TARGET_DIR" "$RUSTC" "$CARGO_BUILD_JOBS" "$@"')
        log = self.base / "cargo.log"
        target = self.base / "private target"
        rustc = self.base / "chosen-rustc"
        values = dict(ROOT_DIR=root, HOST_CARGO=self.tools / "chosen-cargo",
                      CARGO_TARGET_DIR=target, CARGO_LOG=log, RUSTC=rustc,
                      CARGO_BUILD_JOBS="10")
        code = "\n".join(f"export {key}={shlex.quote(str(value))}" for key, value in values.items())
        result = self.run_shell(code + "\n" + producer[start:end])
        self.assertEqual(result.returncode, 0, result.stderr)
        rows = log.read_text().splitlines()
        self.assertEqual(rows[:4], [str(root / "src/compiler_rust"), str(target), str(rustc), "10"])
        self.assertEqual(rows[4:], ["build", "--locked", "--offline", "--manifest-path",
                                   str(root / "src/compiler_rust/Cargo.toml"), "--package",
                                   "simple-runtime", "--lib", "--profile", "bootstrap", "--features", "vulkan,cuda"])


if __name__ == "__main__":
    unittest.main()
