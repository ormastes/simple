#!/usr/bin/env python3
"""Bounded, compiler-qualified Hello linkage evidence; never bootstrap admission.

The Linux adapter uses genuine LLD reproduction inputs, including the compiler's
hosted entry shim. It substitutes the explicitly emitted main/provider bytes at
the final link boundary. Darwin captures the real pinned clang driver argv and preserves hosted inputs.
"""
import argparse
import concurrent.futures
import hashlib
import importlib.util
import os
from pathlib import Path
import shlex
import shutil
import signal
import subprocess
import sys
import tarfile
import threading
import time


FIXTURES = Path("test/fixtures/bootstrap/hello_sanity_matrix")
EXPECTED = b"Hello, World!\n"
LANES = ("one-source", "two-objects", "static-library", "shared-library")


class CleanupPending(RuntimeError):
    """The retained finite watchdog still owns a nonquiescent process tree."""


def digest(path):
    with Path(path).open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def sdn(path, values):
    """Write inert SDN, never source evidence as executable shell code."""
    lines = []
    for key, value in values.items():
        if isinstance(value, bool):
            text = "true" if value else "false"
        elif isinstance(value, (int, float)):
            text = str(value)
        else:
            text = '"' + str(value).replace("\\", "\\\\").replace('"', '\\"').replace("\n", "\\n") + '"'
        lines.append(f"{key}: {text}\n")
    tmp = path.with_suffix(path.suffix + ".tmp")
    tmp.write_text("".join(lines))
    tmp.replace(path)


def response_tokens(text, windows=False):
    if windows:
        import ctypes
        count = ctypes.c_int()
        api = ctypes.windll.shell32.CommandLineToArgvW
        api.argtypes = [ctypes.c_wchar_p, ctypes.POINTER(ctypes.c_int)]
        api.restype = ctypes.POINTER(ctypes.c_wchar_p)
        pointer = api("linker " + text, ctypes.byref(count))
        if not pointer:
            raise ValueError("invalid Windows linker response")
        try:
            values = [pointer[index] for index in range(1, count.value)]
        finally:
            ctypes.windll.kernel32.LocalFree(pointer)
    else:
        values = shlex.split(text)
    if not values or any(x.startswith("@") for x in values):
        raise ValueError("empty/nested linker response is unsupported")
    return values


def replace_inputs(tokens, root, main_object, provider):
    """Identify actual consumed files by bytes, then pass explicit artifacts."""
    wanted = {digest(main_object): main_object, digest(provider): provider}
    if len(wanted) != 2:
        raise ValueError("main/provider identity collision")
    found = set()
    result = []
    chroot = "--chroot" in tokens or "--chroot=." in tokens
    for token in tokens:
        path = root / token
        if not token.startswith("-") and path.is_file():
            sha = digest(path)
            if sha in wanted:
                if sha in found:
                    raise ValueError("ambiguous duplicate captured main/provider input")
                # LLD's reproduction chroot also rewrites absolute arguments.
                # Deliberate relative paths select the exact external emitted
                # artifacts while CRT/runtime paths remain in the archive.
                result.append(os.path.relpath(wanted[sha], root) if chroot else str(wanted[sha]))
                found.add(sha)
                continue
        result.append(token)
    if found != set(wanted):
        raise ValueError("captured link did not consume exact emitted main and provider bytes")
    return result


def verify_capture_receipt(capture, output, linker):
    lines = Path(str(capture) + ".receipt").read_text().splitlines()
    if not lines or lines[0] != "simple-native-link-reproduce-v1":
        raise ValueError("invalid native link reproduction receipt")
    fields = {}
    for line in lines[1:]:
        key, value = line.split("=", 1)
        if key in fields:
            raise ValueError("duplicate reproduction receipt key")
        fields[key] = value
    if fields != {"archive_sha256": digest(capture), "output_sha256": digest(output),
                  "linker_sha256": digest(linker)}:
        raise ValueError("native reproduction archive/output/linker identity mismatch")


def phase_capabilities(phase):
    """Required cases by compiler generation; skips are not passes."""
    return {1: (True, False), 2: (False, True), 3: (True, True)}[phase]


def interpreter_invocation(phase, compiler):
    fixture = str(FIXTURES / "single.spl")
    if phase == 1:
        return [compiler, "run", fixture], {"SIMPLE_EXECUTION_MODE": "interpret", "SIMPLE_NO_BOOTSTRAP_DELEGATE": "1"}
    return [compiler, "run", fixture, "--interpret"], {"SIMPLE_NO_BOOTSTRAP_DELEGATE": "1"}


def matrix_status(phase, native_status, interpreter_status):
    """Phase 2 is compiler-only; its configured skip is not an interpreter pass."""
    if native_status == "FAIL":
        return "FAIL"
    if interpreter_status != "PASS" and not (phase == 2 and interpreter_status == "SKIPPED"):
        return "FAIL"
    return native_status


def runtime_identity(root):
    return {str(path.relative_to(root)): digest(path)
            for path in root.rglob("*") if path.is_file() and
            (path.suffix in {".a", ".lib", ".o", ".obj", ".dll", ".so", ".dylib"} or path.name == "hosted-runtime.env")}


def first_command_executable(text):
    """Read only the tool token from diagnostic metadata; never eval it."""
    line = text.strip()
    if not line or "\n" in line or "\r" in line:
        raise ValueError("multiline/empty natural linker metadata")
    if line.startswith('"'):
        end = line.find('"', 1)
        if end < 0 or (len(line) > end + 1 and not line[end + 1].isspace()):
            raise ValueError("ambiguous quoted natural linker executable")
        value = line[1:end]
    else:
        value = line.split(None, 1)[0]
    if not value or '"' in value:
        raise ValueError("invalid natural linker executable")
    return value


def phase1_linker_proxy(directory, linker, capture):
    """Instrument the real LLD tool, never synthesize a tested program launcher."""
    directory.mkdir()
    proxy = directory / linker.name
    metadata = Path(str(capture) + ".tool.sdn")
    program = "#!/usr/bin/env python3\n" + "\n".join([
        "import hashlib, os, pathlib, sys",
        "tool = " + repr(str(linker)),
        "record = pathlib.Path(" + repr(str(metadata)) + ")",
        "if '--version' not in sys.argv and '-v' not in sys.argv:",
        "    sha = hashlib.sha256(pathlib.Path(tool).read_bytes()).hexdigest()",
        "    with record.open('x') as stream:",
        "        stream.write(" + repr('linker_sha256: "') + " + sha + " + repr('"\n') + ")",
        "os.execv(tool, [tool, *sys.argv[1:]])",
        "",
    ])
    proxy.write_text(program)
    proxy.chmod(0o755)
    return proxy


class Matrix:
    def __init__(self, args):
        self.args = args
        self.root = args.source_root.resolve()
        self.out = args.output.resolve()
        self.compiler = args.compiler.resolve()
        self.runtime = args.runtime_path.resolve()
        self.sha = digest(self.compiler)
        # LLD selects its driver from argv[0]; resolving ld.lld -> lld breaks
        # linking even though the target bytes have the same SHA-256.
        self.linker = Path(os.path.abspath(shutil.which(args.linker)))
        self.linker_sha = digest(self.linker)
        self.runtime_hashes = runtime_identity(self.runtime)
        if not self.runtime_hashes:
            raise ValueError("runtime contains no bound library/object authority")
        self.created_output = False
        self.windows = os.name == "nt"
        self.darwin = sys.platform == "darwin"
        if self.darwin:
            helper = Path(__file__).with_name("hello-sanity-matrix-darwin.py")
            spec = importlib.util.spec_from_file_location("hello_matrix_darwin", helper)
            self.darwin_adapter = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(self.darwin_adapter)
            self.driver = self.darwin_adapter.resolve_driver()
            self.driver_sha = digest(self.driver)
            self.sdk = self.darwin_adapter.resolve_sdk()
        self.windows_budget = None
        if self.windows:
            helper = Path(__file__).with_name("hello-sanity-matrix-windows.py")
            spec = importlib.util.spec_from_file_location("hello_matrix_windows", helper)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            self.windows_budget = module.install_memory_budget(
                (len(args.lanes) + 1) * args.max_rss_kib * 1024 + 268435456)
        self.stop = threading.Event()
        self.lock = threading.Lock()
        self.children = set()
        self.base = os.environ.copy()
        for key in list(self.base):
            if key.startswith("SIMPLE_") or key.startswith("BOOTSTRAP_"):
                del self.base[key]
        self.base.update({
            "SIMPLE_BINARY": str(self.compiler), "SIMPLE_BIN": str(self.compiler),
            "SIMPLE_BOOTSTRAP_DRIVER": str(self.compiler),
            "SIMPLE_FRONTEND_DELEGATE": str(self.compiler),
            "SIMPLE_FRONTEND_DELEGATED": "1", "SIMPLE_NO_STUB_FALLBACK": "1",
            "SIMPLE_NATIVE_BUILD_FORCE_WORKER": "0", "SIMPLE_BOOTSTRAP": "1",
            "SIMPLE_LIB": str(self.root / "src"),
            "SIMPLE_RUNTIME_PATH": str(self.runtime),
            "SIMPLE_PACKAGE_INDEX_COLD_INIT": "1", "SIMPLE_LINKER": "lld-link" if self.windows and args.windows_abi == "msvc" else "lld",
        })
        if self.darwin:
            self.base.pop("SIMPLE_LINKER", None)
            self.base = self.darwin_adapter.driver_environment(self.base)
            self.base["SDKROOT"] = str(self.sdk)
        self.base["PATH"] = str(self.linker.parent) + os.pathsep + self.base.get("PATH", "")

    def validate_identity(self):
        if digest(self.compiler) != self.sha:
            raise ValueError("phase compiler bytes changed")
        if self.darwin and digest(self.driver) != self.driver_sha:
            raise ValueError("Darwin compiler driver bytes changed")
        if digest(self.linker) != self.linker_sha:
            raise ValueError("linker bytes changed")

    def command_environment(self, lane, extra=None):
        extra = extra or {}
        if {"HOME", "home", "CODEX_HOME"} & extra.keys():
            raise ValueError("reserved user environment cannot be repurposed")
        env = self.base | {
            "TMPDIR": str(lane / "tmp"),
            "SIMPLE_USER_STORAGE_ROOT": str(lane / "storage"),
            "SIMPLE_NATIVE_BUILD_CACHE_DIR": str(lane / "native-state"),
            "SIMPLE_CACHE": str(lane / "cache" / "user"),
            "SIMPLE_CACHE_PROJECT": str(lane / "cache" / "project"),
            "XDG_CACHE_HOME": str(lane / "cache" / "xdg"),
        }
        return env | extra

    def run(self, lane, name, argv, extra=None, cwd=None, seconds=None):
        if self.stop.is_set():
            raise ValueError("interrupted before command launch")
        self.validate_identity()
        if shutil.disk_usage(self.out).free < self.args.min_free_disk_bytes:
            raise ValueError("disk reserve reached before command launch")
        env = self.command_environment(lane, extra)
        for child in ["tmp", "storage", "native-state", "cache/user", "cache/project", "cache/xdg"]:
            (lane / child).mkdir(parents=True, exist_ok=True)
        timeout = seconds or self.args.timeout_seconds
        log = lane / (name + ".log")
        stdout = lane / (name + ".stdout")
        stderr = lane / (name + ".stderr")
        watchdog = self.root / "scripts/resource/process-tree-rss-watchdog.pl"
        command = ["perl", str(watchdog), f"--max-rss-kib={self.args.max_rss_kib}",
                   "--interval-ms=100", f"--timeout-seconds={timeout}",
                   "--session-mode=new", "--budget-scope=compiler", "--compiler-jobs=1",
                   f"--receipt={lane / (name + '.rss.env')}", "--"] + list(map(str, argv))
        if self.windows:
            owner = self.root / "scripts/bootstrap/run-process-group-bounded-log-windows.py"
            command = [sys.executable, str(owner), "--output-parent", str(lane),
                "--log-leaf", name + ".owner.log", "--receipt-leaf", name + ".owner.env",
                "--helper-sha256", digest(owner), "--max-bytes", str(self.args.max_log_bytes),
                "--timeout-seconds", str(timeout), "--term-grace-seconds", "1",
                "--root-exit-policy", "terminate-job", "--", sys.executable,
                str(Path(__file__).resolve()), "--capture-split", str(lane / name), *map(str, argv)]
        (lane / (name + ".argv.txt")).write_text(shlex.join(command) + "\n")
        begin = time.monotonic()
        reason = "child-exit"
        with (lane / (name + ".supervisor.stdout")).open("xb") if self.windows else stdout.open("xb") as out, \
             (lane / (name + ".supervisor.stderr")).open("xb") if self.windows else stderr.open("xb") as err:
            process = subprocess.Popen(command, cwd=cwd or self.root, env=env,
                                       stdout=out, stderr=err, start_new_session=not self.windows)
            with self.lock:
                self.children.add(process.pid)
            print(f"LAUNCHED {lane.name}/{name} pid={process.pid}", flush=True)
            try:
                while process.poll() is None:
                    if self.stop.is_set():
                        reason = "interrupted"
                    elif time.monotonic() - begin > timeout + 15:
                        reason = "supervisor-timeout"
                    elif shutil.disk_usage(self.out).free < self.args.min_free_disk_bytes:
                        reason = "disk-reserve"
                    elif sum(path.stat().st_size for path in [stdout, stderr] if path.exists()) > self.args.max_log_bytes:
                        reason = "log-limit"
                    else:
                        time.sleep(0.1)
                        continue
                    process.terminate() if self.windows else process.send_signal(signal.SIGTERM)
                    try:
                        process.wait(timeout=45)
                    except subprocess.TimeoutExpired:
                        # Retain the watchdog until its finite owned-child cleanup
                        # completes; killing it first can orphan a compiler tree.
                        try:
                            process.wait(timeout=timeout + 60)
                        except subprocess.TimeoutExpired as error:
                            sdn(lane / (name + ".cleanup.sdn"), {
                                "status": "RUNNING_FINALIZATION", "watchdog_pid": process.pid,
                                "watchdog_timeout_seconds": timeout, "admitted": False})
                            raise CleanupPending("retained watchdog cleanup is still active") from error
                    break
                code = process.wait()
            finally:
                with self.lock:
                    if process.poll() is not None:
                        self.children.discard(process.pid)
        log.write_bytes(stdout.read_bytes() + stderr.read_bytes())
        sdn(lane / (name + ".sdn"), {"exit_code": code, "reason": reason,
            "compiler_sha256": self.sha, "elapsed_seconds": round(time.monotonic() - begin, 3),
            "stdout_sha256": digest(stdout), "stderr_sha256": digest(stderr)})
        self.validate_identity()
        if not self.windows:
            fields = dict(line.split("=", 1) for line in
                          (lane / (name + ".rss.env")).read_text().splitlines() if "=" in line)
            if fields.get("quiescent") != "1" or fields.get("observer_errors") != "0":
                raise ValueError(f"{name}: process tree lacks quiescent ownership receipt")
        if code or reason != "child-exit":
            raise ValueError(f"{name}: exit={code} reason={reason}; see {log}")
        return stdout.read_bytes(), stderr.read_bytes()

    def compile(self, lane, name, entry, output, flags=(), extra=None):
        command = [str(self.compiler), "native-build", "--backend", self.args.backend,
                   "--runtime-bundle", "core-c-bootstrap", "--runtime-path", str(self.runtime),
                   "--entry-closure", "--threads", "1", "--cache-dir", str(lane / "cache" / name),
                   "--mode", "one-binary", "--entry", str(entry), "--output", str(output)]
        if self.darwin:
            command.extend(["--source", str(entry.parent)])
        command.extend(flags)
        capture = None
        if self.darwin and not flags and not (extra or {}).get("SIMPLE_CC"):
            capture = lane / (name + ".link.json")
            proxy = self.darwin_adapter.capture_proxy(lane / (name + "-tool"), self.driver, self.linker, capture)
            extra = (extra or {}) | {"SIMPLE_CC": str(proxy)}
        self.run(lane, name, command, extra)
        if not output.is_file() or output.stat().st_size == 0:
            raise ValueError(f"{name}: missing/empty artifact")
        if capture:
            self.darwin_adapter.verify_capture(capture, output, self.driver, self.linker)

    def check_executable(self, lane, executable):
        stdout, stderr = self.run(lane, "execute", [executable], seconds=5)
        if stdout != EXPECTED or stderr:
            raise ValueError(f"executable output differs: stdout={stdout!r} stderr={stderr!r}")

    def verify_capture(self, lane, capture, captured_output):
        if not self.windows and self.args.phase != 1:
            verify_capture_receipt(capture, captured_output, self.linker)
            return
        if self.windows:
            # The compiler records the same actual executable passed to its
            # Windows process owner. A clang driver cannot prove LLD identity.
            records = list(captured_output.parent.rglob(captured_output.name + "*.link-command.txt"))
            if len(records) != 1:
                raise ValueError("natural Windows link lacks unique actual tool metadata")
            metadata = records[0]
            tool = first_command_executable(metadata.read_text())
            resolved = shutil.which(tool, path=self.base["PATH"])
            if not resolved or digest(resolved) != self.linker_sha or Path(resolved).name.lower() != self.linker.name.lower():
                raise ValueError("natural Windows linker differs from pinned replay driver")
        else:
            metadata = Path(str(capture) + ".tool.sdn")
            fields = dict(line.split(": ", 1) for line in metadata.read_text().splitlines())
            if fields != {"linker_sha256": '"' + self.linker_sha + '"'}:
                raise ValueError("phase1 actual linker-tool identity missing/mismatched")
        sdn(lane / "capture-binding.sdn", {"schema": "hello-matrix-link-capture-v1",
            "archive_sha256": digest(capture), "output_sha256": digest(captured_output),
            "linker_sha256": self.linker_sha, "tool_metadata_sha256": digest(metadata),
            "admitted": False})

    def replay(self, lane, main, provider, capture, output, captured_output=None):
        if captured_output is None:
            captured_output = lane / "capture-program"
        if self.darwin:
            command, root = self.darwin_adapter.replay_inputs(
                capture, captured_output, self.driver, self.linker, main, provider, output)
            self.run(lane, "link-explicit-objects", command, cwd=root)
            sdn(lane / "link-inputs.sdn", {"main_object": main, "main_sha256": digest(main),
                "provider": provider, "provider_sha256": digest(provider),
                "exact_emitted_inputs_consumed": True, "capture_sha256": digest(capture),
                "driver_sha256": self.driver_sha, "linker_sha256": self.linker_sha})
            return
        self.verify_capture(lane, capture, captured_output)
        unpack = lane / "link-reproduction"
        unpack.mkdir()
        with tarfile.open(capture) as archive:
            if any(not item.isfile() and not item.isdir() for item in archive.getmembers()):
                raise ValueError("nonregular linker reproduction member")
            archive.extractall(unpack, filter="data")
        responses = list(unpack.glob("*/response.txt"))
        if len(responses) != 1:
            raise ValueError("expected one genuine LLD response.txt")
        root = responses[0].parent
        tokens = replace_inputs(response_tokens(responses[0].read_text(), self.windows and self.args.windows_abi == "msvc"), root, main, provider)
        # Last -o is authoritative in LLD; preserve every original link input.
        selected_output = os.path.relpath(output, root) if "--chroot" in tokens or "--chroot=." in tokens else str(output)
        tokens.extend(["/out:" + selected_output] if self.windows and self.args.windows_abi == "msvc" else ["-o", selected_output])
        response = lane / "explicit-inputs.rsp"
        response.write_text(subprocess.list2cmdline(tokens) if self.windows and self.args.windows_abi == "msvc" else shlex.join(tokens))
        self.run(lane, "link-explicit-objects", [self.linker, "@" + str(response)], cwd=root)
        sdn(lane / "link-inputs.sdn", {"main_object": main, "main_sha256": digest(main),
             "provider": provider, "provider_sha256": digest(provider),
             "exact_emitted_inputs_consumed": True, "reproduction_sha256": digest(capture)})

    def shared_provider(self, lane, provider_object, library):
        if self.darwin:
            command = [self.driver, "--ld-path=" + str(self.linker), "--no-default-config", "-dynamiclib",
                       "-Wl,-undefined,error", "-Wl,-install_name,@loader_path/" + library.name,
                       "-o", library, provider_object]
        elif not self.windows:
            command = [self.linker, "-shared", "--no-undefined", "-soname", library.name,
                       "-o", library, provider_object]
        elif self.args.windows_abi == "msvc":
            command = [self.linker, "/DLL", "/NOENTRY", "/EXPORT:hello_value",
                       "/OUT:" + str(library), "/IMPLIB:" + str(lane / "hello.lib"), provider_object]
        else:
            machine = int.from_bytes(provider_object.read_bytes()[:2], "little")
            emulation = {0x8664: "i386pep", 0x14c: "i386pe", 0xaa64: "arm64pe"}.get(machine)
            if not emulation:
                raise ValueError("unsupported Windows GNU provider object machine")
            command = [self.linker, "-m", emulation, "-shared", "--export-all-symbols",
                       "--entry", "0", "--out-implib", lane / "hello.dll.a",
                       "-o", library, provider_object]
        self.run(lane, "link-provider-shared", command)
        if not library.is_file() or library.stat().st_size == 0:
            raise ValueError("platform linker produced no shared provider")

    def prior_native_inputs(self, name):
        prior = (self.args.reuse_shared_evidence if name == "shared-library" and self.args.reuse_shared_evidence
                 else self.args.reuse_build_evidence).resolve()
        fields = dict(line.split(": ", 1) for line in (prior / "identity.sdn").read_text().splitlines())
        if fields.get("compiler_sha256") != '"' + self.sha + '"' or fields.get("phase") != str(self.args.phase):
            raise ValueError("prior matrix compiler/phase identity mismatch")
        runtime_fields = dict(line.split(": ", 1) for line in (prior / "runtime-inputs.sdn").read_text().splitlines())
        if runtime_fields != {key: '"' + value + '"' for key, value in self.runtime_hashes.items()}:
            raise ValueError("prior matrix runtime authority mismatch")
        for fixture in ["single.spl", "main.spl", "provider.spl"]:
            if fields.get(fixture.replace(".", "_") + "_sha256") != '"' + digest(self.root / FIXTURES / fixture) + '"':
                raise ValueError("prior matrix fixture identity mismatch")
        # Inspect actual recorded compiler argv; old evidence may predate the
        # explicit backend field. A label alone cannot qualify another backend.
        provider_command = prior / name / "provider.argv.txt"
        if not provider_command.exists():
            provider_command = prior / name / "provider-object.argv.txt"
        command = shlex.split(provider_command.read_text())
        if command[command.index("--backend") + 1] != self.args.backend:
            raise ValueError("prior matrix backend mismatch")
        if name != "shared-library" or self.args.reuse_shared_evidence:
            jobs = ["provider", "main-object", "capture-hosted-link"] if name != "shared-library" else ["provider-object", "link-provider-shared", "main-object", "capture-hosted-link"]
            for job in jobs:
                receipt = prior / name / (job + ".sdn")
                job_fields = dict(line.split(": ", 1) for line in receipt.read_text().splitlines())
                if job_fields.get("exit_code") != "0" or job_fields.get("compiler_sha256") != '"' + self.sha + '"':
                    raise ValueError("prior native compilation did not pass with exact producer")
                for stream in ["stdout", "stderr"]:
                    if job_fields.get(stream + "_sha256") != '"' + digest(prior / name / (job + "." + stream)) + '"':
                        raise ValueError("prior native compilation stream identity mismatch")
        return prior / name

    def lane(self, name, barrier):
        lane = self.out / name
        started = time.monotonic()
        values = {"phase": self.args.phase, "compiler_sha256": self.sha, "status": "FAIL"}
        try:
            lane.mkdir()
            barrier.wait(timeout=15)
            output = lane / ("hello.exe" if self.windows else "hello")
            if name == "one-source":
                self.compile(lane, "single", FIXTURES / "single.spl", output)
            else:
                prior = self.prior_native_inputs(name) if self.args.reuse_build_evidence or (name == "shared-library" and self.args.reuse_shared_evidence) else None
                reusable_shared = name == "shared-library" and self.args.reuse_shared_evidence is not None
                provider = lane / {"two-objects": "provider.obj" if self.windows else "provider.o", "static-library": "hello.lib" if self.windows else "libhello.a",
                                   "shared-library": "hello.dll" if self.windows else "libhello.dylib" if self.darwin else "libhello.so"}[name]
                flag = {"two-objects": "--emit-object", "static-library": "--emit-archive",
                        "shared-library": "--emit-shared"}[name]
                main = lane / ("main.obj" if self.windows else "main.o")
                if reusable_shared:
                    shutil.copyfile(prior / provider.name, provider)
                    if self.windows:
                        for suffix in ["hello.lib", "hello.dll.a", "libhello.dll.a"]:
                            if (prior / suffix).exists():
                                shutil.copyfile(prior / suffix, lane / suffix)
                elif name == "shared-library":
                    provider_object = lane / ("provider.obj" if self.windows else "provider.o")
                    self.compile(lane, "provider-object", FIXTURES / "provider.spl", provider_object, ["--emit-object"])
                    self.shared_provider(lane, provider_object, provider)
                elif prior:
                    provider = prior / provider.name
                else:
                    self.compile(lane, "provider", FIXTURES / "provider.spl", provider, [flag])
                if prior and (name != "shared-library" or reusable_shared):
                    main = prior / main.name
                else:
                    self.compile(lane, "main-object", FIXTURES / "main.spl", main, ["--emit-object"])
                link_provider = provider
                if self.windows and name == "shared-library":
                    imports = [path for path in [lane / "hello.lib", lane / "hello.dll.a", lane / "libhello.dll.a"] if path.is_file()]
                    if len(imports) != 1:
                        raise ValueError("expected one genuine DLL import library from compiler shared emission")
                    link_provider = imports[0]
                capture = lane / ("link.json" if self.darwin else "link.tar")
                captured_output = lane / ("capture-program.exe" if self.windows else "capture-program")
                capture_env = {"SIMPLE_LINK_OBJECTS": str(link_provider)}
                capture_env["LLD_REPRODUCE" if self.windows else "SIMPLE_NATIVE_LINK_REPRODUCE_PATH"] = str(capture)
                if self.darwin:
                    capture_env.pop("SIMPLE_NATIVE_LINK_REPRODUCE_PATH", None)
                    proxy = self.darwin_adapter.capture_proxy(lane / "capture-tool", self.driver, self.linker, capture)
                    capture_env["SIMPLE_CC"] = str(proxy)
                elif self.args.phase == 1:
                    capture_env.pop("SIMPLE_NATIVE_LINK_REPRODUCE_PATH", None)
                    capture_env["LLD_REPRODUCE"] = str(capture)
                    if not self.windows:
                        proxy = phase1_linker_proxy(lane / "capture-tool", self.linker, capture)
                        capture_env["PATH"] = str(proxy.parent) + os.pathsep + self.base["PATH"]
                if prior and (name != "shared-library" or reusable_shared):
                    capture = prior / ("link.json" if self.darwin else "link.tar")
                    captured_output = prior / captured_output.name
                else:
                    self.compile(lane, "capture-hosted-link", FIXTURES / "main.spl", captured_output,
                        extra=capture_env)
                self.replay(lane, main, link_provider, capture, output, captured_output)
                if name == "shared-library":
                    if self.darwin:
                        stdout, _ = self.run(lane, "dynamic-needed", ["otool", "-L", output])
                        if b"@loader_path/libhello.dylib" not in stdout:
                            raise ValueError("shared executable lacks provider LC_LOAD_DYLIB")
                        symbols, _ = self.run(lane, "provider-symbols", ["nm", "-gU", provider])
                    else:
                        stdout, _ = self.run(lane, "dynamic-needed", ["llvm-readobj", "--coff-imports", output] if self.windows else ["readelf", "-d", output])
                        if (b"hello.dll" not in stdout.lower()) if self.windows else (b"NEEDED" not in stdout or b"libhello.so" not in stdout):
                            raise ValueError("shared executable lacks provider dynamic dependency")
                        symbols, _ = self.run(lane, "provider-symbols", ["llvm-readobj", "--coff-exports", provider] if self.windows else ["nm", "-D", "--defined-only", provider])
                    if b"hello_value" not in symbols:
                        raise ValueError("shared provider export hello_value is missing")
            self.check_executable(lane, output)
            values.update(status="PASS", executable_sha256=digest(output))
        except Exception as error:
            if self.args.jobs != 1:
                barrier.abort()
            values["reason"] = str(error)
            if isinstance(error, CleanupPending):
                values["status"] = "RUNNING_FINALIZATION"
        values["elapsed_seconds"] = round(time.monotonic() - started, 3)
        if lane.is_dir():
            sdn(lane / "result.sdn", values)
        else:
            sdn(self.out / (name + ".failure.sdn"), values)
        print(f"RESULT {name} {values['status']} {values.get('reason', '')}", flush=True)
        return values

    def interpreter(self):
        lane = self.out / "interpreter"
        lane.mkdir()
        values = {"phase": self.args.phase, "compiler_sha256": self.sha, "status": "FAIL"}
        try:
            if self.args.prior_interpreter_evidence:
                if self.args.phase == 1:
                    raise ValueError("phase 1 interpreter evidence must bind interpreter environment; reuse unavailable")
                prior = self.args.prior_interpreter_evidence.resolve()
                record = dict(line.split(": ", 1) for line in prior.read_text().splitlines())
                identity = dict(line.split(": ", 1) for line in (prior.parent.parent / "identity.sdn").read_text().splitlines())
                run = dict(line.split(": ", 1) for line in (prior.parent / "run.sdn").read_text().splitlines())
                if record.get("compiler_sha256") != '"' + self.sha + '"' or record.get("phase") != str(self.args.phase) or \
                        identity.get("single_spl_sha256") != '"' + digest(self.root / FIXTURES / "single.spl") + '"':
                    raise ValueError("prior interpreter owner/fixture identity mismatch")
                for stream in ["stdout", "stderr"]:
                    if run.get(stream + "_sha256") != '"' + digest(prior.parent / ("run." + stream)) + '"':
                        raise ValueError("prior interpreter stream identity mismatch")
                status = record.get("status", "").strip('"')
                if status == "UNSUPPORTED":
                    if "unknown command 'run'" not in (prior.parent / "run.log").read_text() or run.get("exit_code") != "1":
                        raise ValueError("prior unsupported interpreter lacks actual rejection")
                elif status == "PASS":
                    command = shlex.split((prior.parent / "run.argv.txt").read_text())
                    expected = [str(self.compiler), "run", str(FIXTURES / "single.spl"), "--interpret"]
                    runtime_fields = dict(line.split(": ", 1) for line in (prior.parent.parent / "runtime-inputs.sdn").read_text().splitlines())
                    if command[-len(expected):] != expected:
                        raise ValueError("prior PASS did not execute canonical interpreter command")
                    if runtime_fields != {key: '"' + value + '"' for key, value in self.runtime_hashes.items()}:
                        raise ValueError("prior interpreter runtime identity mismatch")
                    if run.get("compiler_sha256") != '"' + self.sha + '"' or run.get("exit_code") != "0" or (prior.parent / "run.stdout").read_bytes() != EXPECTED or (prior.parent / "run.stderr").read_bytes():
                        raise ValueError("prior interpreter did not execute exact Hello")
                else:
                    raise ValueError("prior interpreter result is not reusable")
                values.update(status=status, prior_evidence=str(prior), prior_sha256=digest(prior), evidence_reused=True)
                sdn(lane / "result.sdn", values)
                print("RESULT interpreter " + status + " (exact evidence reused)", flush=True)
                return values
            command, interpreter_env = interpreter_invocation(self.args.phase, self.compiler)
            sdn(lane / "interpreter-mode.sdn", interpreter_env)
            stdout, stderr = self.run(lane, "run", command, extra=interpreter_env, seconds=30)
            # The seed emits this advisory for the full source library, even in
            # forced interpreter mode. It is not a successful-output substitute.
            permitted = (stderr.startswith(b"[memory-guard] SIMPLE_LIB=") and
                         stderr.endswith(" contains 600+ .spl files — consider narrowing scope to avoid memory bloat\n".encode()) and
                         stderr.count(b"\n") == 1)
            if stdout != EXPECTED or (stderr and not (self.args.phase == 1 and permitted)):
                raise ValueError("interpreter stdout/stderr differs from exact Hello oracle")
            values["status"] = "PASS"
        except Exception as error:
            values["reason"] = str(error)
            diagnostic = (lane / "run.log").read_text(errors="replace") if (lane / "run.log").exists() else ""
            if "unknown command 'run'" in diagnostic:
                values["status"] = "UNSUPPORTED"
                values["reason"] = "exact phase compiler has no run/interpreter command; no fallback owner"
        sdn(lane / "result.sdn", values)
        print("RESULT interpreter " + values["status"], flush=True)
        return values

    def execute(self):
        self.out.mkdir(parents=True, exist_ok=False)
        self.created_output = True
        fixture_hashes = {name: digest(self.root / FIXTURES / name)
                          for name in ["single.spl", "main.spl", "provider.spl"]}
        revision = subprocess.check_output(["git", "-C", str(self.root), "rev-parse", "HEAD"], text=True).strip()
        sdn(self.out / "identity.sdn", {"classification": "DIAGNOSTIC_NOT_ADMITTED",
            "phase": self.args.phase, "compiler": self.compiler, "compiler_sha256": self.sha,
            "backend": self.args.backend,
            "source_root": self.root, "source_revision": revision, "runtime": self.runtime,
            "linker": self.linker, "linker_sha256": self.linker_sha,
            **({"driver": self.driver, "driver_sha256": self.driver_sha, "sdk": self.sdk} if self.darwin else {}),
            **{name.replace(".", "_") + "_sha256": sha for name, sha in fixture_hashes.items()}})
        sdn(self.out / "runtime-inputs.sdn", self.runtime_hashes)
        setup = self.out / "setup"
        setup.mkdir()
        if self.args.prior_version_evidence:
            prior = self.args.prior_version_evidence.resolve()
            fields = dict(line.split(": ", 1) for line in prior.read_text().splitlines())
            prefix = prior.with_suffix("")
            if fields.get("exit_code") != "0" or fields.get("reason") != '"child-exit"' or \
                    fields.get("compiler_sha256") != '"' + self.sha + '"' or \
                    fields.get("stdout_sha256") != '"' + digest(Path(str(prefix) + ".stdout")) + '"' or \
                    fields.get("stderr_sha256") != '"' + digest(Path(str(prefix) + ".stderr")) + '"':
                raise ValueError("prior compiler version evidence identity mismatch")
            sdn(setup / "version-reuse.sdn", {"prior_evidence": prior, "sha256": digest(prior)})
        else:
            self.run(setup, "compiler-version", [self.compiler, "--version"], seconds=5)
        # The exact compiler initializes this source owner's inventory once.
        # All four concurrent lanes then consume it through the warm path.
        if not (self.root / "build/scv/source-inventory/CURRENT").exists():
            try:
                self.compile(setup, "source-inventory-prime", FIXTURES / "single.spl", setup / "prime.o",
                             ["--emit-object"], {"SIMPLE_SCV_INVENTORY_COLD_INIT": "1"})
            except ValueError:
                if not (self.root / "build/scv/source-inventory/CURRENT").exists():
                    raise
        barrier = threading.Barrier(1 if self.args.jobs == 1 else len(self.args.lanes))
        with concurrent.futures.ThreadPoolExecutor(max_workers=self.args.jobs or len(self.args.lanes) + 1) as pool:
            futures = [pool.submit(self.lane, name, barrier) for name in self.args.lanes]
            configured_skip = not phase_capabilities(self.args.phase)[0]
            interpreter = pool.submit(self.interpreter) if not configured_skip and not self.args.skip_interpreter else None
            rows = [future.result() for future in futures]
            interpreter_result = interpreter.result() if interpreter else {"status": "SKIPPED" if configured_skip else "UNRUN"}
        buildrunner_rows = {name: {"status": "SKIPPED" if not phase_capabilities(self.args.phase)[1] else "UNRUN"} for name in LANES}
        provider = (self.args.buildrunner_manager, self.args.buildrunner_manifest_writer,
                    self.args.buildrunner_template, self.args.buildrunner_target)
        if phase_capabilities(self.args.phase)[1] and all(provider):
            helper = Path(__file__).with_name("hello-sanity-buildrunner.py")
            spec = importlib.util.spec_from_file_location("hello_sanity_buildrunner", helper)
            adapter = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(adapter)
            buildrunner_rows["one-source"] = adapter.run_one_source(self, self.args.backend, *provider)
        for name, record in buildrunner_rows.items():
            sdn(self.out / ("buildrunner-" + name + ".sdn"), record)
        for name, sha in fixture_hashes.items():
            if digest(self.root / FIXTURES / name) != sha:
                raise ValueError("fixture changed during matrix")
        if runtime_identity(self.runtime) != self.runtime_hashes:
            raise ValueError("runtime authority bytes changed during matrix")
        passed = sum(row["status"] == "PASS" for row in rows)
        complete_native = set(self.args.lanes) == set(LANES)
        native_status = "FAIL" if passed != len(rows) else "PASS" if complete_native else "PARTIAL"
        status = matrix_status(self.args.phase, native_status, interpreter_result["status"])
        if phase_capabilities(self.args.phase)[1]:
            states = {row["status"] for row in buildrunner_rows.values()}
            buildrunner_status = "FAIL" if "FAIL" in states else "UNRUN" if states == {"UNRUN"} else "PARTIAL" if "UNRUN" in states else "PASS"
            if buildrunner_status == "FAIL":
                status = "FAIL"
            elif status == "PASS" and buildrunner_status != "PASS":
                status = "PARTIAL"
        else:
            buildrunner_status = "SKIPPED"
        if self.children:
            status = "RUNNING_FINALIZATION"
        sdn(self.out / "result.sdn", {"phase": self.args.phase, "compiler_sha256": self.sha,
            "status": status, "scope": "compiler-native-and-interpreter",
            "buildrunner_status": buildrunner_status,
            "native_status": native_status,
            "selected_native_status": "PASS" if passed == len(rows) else "FAIL",
            "required_native_lanes": 4, "selected_native_lanes": len(rows),
            "interpreter_status": interpreter_result["status"], "executed_lanes": len(rows),
            "passed_lanes": passed, "failed_lanes": len(rows) - passed, "admitted": False})
        return 0 if status == "PASS" else 1


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--compiler", required=True, type=Path)
    parser.add_argument("--phase", required=True, type=int, choices=[1, 2, 3])
    parser.add_argument("--source-root", required=True, type=Path)
    parser.add_argument("--runtime-path", required=True, type=Path)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--backend", choices=["llvm", "cranelift"], default="cranelift")
    parser.add_argument("--timeout-seconds", type=int, default=900)
    parser.add_argument("--max-rss-kib", type=int, default=4194304,
                        help="per-lane process-tree budget; four concurrent lanes")
    parser.add_argument("--jobs", type=int, choices=[0, 1], default=1 if sys.platform == "darwin" else 0,
                        help="1 serializes native/interpreter commands; 0 runs lanes concurrently")
    parser.add_argument("--min-free-disk-bytes", type=int, default=1610612736)
    parser.add_argument("--max-log-bytes", type=int, default=4194304)
    parser.add_argument("--linker", default="lld-link" if os.name == "nt" else "ld64.lld" if sys.platform == "darwin" else "ld.lld")
    parser.add_argument("--windows-abi", choices=["msvc", "gnu"], default="msvc")
    parser.add_argument("--prior-version-evidence", type=Path,
                        help="reuse hash-bound green version evidence without rerunning it")
    parser.add_argument("--lanes", nargs="+", choices=LANES, default=list(LANES),
                        help="default: all four parallel native lanes; narrow only for retained failed-case repairs")
    parser.add_argument("--reuse-build-evidence", type=Path,
                        help="replay retained native inputs after validating phase/compiler/backend/fixture identities")
    parser.add_argument("--reuse-shared-evidence", type=Path,
                        help="reuse a retained successful platform shared-provider build and hosted capture")
    parser.add_argument("--skip-interpreter", action="store_true",
                        help="explicitly unrun interpreter case when reusing separate retained evidence")
    parser.add_argument("--prior-interpreter-evidence", type=Path,
                        help="reuse exact phase/compiler/fixture interpreter evidence across code-generation backend reports")
    parser.add_argument("--buildrunner-manager", type=Path)
    parser.add_argument("--buildrunner-manifest-writer", type=Path)
    parser.add_argument("--buildrunner-template", type=Path)
    parser.add_argument("--buildrunner-target")
    args = parser.parse_args()
    provider = (args.buildrunner_manager, args.buildrunner_manifest_writer,
                args.buildrunner_template, args.buildrunner_target)
    if any(provider) and not all(provider):
        parser.error("BuildRunner requires manager, manifest writer, template, and target together")
    if all(provider):
        args.buildrunner_manager = args.buildrunner_manager.resolve()
        args.buildrunner_manifest_writer = args.buildrunner_manifest_writer.resolve()
        args.buildrunner_template = args.buildrunner_template.resolve()
    if len(set(args.lanes)) != len(args.lanes):
        parser.error("native lanes must be unique")
    if min(args.timeout_seconds, args.max_rss_kib, args.max_log_bytes) <= 0 or args.min_free_disk_bytes < 0:
        parser.error("resource bounds must be positive")
    if sys.platform not in {"linux", "darwin"} and os.name != "nt":
        parser.error("UNSUPPORTED: exact hosted-link adapters support Linux/ELF, macOS/Mach-O and native Windows/COFF")
    for tool in [args.linker, "llvm-readobj"] if os.name == "nt" else (["perl", args.linker, "clang", "otool", "nm"] if sys.platform == "darwin" else ["perl", args.linker, "readelf", "nm"]):
        if shutil.which(tool) is None:
            parser.error(f"missing required tool: {tool}")
    matrix = Matrix(args)
    for number in [signal.SIGINT, signal.SIGTERM]:
        signal.signal(number, lambda *_: matrix.stop.set())
    try:
        return matrix.execute()
    except Exception as error:
        if matrix.created_output:
            sdn(matrix.out / "result.sdn", {"phase": args.phase,
                "status": "RUNNING_FINALIZATION" if matrix.children else "FAIL",
                "reason": str(error), "admitted": False})
        print(f"FAIL: {error}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    if len(sys.argv) >= 4 and sys.argv[1] == "--capture-split":
        prefix = Path(sys.argv[2])
        with Path(str(prefix) + ".stdout").open("xb") as out, Path(str(prefix) + ".stderr").open("xb") as err:
            sys.exit(subprocess.call(sys.argv[3:], stdout=out, stderr=err))
    sys.exit(main())
