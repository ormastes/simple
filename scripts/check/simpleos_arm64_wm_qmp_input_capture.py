#!/usr/bin/env python3
"""Live QMP input/capture oracle for the canonical ARM64 SimpleOS desktop.

This helper is intentionally transport-only.  The shell wrapper owns the
current-source build and exact QEMU launch; this process owns one QMP session,
serial correlation, and PPM validation.  It never fabricates capture evidence.
"""

import hashlib
import json
import os
import pathlib
import re
import signal
import socket
import subprocess
import sys
import time


FAULT_PATTERNS = (
    "[desktop-gui-arm64] fatal",
    "[engine2d-simd] fatal",
    "*** EXCEPTION FRAME",
    "page-fault",
    "nil receiver",
)

SOURCE_MANIFEST_PATHS = (
    "src/os",
    "src/lib",
    "examples/09_embedded/simple_os",
    "scripts/os/make_os_disk.shs",
    "scripts/os/make_os_disk.c",
    "scripts/os/simpleos_font_bundle_companion.sha256",
    "assets/fonts",
    "scripts/check/check-simpleos-arm64-wm-input-evidence.shs",
    "scripts/check/simpleos_arm64_wm_qmp_input_capture.py",
    "test/03_system/os/wm/arm64_simpleos_qmp_input_spec.spl",
    "test/03_system/check/simpleos_arm64_wm_input_evidence_contract_spec.spl",
)


def _run_git(root, arguments):
    result = subprocess.run(
        ["git", "-C", root] + arguments,
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        timeout=30,
    )
    return result.stdout


def write_source_manifest(root, compiler, qemu, output_path):
    root_path = pathlib.Path(root).resolve()
    compiler_path = pathlib.Path(compiler).resolve()
    qemu_path = pathlib.Path(qemu).resolve()
    tracked = _run_git(
        str(root_path), ["ls-files", "-z", "--"] + list(SOURCE_MANIFEST_PATHS)
    ).split(b"\0")
    untracked = _run_git(
        str(root_path),
        ["ls-files", "--others", "--exclude-standard", "-z", "--"]
        + list(SOURCE_MANIFEST_PATHS),
    ).split(b"\0")
    relative_paths = sorted(
        {
            value.decode("utf-8", errors="surrogateescape")
            for value in tracked + untracked
            if value
        }
    )
    lines = ["schema=simpleos-arm64-wm-source-manifest-v1"]
    head = _run_git(str(root_path), ["rev-parse", "HEAD"]).decode().strip()
    lines.append("git_head=" + head)
    diff = _run_git(
        str(root_path),
        ["diff", "--no-ext-diff", "--binary", "HEAD", "--"]
        + list(SOURCE_MANIFEST_PATHS),
    )
    lines.append("git_dirty_diff_sha256=" + hashlib.sha256(diff).hexdigest())
    lines.append("compiler_path=" + str(compiler_path))
    lines.append(
        "compiler_sha256="
        + hashlib.sha256(compiler_path.read_bytes()).hexdigest()
    )
    qemu_version = subprocess.run(
        [str(qemu_path), "--version"],
        check=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        text=True,
        timeout=15,
    ).stdout.splitlines()[0]
    lines.append("qemu_path=" + str(qemu_path))
    lines.append(
        "qemu_sha256=" + hashlib.sha256(qemu_path.read_bytes()).hexdigest()
    )
    lines.append("qemu_version_sha256=" + hashlib.sha256(qemu_version.encode()).hexdigest())
    for relative in relative_paths:
        path = root_path / relative
        if path.is_file():
            digest = hashlib.sha256(path.read_bytes()).hexdigest()
            mode = path.stat().st_mode & 0o777
            lines.append("file=%s mode=%04o sha256=%s" % (relative, mode, digest))
        else:
            lines.append("file=%s missing=true" % relative)
    pathlib.Path(output_path).write_text("\n".join(lines) + "\n")


def run_bounded(timeout_seconds, grace_seconds, log_path, arguments):
    with open(log_path, "wb") as log:
        process = subprocess.Popen(
            arguments,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
        try:
            return process.wait(timeout=timeout_seconds)
        except subprocess.TimeoutExpired:
            os.killpg(process.pid, signal.SIGTERM)
            try:
                process.wait(timeout=grace_seconds)
            except subprocess.TimeoutExpired:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
            return 124


def spawn_process(log_path, arguments):
    log = open(log_path, "wb")
    try:
        process = subprocess.Popen(
            arguments,
            stdout=log,
            stderr=subprocess.STDOUT,
            start_new_session=True,
        )
    finally:
        log.close()
    print(process.pid)


def terminate_process_group(pid, grace_seconds, expected_tokens):
    try:
        process_group = os.getpgid(pid)
    except ProcessLookupError:
        return
    command = subprocess.run(
        ["ps", "-ww", "-p", str(pid), "-o", "command="],
        check=False,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
        text=True,
        timeout=5,
    ).stdout
    if not command or any(token not in command for token in expected_tokens):
        raise RuntimeError("refusing-to-terminate-unowned-process")
    try:
        os.killpg(process_group, signal.SIGTERM)
    except ProcessLookupError:
        return
    deadline = time.monotonic() + grace_seconds
    while time.monotonic() < deadline:
        try:
            os.kill(pid, 0)
        except ProcessLookupError:
            return
        time.sleep(0.05)
    try:
        os.killpg(process_group, signal.SIGKILL)
    except ProcessLookupError:
        return


def serial_text(path):
    try:
        with open(path, "r", errors="replace") as stream:
            return stream.read()
    except OSError:
        return ""


def require_no_guest_fault(text):
    for pattern in FAULT_PATTERNS:
        if pattern in text:
            raise RuntimeError("guest-fault-observed:" + pattern)


class Qmp:
    def __init__(self, socket_path):
        self.socket = socket.socket(socket.AF_UNIX)
        self.socket.settimeout(10.0)
        self.socket.connect(socket_path)
        self.stream = self.socket.makefile("rwb", buffering=0)
        greeting_raw = self.stream.readline()
        if not greeting_raw:
            raise RuntimeError("qmp-greeting-missing")
        greeting = json.loads(greeting_raw)
        if "QMP" not in greeting:
            raise RuntimeError("qmp-greeting-invalid")
        self.next_id = 0
        self.command_count = 0

    def command(self, execute, arguments=None):
        self.next_id += 1
        self.command_count += 1
        request = {"execute": execute, "id": self.next_id}
        if arguments is not None:
            request["arguments"] = arguments
        self.stream.write(json.dumps(request).encode("utf-8") + b"\n")
        self.stream.flush()
        while True:
            raw = self.stream.readline()
            if not raw:
                raise RuntimeError("qmp-connection-closed")
            response = json.loads(raw)
            if response.get("id") != self.next_id:
                continue
            if "error" in response:
                raise RuntimeError(
                    "qmp-command-error:%s:%s" % (execute, response["error"])
                )
            if "return" not in response:
                raise RuntimeError("qmp-command-unacknowledged:" + execute)
            return response["return"]

    def close(self):
        try:
            self.stream.close()
        finally:
            self.socket.close()


def wait_for_file(path, timeout_seconds=15.0):
    deadline = time.monotonic() + timeout_seconds
    previous_size = -1
    stable_checks = 0
    while time.monotonic() < deadline:
        try:
            size = os.path.getsize(path)
        except OSError:
            size = -1
        if size > 16 and size == previous_size:
            stable_checks += 1
            if stable_checks >= 2:
                return
        else:
            stable_checks = 0
        previous_size = size
        time.sleep(0.05)
    raise RuntimeError("screendump-file-missing-or-unstable:" + path)


def ppm_tokens_and_payload(data):
    tokens = []
    index = 0
    length = len(data)
    while len(tokens) < 4:
        while index < length and data[index] in b" \t\r\n":
            index += 1
        if index >= length:
            raise RuntimeError("ppm-header-truncated")
        if data[index] == ord("#"):
            while index < length and data[index] not in b"\r\n":
                index += 1
            continue
        end = index
        while end < length and data[end] not in b" \t\r\n":
            end += 1
        tokens.append(data[index:end])
        index = end
    if index >= length or data[index] not in b" \t\r\n":
        raise RuntimeError("ppm-header-payload-separator-missing")
    if data[index : index + 2] == b"\r\n":
        index += 2
    else:
        index += 1
    return tokens, data[index:]


def validate_ppm(path):
    with open(path, "rb") as stream:
        data = stream.read()
    tokens, pixels = ppm_tokens_and_payload(data)
    if tokens[0] != b"P6":
        raise RuntimeError("ppm-magic-not-p6:" + path)
    try:
        width = int(tokens[1])
        height = int(tokens[2])
        maximum = int(tokens[3])
    except ValueError as error:
        raise RuntimeError("ppm-header-nonnumeric:" + path) from error
    if width <= 0 or height <= 0 or maximum != 255:
        raise RuntimeError("ppm-header-invalid:" + path)
    expected = width * height * 3
    if len(pixels) != expected:
        raise RuntimeError(
            "ppm-payload-size-mismatch:%s:expected=%d:actual=%d"
            % (path, expected, len(pixels))
        )
    first = pixels[0:3]
    nonuniform = any(
        pixels[offset : offset + 3] != first for offset in range(3, len(pixels), 3)
    )
    nonzero = any(value != 0 for value in pixels)
    if not nonuniform or not nonzero:
        raise RuntimeError("ppm-blank-or-uniform:" + path)
    return hashlib.sha256(data).hexdigest(), width, height


def wait_key_chain(serial_path, after_sequence, value, edge, timeout_seconds):
    deadline = time.monotonic() + timeout_seconds
    device_pattern = re.compile(
        r"^\[virtio-input-device\] input_seq=(\d+) "
        r"device=keyboard type=1 code=15 value=%d\r?$" % value,
        re.MULTILINE,
    )
    while time.monotonic() < deadline:
        text = serial_text(serial_path)
        require_no_guest_fault(text)
        sequences = sorted(
            {
                int(match.group(1))
                for match in device_pattern.finditer(text)
                if int(match.group(1)) > after_sequence
            }
        )
        for sequence in sequences:
            device = re.search(
                r"^\[virtio-input-device\] input_seq=%d "
                r"device=keyboard type=1 code=15 value=%d\r?$"
                % (sequence, value),
                text,
                re.MULTILINE,
            )
            poll = re.search(
                r"^\[wm-key-poll\] source=poll input_seq=%d edge=%s code=15\r?$"
                % (sequence, edge),
                text,
                re.MULTILINE,
            )
            state = re.search(
                r"^\[wm-key-state\] input_seq=%d edge=%s "
                r"changed=(?:true|false) focused_idx=-?\d+\r?$"
                % (sequence, edge),
                text,
                re.MULTILINE,
            )
            frame = re.search(
                r"^\[wm-key-frame\] input_seq=%d generation=[1-9]\d*\r?$"
                % sequence,
                text,
                re.MULTILINE,
            )
            if (
                device
                and poll
                and state
                and frame
                and device.start() < poll.start() < state.start() < frame.start()
            ):
                return sequence
        time.sleep(0.05)
    raise RuntimeError("key-device-wm-frame-correlation-missing:" + edge)


def wait_pointer_chain(
    serial_path,
    after_sequence,
    kind_code,
    button_code,
    raw_kind,
    expected_x,
    expected_y,
    timeout_seconds,
):
    deadline = time.monotonic() + timeout_seconds
    poll_pattern = re.compile(
        r"^\[wm-pointer-poll\] source=poll input_seq=(\d+) "
        r"x=%d y=%d button_code=%d kind_code=%d\r?$"
        % (expected_x, expected_y, button_code, kind_code),
        re.MULTILINE,
    )
    while time.monotonic() < deadline:
        text = serial_text(serial_path)
        require_no_guest_fault(text)
        sequences = sorted(
            {
                int(match.group(1))
                for match in poll_pattern.finditer(text)
                if int(match.group(1)) > after_sequence
            }
        )
        for sequence in sequences:
            raw_positions = []
            if raw_kind == "move":
                raw_x = re.search(
                    r"^\[virtio-input-device\] input_seq=%d device=pointer "
                    r"type=2 code=0 value=32 frame=raw-summary\r?$" % sequence,
                    text,
                    re.MULTILINE,
                )
                raw_y = re.search(
                    r"^\[virtio-input-device\] input_seq=%d device=pointer "
                    r"type=2 code=1 value=18 frame=raw-summary\r?$" % sequence,
                    text,
                    re.MULTILINE,
                )
                raw_ok = raw_x is not None and raw_y is not None
                if raw_ok:
                    raw_positions = [raw_x.start(), raw_y.start()]
            else:
                expected_value = 1 if raw_kind == "down" else 0
                raw_edge = re.search(
                    r"^\[virtio-input-device\] input_seq=%d device=pointer "
                    r"type=1 code=272 value=%d frame=raw-edge\r?$"
                    % (sequence, expected_value),
                    text,
                    re.MULTILINE,
                )
                raw_ok = raw_edge is not None
                if raw_ok:
                    raw_positions = [raw_edge.start()]
            sync = re.search(
                r"^\[virtio-input-device\] input_seq=%d device=pointer "
                r"type=0 code=0 value=0 frame=syn-report\r?$" % sequence,
                text,
                re.MULTILINE,
            )
            poll = re.search(
                r"^\[wm-pointer-poll\] source=poll input_seq=%d "
                r"x=%d y=%d button_code=%d kind_code=%d\r?$"
                % (
                    sequence,
                    expected_x,
                    expected_y,
                    button_code,
                    kind_code,
                ),
                text,
                re.MULTILINE,
            )
            state = re.search(
                r"^\[wm-pointer-state\] input_seq=%d focused_idx=-?\d+\r?$"
                % sequence,
                text,
                re.MULTILINE,
            )
            frame = re.search(
                r"^\[wm-pointer-frame\] input_seq=%d generation=[1-9]\d*\r?$"
                % sequence,
                text,
                re.MULTILINE,
            )
            if (
                raw_ok
                and sync
                and poll
                and state
                and frame
                and max(raw_positions)
                < sync.start()
                < poll.start()
                < state.start()
                < frame.start()
            ):
                return sequence
        time.sleep(0.05)
    raise RuntimeError(
        "pointer-device-wm-frame-correlation-missing:" + raw_kind
    )


def settle_ramfb(serial_path, timeout_seconds=3.0):
    deadline = time.monotonic() + timeout_seconds
    previous_size = -1
    stable = 0
    while time.monotonic() < deadline:
        text = serial_text(serial_path)
        require_no_guest_fault(text)
        size = len(text)
        if size == previous_size and size > 0:
            stable += 1
            if stable >= 3:
                time.sleep(0.1)
                return
        else:
            stable = 0
        previous_size = size
        time.sleep(0.05)
    raise RuntimeError("ramfb-serial-settle-timeout")


def capture(qmp, serial_path, path):
    try:
        os.unlink(path)
    except FileNotFoundError:
        pass
    settle_ramfb(serial_path)
    qmp.command("screendump", {"filename": path})
    deadline = time.monotonic() + 15.0
    last_error = "screendump-not-ready"
    while time.monotonic() < deadline:
        try:
            wait_for_file(path, 0.5)
            return validate_ppm(path)
        except (OSError, RuntimeError) as error:
            last_error = str(error)
            time.sleep(0.05)
    raise RuntimeError("ramfb-screendump-settle-failed:" + last_error)


def emit(name, value):
    print("simpleos_arm64_wm_input_%s=%s" % (name, value))


def run(arguments):
    if len(arguments) != 5:
        raise RuntimeError(
            "usage:qmp-socket serial-log baseline.ppm post-input.ppm"
        )
    qmp_socket, serial_path, baseline_path, post_path = arguments[1:]
    qmp = Qmp(qmp_socket)
    try:
        qmp.command("qmp_capabilities")
        baseline_hash, width, height = capture(qmp, serial_path, baseline_path)
        initial_text = serial_text(serial_path)
        require_no_guest_fault(initial_text)
        sequence_values = [
            int(value)
            for value in re.findall(
                r"^\[virtio-input-device\] input_seq=(\d+) ",
                initial_text,
                re.MULTILINE,
            )
        ]
        last_sequence = max(sequence_values) if sequence_values else 0

        qmp.command(
            "input-send-event",
            {
                "events": [
                    {
                        "type": "key",
                        "data": {
                            "down": True,
                            "key": {"type": "qcode", "data": "tab"},
                        },
                    }
                ]
            },
        )
        key_down_sequence = wait_key_chain(
            serial_path, last_sequence, 1, "press", 45.0
        )

        qmp.command(
            "input-send-event",
            {
                "events": [
                    {
                        "type": "key",
                        "data": {
                            "down": False,
                            "key": {"type": "qcode", "data": "tab"},
                        },
                    }
                ]
            },
        )
        key_up_sequence = wait_key_chain(
            serial_path, key_down_sequence, 0, "release", 45.0
        )

        qmp.command(
            "input-send-event",
            {
                "events": [
                    {"type": "rel", "data": {"axis": "x", "value": 32}},
                    {"type": "rel", "data": {"axis": "y", "value": 18}},
                ]
            },
        )
        pointer_move_sequence = wait_pointer_chain(
            serial_path, key_up_sequence, 3, 0, "move", 544, 402, 45.0
        )

        qmp.command(
            "input-send-event",
            {
                "events": [
                    {
                        "type": "btn",
                        "data": {"down": True, "button": "left"},
                    }
                ]
            },
        )
        pointer_down_sequence = wait_pointer_chain(
            serial_path, pointer_move_sequence, 1, 1, "down", 544, 402, 45.0
        )

        qmp.command(
            "input-send-event",
            {
                "events": [
                    {
                        "type": "btn",
                        "data": {"down": False, "button": "left"},
                    }
                ]
            },
        )
        pointer_up_sequence = wait_pointer_chain(
            serial_path, pointer_down_sequence, 2, 1, "up", 544, 402, 45.0
        )
        post_hash, post_width, post_height = capture(
            qmp, serial_path, post_path
        )

        if (post_width, post_height) != (width, height):
            raise RuntimeError("baseline-post-dimensions-differ")
        if baseline_hash == post_hash:
            raise RuntimeError("baseline-post-captures-identical")
        if qmp.command_count != 8:
            raise RuntimeError(
                "unexpected-qmp-command-count:%d" % qmp.command_count
            )

        emit("baseline_ppm_sha256", baseline_hash)
        emit("post_input_ppm_sha256", post_hash)
        emit("capture_width", width)
        emit("capture_height", height)
        emit("captures_nonblank", "true")
        emit("captures_different", "true")
        emit("key_down_input_sequence", key_down_sequence)
        emit("key_up_input_sequence", key_up_sequence)
        emit("pointer_move_input_sequence", pointer_move_sequence)
        emit("pointer_down_input_sequence", pointer_down_sequence)
        emit("pointer_up_input_sequence", pointer_up_sequence)
        emit("key_down_frame_sequence", key_down_sequence)
        emit("key_up_frame_sequence", key_up_sequence)
        emit("pointer_move_frame_sequence", pointer_move_sequence)
        emit("pointer_down_frame_sequence", pointer_down_sequence)
        emit("pointer_up_frame_sequence", pointer_up_sequence)
        emit("qmp_command_count", qmp.command_count)
        emit("status", "PASS")
    finally:
        qmp.close()


def main(arguments):
    if len(arguments) >= 2 and arguments[1] == "--source-manifest":
        if len(arguments) != 6:
            raise RuntimeError(
                "usage:--source-manifest root compiler qemu output-path"
            )
        write_source_manifest(
            arguments[2], arguments[3], arguments[4], arguments[5]
        )
        return 0
    if len(arguments) >= 2 and arguments[1] == "--run-bounded":
        if len(arguments) < 7 or arguments[5] != "--":
            raise RuntimeError(
                "usage:--run-bounded timeout grace log -- command..."
            )
        return run_bounded(
            float(arguments[2]),
            float(arguments[3]),
            arguments[4],
            arguments[6:],
        )
    if len(arguments) >= 2 and arguments[1] == "--spawn-process":
        if len(arguments) < 5 or arguments[3] != "--":
            raise RuntimeError("usage:--spawn-process log -- command...")
        spawn_process(arguments[2], arguments[4:])
        return 0
    if len(arguments) >= 2 and arguments[1] == "--terminate-process-group":
        if len(arguments) < 5:
            raise RuntimeError(
                "usage:--terminate-process-group pid grace-seconds expected-token..."
            )
        terminate_process_group(
            int(arguments[2]), float(arguments[3]), arguments[4:]
        )
        return 0
    run(arguments)
    return 0


if __name__ == "__main__":
    try:
        sys.exit(main(sys.argv))
    except Exception as error:  # Evidence lanes must turn every issue into FAIL.
        print(
            "simpleos_arm64_wm_input_capture_error=%s"
            % str(error).replace("\n", " "),
            file=sys.stderr,
        )
        sys.exit(1)
