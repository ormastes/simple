#!/usr/bin/env python3
"""Windows host-only adapter for the bootstrap bounded process collector.

The compiler and runtime do not import this helper. A suspended child joins a
kill-on-close Job Object before it executes; native descendants stay in that
job even after the root exits. Logs use locked real directories, never /proc.
"""

import argparse
import ctypes as ct
from ctypes import wintypes as wt
import hashlib
import os
from pathlib import Path
import re
import subprocess
import sys
import time


def digest(path):
    with open(path, "rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def main():
    if os.name != "nt":
        raise RuntimeError("Windows adapter requires native Windows Python")
    import msvcrt

    parser = argparse.ArgumentParser()
    for key in ("output-parent", "log-leaf", "receipt-leaf", "helper-sha256"):
        parser.add_argument("--" + key, required=True)
    for key in ("max-bytes", "timeout-seconds", "term-grace-seconds"):
        parser.add_argument("--" + key, type=int, required=True)
    parser.add_argument("--command-environment", choices=("inherited", "clean-prefix"), default="inherited")
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else []
    if not command or args.max_bytes <= 0 or args.timeout_seconds <= 0 or args.term_grace_seconds < 0:
        raise RuntimeError("invalid command or limits")
    environment_text = None
    if args.command_environment == "clean-prefix":
        # The caller already constructs a reviewed env -i invocation. Consume
        # that exact envelope here, avoiding an MSYS env.exe status translation
        # between the native Cargo process and this native Windows supervisor.
        if command[:2] != ["env", "-i"]:
            raise RuntimeError("clean environment requires an env -i prefix")
        command = command[2:]
        environment = {}
        environment_names = set()
        while command and "=" in command[0]:
            key, value = command.pop(0).split("=", 1)
            if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", key) or key.casefold() in environment_names:
                raise RuntimeError("invalid or duplicate clean environment name")
            environment[key] = value
            environment_names.add(key.casefold())
        if not command or not os.path.isabs(command[0]):
            raise RuntimeError("clean environment requires an absolute native executable")
        environment_text = "\0".join(f"{key}={environment[key]}" for key in sorted(environment, key=str.casefold)) + "\0\0"
    for leaf in (args.log_leaf, args.receipt_leaf):
        if not re.fullmatch(r"[A-Za-z0-9_.-]+", leaf) or leaf in (".", ".."):
            raise RuntimeError("unsafe output leaf")
    if args.log_leaf.casefold() == args.receipt_leaf.casefold():
        raise RuntimeError("log and receipt leaves collide")
    helper = Path(__file__).absolute()
    if not re.fullmatch(r"[0-9a-f]{64}", args.helper_sha256) or digest(helper) != args.helper_sha256:
        raise RuntimeError("collector helper hash mismatch")

    kernel = ct.WinDLL("kernel32", use_last_error=True)
    handle = wt.HANDLE
    voidp = ct.c_void_p
    size = ct.c_size_t

    class StartupInfo(ct.Structure):
        _fields_ = [("cb", wt.DWORD), ("reserved", wt.LPWSTR),
                    ("desktop", wt.LPWSTR), ("title", wt.LPWSTR)] + [
            (name, wt.DWORD) for name in ("x", "y", "xsize", "ysize", "xchars", "ychars", "fill", "flags")
        ] + [("show", wt.WORD), ("reserved_size", wt.WORD),
             ("reserved_bytes", voidp), ("stdin", handle), ("stdout", handle), ("stderr", handle)]

    class ProcessInfo(ct.Structure):
        _fields_ = [("process", handle), ("thread", handle), ("pid", wt.DWORD), ("tid", wt.DWORD)]

    class BasicLimit(ct.Structure):
        _fields_ = [("process_time", ct.c_longlong), ("job_time", ct.c_longlong),
                    ("flags", wt.DWORD), ("min_working", size), ("max_working", size),
                    ("active_limit", wt.DWORD), ("affinity", size),
                    ("priority", wt.DWORD), ("scheduling", wt.DWORD)]

    class ExtendedLimit(ct.Structure):
        _fields_ = [("basic", BasicLimit), ("io", ct.c_ulonglong * 6),
                    ("process_memory", size), ("job_memory", size),
                    ("peak_process_memory", size), ("peak_job_memory", size)]

    class Accounting(ct.Structure):
        _fields_ = [("times", ct.c_longlong * 4), ("page_faults", wt.DWORD),
                    ("total", wt.DWORD), ("active", wt.DWORD), ("terminated", wt.DWORD)]

    def api(name, result, *parameters):
        fn = getattr(kernel, name)
        fn.restype, fn.argtypes = result, parameters
        return fn

    close = api("CloseHandle", wt.BOOL, handle)
    create_file = api("CreateFileW", handle, wt.LPCWSTR, wt.DWORD, wt.DWORD, voidp, wt.DWORD, wt.DWORD, handle)
    attributes = api("GetFileAttributesW", wt.DWORD, wt.LPCWSTR)
    create_job = api("CreateJobObjectW", handle, voidp, wt.LPCWSTR)
    set_job = api("SetInformationJobObject", wt.BOOL, handle, ct.c_int, voidp, wt.DWORD)
    query_job = api("QueryInformationJobObject", wt.BOOL, handle, ct.c_int, voidp, wt.DWORD, voidp)
    assign = api("AssignProcessToJobObject", wt.BOOL, handle, handle)
    terminate_job = api("TerminateJobObject", wt.BOOL, handle, wt.UINT)
    terminate_process = api("TerminateProcess", wt.BOOL, handle, wt.UINT)
    create_process = api("CreateProcessW", wt.BOOL, wt.LPCWSTR, wt.LPWSTR, voidp, voidp,
                         wt.BOOL, wt.DWORD, voidp, wt.LPCWSTR, voidp, voidp)
    resume = api("ResumeThread", wt.DWORD, handle)
    wait = api("WaitForSingleObject", wt.DWORD, handle, wt.DWORD)
    exit_code = api("GetExitCodeProcess", wt.BOOL, handle, ct.POINTER(wt.DWORD))
    peek = api("PeekNamedPipe", wt.BOOL, handle, voidp, wt.DWORD, voidp, ct.POINTER(wt.DWORD), voidp)
    move = api("MoveFileExW", wt.BOOL, wt.LPCWSTR, wt.LPCWSTR, wt.DWORD)
    api("SetErrorMode", wt.UINT, wt.UINT)(0x0001 | 0x0002)

    def require(ok, operation):
        if not ok:
            raise OSError(ct.get_last_error(), operation)

    parent = Path(args.output_parent)
    if not parent.is_absolute() or parent.drive.startswith("\\\\") or any(p in (".", "..") for p in parent.parts):
        raise RuntimeError("output parent must be an absolute local directory")
    directories = []
    job = None
    process = ProcessInfo()
    read_fd = write_fd = input_fd = None
    temps = []
    assigned = False
    try:
        # Reject reparse points and hold every directory without FILE_SHARE_DELETE.
        # This prevents parent rename/replacement while real-path output is written.
        for directory in reversed((parent, *parent.parents)):
            value = attributes(str(directory))
            if value == 0xFFFFFFFF or not value & 0x10 or value & 0x400:
                raise RuntimeError("output parent contains a non-directory or reparse point")
            held = create_file(str(directory), 0x80, 0x1 | 0x2, None, 3, 0x02000000 | 0x00200000, None)
            if held == ct.c_void_p(-1).value:
                raise OSError(ct.get_last_error(), "lock output directory")
            directories.append(held)
            if attributes(str(directory)) & 0x400:
                raise RuntimeError("output parent changed to a reparse point")
        log_path, receipt_path = parent / args.log_leaf, parent / args.receipt_leaf
        if os.path.lexists(log_path) or os.path.lexists(receipt_path):
            raise RuntimeError("output collision")
        log_tmp = parent / f".{args.log_leaf}.tmp.{os.getpid()}"
        receipt_tmp = parent / f".{args.receipt_leaf}.tmp.{os.getpid()}"
        with open(log_tmp, "xb", buffering=0) as log:
            temps.append(log_tmp)
            job = create_job(None, None)
            require(job, "create job")
            limits = ExtendedLimit()
            limits.basic.flags = 0x2000  # JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE; no breakaway.
            require(set_job(job, 9, ct.byref(limits), ct.sizeof(limits)), "set kill-on-close")
            read_fd, write_fd = os.pipe()
            input_fd = os.open(os.devnull, os.O_RDONLY)
            os.set_inheritable(write_fd, True)
            os.set_inheritable(input_fd, True)
            startup = StartupInfo()
            startup.cb = ct.sizeof(startup)
            startup.flags = 0x100  # STARTF_USESTDHANDLES
            startup.stdin = msvcrt.get_osfhandle(input_fd)
            startup.stdout = startup.stderr = msvcrt.get_osfhandle(write_fd)
            command_line = ct.create_unicode_buffer(subprocess.list2cmdline(command))
            environment_block = ct.create_unicode_buffer(environment_text) if environment_text is not None else None
            reason, raw_status, native_status = "exec-failure", 127, "not-run"
            spawned = create_process(None, command_line, None, None, True,
                                     0x00000004 | 0x08000000 | 0x00000400, environment_block, None,
                                     ct.byref(startup), ct.byref(process))
            if spawned:
                # Failure leaves a suspended child, terminated by the finally block.
                require(assign(job, process.process), "assign suspended child to job")
                assigned = True
                if resume(process.thread) == 0xFFFFFFFF:
                    raise OSError(ct.get_last_error(), "resume assigned child")
                close(process.thread)
                process.thread = None
            os.close(write_fd)
            write_fd = None
            os.close(input_fd)
            input_fd = None
            captured = 0
            log_hash = hashlib.sha256()
            deadline = time.monotonic() + args.timeout_seconds
            read_handle = msvcrt.get_osfhandle(read_fd)
            eof = False

            def active_processes():
                accounting = Accounting()
                require(query_job(job, 1, ct.byref(accounting), ct.sizeof(accounting), None), "query job")
                return accounting.active

            while spawned:
                available = wt.DWORD()
                if not peek(read_handle, None, 0, None, ct.byref(available), None):
                    if ct.get_last_error() != 109:  # ERROR_BROKEN_PIPE is EOF.
                        raise OSError(ct.get_last_error(), "peek output pipe")
                    eof = True
                if available.value:
                    chunk = os.read(read_fd, min(65536, available.value))
                    kept = chunk[:args.max_bytes - captured]
                    log.write(kept)
                    log_hash.update(kept)
                    captured += len(kept)
                    if len(kept) < len(chunk):
                        reason, raw_status = "overflow", 125
                        break
                if eof and not active_processes():
                    native = wt.DWORD()
                    require(exit_code(process.process, ct.byref(native)), "read child exit")
                    native_status = native.value
                    reason = "child-native-exception" if native.value & 0xC0000000 == 0xC0000000 else "child-exit"
                    raw_status = native.value if native.value <= 255 else {
                        0xC0000005: 139, 0xC000001D: 132, 0xC0000094: 136, 0xC00000FD: 139
                    }.get(native.value, 125 if reason == "child-native-exception" else 1)
                    break
                if time.monotonic() >= deadline:
                    reason, raw_status = "timeout", 124
                    break
                if not available.value:
                    time.sleep(0.01)
            if spawned and reason in ("timeout", "overflow"):
                require(terminate_job(job, raw_status), "terminate bounded job")
                cleanup_deadline = time.monotonic() + 10
                while active_processes():
                    if time.monotonic() >= cleanup_deadline:
                        raise RuntimeError("job cleanup deadline")
                    time.sleep(0.01)
                if wait(process.process, 1000) != 0:
                    raise RuntimeError("root reap deadline")
                native = wt.DWORD()
                require(exit_code(process.process, ct.byref(native)), "read terminated child exit")
                native_status = native.value
            os.fsync(log.fileno())
        if digest(helper) != args.helper_sha256:
            raise RuntimeError("collector helper mutated during execution")
        # No MOVEFILE_REPLACE_EXISTING: a collision fails atomically. Same-volume
        # temporary + MOVEFILE_WRITE_THROUGH retains the log if receipt publication fails.
        require(move(str(log_tmp), str(log_path), 0x8), "publish log without replacement")
        values = {
            "schema": "simple-bounded-process-log-v1", "status": "complete",
            "reason": reason, "raw_status": raw_status, "native_exit_status": native_status,
            "max_bytes": args.max_bytes, "bytes_captured": captured,
            "timeout_seconds": args.timeout_seconds, "term_grace_seconds": args.term_grace_seconds,
            "combined_stream": "stdout-stderr", "process_group": "windows-job",
            "termination": "job-terminate", "artifact_limit": "none",
            "log_leaf": args.log_leaf, "log_sha256": log_hash.hexdigest(),
            "helper_sha256": args.helper_sha256,
            "command_environment": args.command_environment,
            "environment_sha256": hashlib.sha256(environment_text.encode("utf-16-le")).hexdigest() if environment_text is not None else "inherited",
        }
        with open(receipt_tmp, "xb", buffering=0) as receipt:
            temps.append(receipt_tmp)
            receipt.write("".join(f"{key}={value}\n" for key, value in values.items()).encode("ascii"))
            os.fsync(receipt.fileno())
        require(move(str(receipt_tmp), str(receipt_path), 0x8), "publish receipt without replacement")
        return raw_status
    finally:
        if process.process and not assigned:
            terminate_process(process.process, 126)
            wait(process.process, 1000)
        if job:
            close(job)  # Last non-inherited job handle: all remaining descendants die.
        for held in (process.thread, process.process):
            if held:
                close(held)
        for descriptor in (write_fd, read_fd, input_fd):
            if descriptor is not None:
                os.close(descriptor)
        for path in temps:
            path.unlink(missing_ok=True)
        for held in reversed(directories):
            close(held)


if __name__ == "__main__":
    try:
        sys.exit(main())
    except (OSError, RuntimeError, KeyboardInterrupt) as error:
        print(f"bounded-log-error: {error}", file=sys.stderr)
        sys.exit(126)
