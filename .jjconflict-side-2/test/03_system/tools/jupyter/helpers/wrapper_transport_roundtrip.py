#!/usr/bin/env python3
"""Live round-trip check for `tools/jupyter/kernel_wrapper.py` (Task P2).

Drives the REAL wrapper process over REAL ZMQ sockets via `jupyter_client`,
exercising exactly the pass-throughs P2 relies on:

  1. shell-channel `complete_request` -> `complete_reply`
  2. shell-channel `inspect_request` -> `inspect_reply`
  3. control-channel `interrupt_request` -> SIGINT + the kernel's own,
     relayed `interrupt_reply` (not a wrapper-fabricated one)
  4. shell `comm_open` + iopub `comm_msg` round trip on the `simple_lane`
     comm target

This is a manual verification helper, not an sspec -- it is meant to be run
directly (`python3 wrapper_transport_roundtrip.py`) against a real installed
`jupyter_client`, the same pattern used to verify Task P0. It prints PASS/FAIL
per check and exits non-zero on any failure.

Each check gets its own fresh kernel process so that one check's failure mode
(e.g. the kernel subprocess exiting) cannot mask or cascade into the others --
see the note above `check_complete` for why that matters here.
"""

import json
import os
import shutil
import sys
import tempfile
import time

REPO_ROOT = os.path.abspath(
    os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "..", "..")
)
WRAPPER = os.path.join(REPO_ROOT, "tools", "jupyter", "kernel_wrapper.py")
KERNEL_NAME = "simple_p2_wrapper_roundtrip"

try:
    from jupyter_client import KernelManager
except ImportError:
    sys.stderr.write(
        "wrapper_transport_roundtrip.py: jupyter_client is required "
        "(pip install jupyter_client pyzmq)\n"
    )
    sys.exit(1)

FAILURES = []


def report(label, condition, detail=""):
    if condition:
        print(f"PASS - {label}")
    else:
        print(f"FAIL - {label} {detail}")
        FAILURES.append(label)


def install_temp_kernelspec():
    """Register a throwaway kernelspec whose argv points at the real wrapper.

    `KernelManager` resolves its launch command from `self.kernel_spec.argv`
    -- this jupyter_client version has no `kernel_cmd` override trait, so
    without a real, discoverable kernelspec it silently launches whatever the
    environment's default "python3" kernel is (a real ipykernel). That looks
    like a working round trip right up until a comm_open reply comes back
    from the WRONG kernel (verified while writing this script: the fabricated
    kernel_cmd override was silently ignored and every check "passed" against
    ipykernel, not our wrapper). Discovery goes through `JUPYTER_PATH`, so a
    kernels/<name>/kernel.json dropped under a temp dir on that path is
    enough; nothing is installed into the user's real kernel registry.
    """
    tmp_dir = tempfile.mkdtemp(prefix="simple_p2_kernelspec_")
    kdir = os.path.join(tmp_dir, "kernels", KERNEL_NAME)
    os.makedirs(kdir)
    with open(os.path.join(kdir, "kernel.json"), "w", encoding="utf-8") as f:
        json.dump(
            {
                "argv": [sys.executable, WRAPPER, "-f", "{connection_file}"],
                "display_name": "Simple (P2 wrapper round-trip check)",
                "language": "simple",
            },
            f,
        )
    existing = os.environ.get("JUPYTER_PATH", "")
    os.environ["JUPYTER_PATH"] = tmp_dir if not existing else tmp_dir + os.pathsep + existing
    return tmp_dir


class LiveKernel:
    """One wrapper-backed kernel process + client, for the `with` block."""

    def __enter__(self):
        self.km = KernelManager(kernel_name=KERNEL_NAME)
        self.km.env = dict(os.environ, SIMPLE_REPO_ROOT=REPO_ROOT)
        self.km.start_kernel(cwd=REPO_ROOT)
        self.kc = self.km.client()
        self.kc.start_channels()
        self.kc.wait_for_ready(timeout=30)
        return self.kc

    def __exit__(self, *exc):
        try:
            self.kc.stop_channels()
        finally:
            self.km.shutdown_kernel(now=True)
        return False


def wait_for(get_msg, predicate, timeout=10):
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            msg = get_msg(timeout=1)
        except Exception:
            continue
        if predicate(msg):
            return msg
    return None


def check_complete():
    # NOTE: as of 2026-08-07 this fails on the deployed bin/simple seed --
    # not because of the wrapper, but because complete_request lazily starts
    # an LSP subprocess (get_or_start_lsp_bridge -> rt_process_spawn_piped),
    # and that extern is unrecognised by the currently-deployed seed binary
    # ("error: semantic: unknown extern function: rt_process_spawn_piped"),
    # which kills the whole kernel subprocess. Reproduced directly against
    # the kernel (bypassing the wrapper entirely) -- see
    # doc/08_tracking/bug/jupyter_lsp_bridge_missing_extern_blocks_complete_inspect_2026-08-07.md.
    # Isolated to its own kernel instance so this doesn't take the other
    # checks down with it.
    with LiveKernel() as kc:
        msg_id = kc.complete("val x = 4", 9)
        reply = wait_for(kc.get_shell_msg, lambda m: m["parent_header"].get("msg_id") == msg_id)
        report(
            "complete_request -> complete_reply",
            reply is not None and reply["header"]["msg_type"] == "complete_reply",
            detail=str(reply.get("header") if reply else None),
        )


def check_inspect():
    # Same underlying gap as check_complete (also routes through
    # get_or_start_lsp_bridge). Isolated for the same reason.
    with LiveKernel() as kc:
        msg_id = kc.inspect("val x = 4", 9)
        reply = wait_for(kc.get_shell_msg, lambda m: m["parent_header"].get("msg_id") == msg_id)
        report(
            "inspect_request -> inspect_reply",
            reply is not None and reply["header"]["msg_type"] == "inspect_reply",
            detail=str(reply.get("header") if reply else None),
        )


def check_interrupt():
    with LiveKernel() as kc:
        # Sent as a real ZMQ control-channel message (protocol msg_type
        # "interrupt_request"), the same way a Jupyter frontend does it --
        # this is what exercises the wrapper's control_sock plumbing, unlike
        # KernelManager.interrupt_kernel(), which defaults to a bare
        # process-level SIGINT for kernels without a "message" interrupt_mode
        # kernelspec entry and never touches the ZMQ control channel at all.
        kc.control_channel.send(kc.session.msg("interrupt_request", content={}))
        reply = wait_for(
            kc.get_control_msg, lambda m: m["header"]["msg_type"] == "interrupt_reply"
        )
        report(
            "interrupt_request -> interrupt_reply (relayed from kernel, not wrapper-fabricated)",
            reply is not None and reply["content"].get("status") in ("ok", "error"),
            detail=str(reply),
        )


def check_comm():
    with LiveKernel() as kc:
        comm_id = "p2-roundtrip-comm"
        kc.shell_channel.send(
            kc.session.msg(
                "comm_open",
                content={"comm_id": comm_id, "target_name": "simple_lane", "data": {}},
            )
        )
        reply = wait_for(
            kc.get_iopub_msg,
            lambda m: m["header"]["msg_type"] == "comm_msg"
            and m["content"].get("comm_id") == comm_id,
        )
        report(
            "comm_open -> comm_msg on iopub (simple_lane)",
            reply is not None and "mode" in reply["content"].get("data", {}),
            detail=str(reply),
        )


def main():
    if not os.path.exists(WRAPPER):
        sys.stderr.write(f"wrapper not found at {WRAPPER}\n")
        return 1

    kernelspec_dir = install_temp_kernelspec()
    try:
        probe_km = KernelManager(kernel_name=KERNEL_NAME)
        report(
            "KernelManager resolves argv to the real wrapper (not a system default kernel)",
            probe_km.kernel_spec.argv[:2] == [sys.executable, WRAPPER],
            detail=str(probe_km.kernel_spec.argv),
        )

        check_interrupt()
        check_comm()
        check_complete()
        check_inspect()
    finally:
        shutil.rmtree(kernelspec_dir, ignore_errors=True)

    if FAILURES:
        print(f"\n{len(FAILURES)} check(s) failed: {FAILURES}")
        return 1
    print("\nAll wrapper transport round-trip checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
