#!/usr/bin/env python3
import os
import time

try:
    import renderdoc
except ImportError:
    pass


def env_int(name, fallback):
    value = os.environ.get(name, "")
    try:
        return int(value)
    except ValueError:
        return fallback


def append_line(path, key, value):
    with open(path, "a", encoding="utf-8") as f:
        f.write(f"{key}={value}\n")


def target_message_type_name(msg_type):
    try:
        return str(msg_type).split(".")[-1]
    except Exception:
        return str(msg_type)


out_path = os.environ.get("RDOC_TARGET_CONTROL_OUT", "build/renderdoc/target-control.env")
wanted_pid = env_int("RDOC_TARGET_CONTROL_PID", 0)
timeout_s = env_int("RDOC_TARGET_CONTROL_TIMEOUT_SECS", 20)
capture_out = os.environ.get("RDOC_TARGET_CONTROL_CAPTURE_OUT", "")
client_name = os.environ.get("RDOC_TARGET_CONTROL_CLIENT", "simple-renderdoc-target-control")

os.makedirs(os.path.dirname(out_path) or ".", exist_ok=True)
with open(out_path, "w", encoding="utf-8") as f:
    f.write("rdoc_target_control_status=running\n")
    f.write(f"rdoc_target_control_wanted_pid={wanted_pid}\n")
    f.write(f"rdoc_target_control_timeout_secs={timeout_s}\n")

idents = []
next_ident = 0
for _ in range(256):
    next_ident = renderdoc.EnumerateRemoteTargets("", next_ident)
    if next_ident == 0:
        break
    idents.append(next_ident)

append_line(out_path, "rdoc_target_control_ident_count", len(idents))
append_line(out_path, "rdoc_target_control_idents", "|".join(str(i) for i in idents))

chosen = None
chosen_ident = 0
for ident in idents:
    target = renderdoc.CreateTargetControl("", ident, client_name, True)
    if target is None:
        append_line(out_path, f"rdoc_target_control_ident_{ident}_connect", "fail")
        continue
    try:
        pid = target.GetPID()
        api = target.GetAPI()
        name = target.GetTarget()
        append_line(out_path, f"rdoc_target_control_ident_{ident}_pid", pid)
        append_line(out_path, f"rdoc_target_control_ident_{ident}_api", api)
        append_line(out_path, f"rdoc_target_control_ident_{ident}_target", name)
        if wanted_pid == 0 or pid == wanted_pid:
            chosen = target
            chosen_ident = ident
            break
    finally:
        if chosen is None:
            target.Shutdown()

if chosen is None:
    append_line(out_path, "rdoc_target_control_status", "fail")
    append_line(out_path, "rdoc_target_control_reason", "no-matching-target")
    os._exit(1)

append_line(out_path, "rdoc_target_control_chosen_ident", chosen_ident)
append_line(out_path, "rdoc_target_control_chosen_pid", chosen.GetPID())
append_line(out_path, "rdoc_target_control_chosen_api", chosen.GetAPI())
append_line(out_path, "rdoc_target_control_chosen_target", chosen.GetTarget())

new_capture_path = ""
new_capture_id = -1
new_capture_api = ""
try:
    chosen.TriggerCapture(1)
    append_line(out_path, "rdoc_target_control_trigger", "sent")
    deadline = time.time() + timeout_s
    while time.time() < deadline:
        msg = chosen.ReceiveMessage(None)
        msg_type = target_message_type_name(msg.type)
        append_line(out_path, "rdoc_target_control_message", msg_type)
        if msg.type == renderdoc.TargetControlMessageType.NewCapture:
            new_capture_path = msg.newCapture.path
            new_capture_id = msg.newCapture.captureId
            new_capture_api = msg.newCapture.api
            break
    if new_capture_path:
        append_line(out_path, "rdoc_target_control_capture_path", new_capture_path)
        append_line(out_path, "rdoc_target_control_capture_id", new_capture_id)
        append_line(out_path, "rdoc_target_control_capture_api", new_capture_api)
        if capture_out:
            chosen.CopyCapture(new_capture_id, capture_out)
            append_line(out_path, "rdoc_target_control_copy_requested", capture_out)
    else:
        append_line(out_path, "rdoc_target_control_status", "fail")
        append_line(out_path, "rdoc_target_control_reason", "no-new-capture-message")
        os._exit(1)
finally:
    chosen.Shutdown()

append_line(out_path, "rdoc_target_control_status", "pass")
append_line(out_path, "rdoc_target_control_reason", "pass")
os._exit(0)
