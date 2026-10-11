"""Bounded read-only breakpoint inspection of one rejected immutable candidate."""
import json
import os
import time
import lldb

PREFIX = "src__lib__nogc_sync_mut__io_runtime__"

def run(debugger):
    target = debugger.GetSelectedTarget()
    process = target.GetProcess()
    evidence = {"qualification": "UNADMITTED", "capture": "INCOMPLETE", "checkpoints": {}}
    debugger.SetAsync(True)
    def persist():
        with open(os.environ["HOSTARCH_DIAGNOSTIC_RECEIPT"], "w") as output:
            json.dump(evidence, output, indent=2)
    def bounded_continue(seconds=30):
        listener = lldb.SBListener("hostarch-state")
        process.GetBroadcaster().AddListener(listener, lldb.SBProcess.eBroadcastBitStateChanged)
        prior_stop = process.GetStopID()
        error = process.Continue()
        if error.Fail():
            raise RuntimeError("debugger continue failed")
        deadline = time.monotonic() + seconds
        while time.monotonic() < deadline:
            event = lldb.SBEvent()
            if listener.WaitForEvent(1, event):
                state = lldb.SBProcess.GetStateFromEvent(event)
                if state == lldb.eStateStopped and process.GetStopID() != prior_stop:
                    return state
                if state in [lldb.eStateExited, lldb.eStateDetached]:
                    return state
        process.Stop()
        stop_deadline = time.monotonic() + 3
        while time.monotonic() < stop_deadline:
            if process.GetState() == lldb.eStateStopped and process.GetStopID() != prior_stop:
                evidence["timeout_stack"] = [[str(frame) for frame in list(thread)[:12]] for thread in process]
                persist()
                raise RuntimeError("bounded debugger timeout before requested boundary")
            time.sleep(0.1)
        evidence["timeout_stack_unavailable"] = "process did not confirm a new stop"
        persist()
        raise RuntimeError("bounded debugger timeout; interrupt failed")
    def symbol(name):
        contexts = target.FindFunctions(name)
        if contexts.GetSize() != 1:
            raise RuntimeError("unresolved/ambiguous symbol: " + name)
        context = contexts.GetContextAtIndex(0)
        owner = context.GetFunction()
        address = owner.GetStartAddress() if owner.IsValid() else context.GetSymbol().GetStartAddress()
        loaded = address.GetLoadAddress(target)
        if not address.IsValid() or loaded == lldb.LLDB_INVALID_ADDRESS:
            raise RuntimeError("invalid symbol load address: " + name)
        return loaded
    def text(frame, raw):
        # Frozen5e repr: TAG_HEAP=1/mask7, HeapHeader8B, Stringtype1.
        if raw & 7 != 1 or (raw & ~7) < 4096:
            raise RuntimeError("value is not a tagged heap string")
        header_error = lldb.SBError()
        header = process.ReadMemory(raw & ~7, 24, header_error)
        if header_error.Fail() or len(header) != 24 or header[0] != 1:
            raise RuntimeError("invalid runtime string header")
        declared_length = int.from_bytes(header[8:16], "little")
        object_size = int.from_bytes(header[4:8], "little")
        if declared_length > 4096 or object_size < 24 + declared_length:
            raise RuntimeError("invalid bounded runtime string extent")
        options = lldb.SBExpressionOptions()
        options.SetTimeoutInMicroSeconds(2000000)
        options.SetIgnoreBreakpoints(True)
        length_address = symbol("rt_string_len")
        data_address = symbol("rt_string_data")
        length_value = frame.EvaluateExpression("((long long(*)(unsigned long long))%d)(%d)" % (length_address, raw), options)
        data_value = frame.EvaluateExpression("((unsigned long long(*)(unsigned long long))%d)(%d)" % (data_address, raw), options)
        if length_value.GetError().Fail() or data_value.GetError().Fail():
            raise RuntimeError("runtime string getter unavailable")
        length = length_value.GetValueAsSigned()
        address = data_value.GetValueAsUnsigned()
        if length != declared_length or address != (raw & ~7) + 24:
            raise RuntimeError("invalid or unbounded runtime string")
        error = lldb.SBError()
        data = process.ReadMemory(address, length, error) if length else b""
        if error.Fail():
            raise RuntimeError("runtime string read failed")
        return {"raw": raw, "length": length, "hex": data.hex()}
    def stop_at(address):
        breakpoint = target.BreakpointCreateByAddress(address)
        bounded_continue()
        if process.GetState() != lldb.eStateStopped or breakpoint.GetHitCount() != 1:
            raise RuntimeError("required boundary not reached; possible child escape")
        thread = process.GetSelectedThread()
        frame = thread.GetFrameAtIndex(0)
        target.BreakpointDelete(breakpoint.GetID())
        return frame
    try:
        # Workflow launches stopped at executable entry; wait for the actual host owner.
        host = target.FindBreakpointByID(1)
        bounded_continue(70)
        if process.GetState() != lldb.eStateStopped or host.GetHitCount() != 1:
            raise RuntimeError("host_arch breakpoint not reached")
        host.SetEnabled(False)
        shell = symbol(PREFIX + "shell_output")
        frame = stop_at(shell)
        command = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        evidence["command"] = command
        persist()
        if bytes.fromhex(command["hex"]) != b"uname -m":
            raise RuntimeError("host_arch did not call exact uname -m")
        # Offsets bound to verified SHA404042 disassembly, after actual getters.
        for label, offset in [("stdout", 0x70), ("stderr", 0x80), ("exit_code", 0x90)]:
            frame = stop_at(shell + offset)
            raw = frame.FindRegister("x0").GetValueAsUnsigned()
            evidence["checkpoints"][label] = frame.FindRegister("x0").GetValueAsSigned() if label == "exit_code" else text(frame, raw)
            persist()
        # Return from actual shell_output, recording post-trim text.
        thread = process.GetSelectedThread()
        debugger.SetAsync(False)
        thread.StepOut()
        debugger.SetAsync(True)
        if process.GetState() != lldb.eStateStopped:
            raise RuntimeError("shell_output return not observed")
        frame = thread.GetFrameAtIndex(0)
        evidence["trimmed"] = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        persist()
        debugger.SetAsync(False)
        thread.StepOut()
        debugger.SetAsync(True)
        if process.GetState() != lldb.eStateStopped:
            raise RuntimeError("host_arch return not observed")
        frame = thread.GetFrameAtIndex(0)
        evidence["host_arch"] = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        evidence["capture"] = "COMPLETE"
    except Exception as error:
        evidence["capture"] = "INCOMPLETE"
        evidence["error"] = str(error)
    finally:
        with open(os.environ["HOSTARCH_DIAGNOSTIC_RECEIPT"], "w") as output:
            json.dump(evidence, output, indent=2)
        if process.IsValid() and process.GetState() not in [lldb.eStateExited, lldb.eStateDetached]:
            process.Kill()
        print("host query diagnostic capture=" + evidence.get("capture", "INCOMPLETE"))
