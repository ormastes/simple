"""Bounded read-only breakpoint inspection of one rejected immutable candidate."""
import json
import os
import lldb

PREFIX = "src__lib__nogc_sync_mut__io_runtime__"

def run(debugger):
    target = debugger.GetSelectedTarget()
    process = target.GetProcess()
    evidence = {"qualification": "UNADMITTED", "checkpoints": {}}
    def symbol(name):
        contexts = target.FindFunctions(name)
        if contexts.GetSize() != 1:
            raise RuntimeError("unresolved/ambiguous symbol: " + name)
        context = contexts.GetContextAtIndex(0)
        return context.GetSymbol().GetStartAddress().GetLoadAddress(target)
    def text(frame, raw):
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
        if not 0 <= length <= 4096 or (length and not address):
            raise RuntimeError("invalid or unbounded runtime string")
        error = lldb.SBError()
        data = process.ReadMemory(address, length, error) if length else b""
        if error.Fail():
            raise RuntimeError("runtime string read failed")
        return {"raw": raw, "length": length, "hex": data.hex()}
    def stop_at(address):
        breakpoint = target.BreakpointCreateByAddress(address)
        error = process.Continue()
        if error.Fail() or process.GetState() != lldb.eStateStopped or breakpoint.GetHitCount() != 1:
            raise RuntimeError("required boundary not reached; possible child escape")
        thread = process.GetSelectedThread()
        frame = thread.GetFrameAtIndex(0)
        target.BreakpointDelete(breakpoint.GetID())
        return frame
    try:
        # Workflow launches already stopped at the exact host_arch owner.
        host = target.FindBreakpointByID(1)
        if process.GetState() != lldb.eStateStopped or host.GetHitCount() != 1:
            raise RuntimeError("host_arch breakpoint not reached")
        host.SetEnabled(False)
        shell = symbol(PREFIX + "shell_output")
        frame = stop_at(shell)
        command = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        evidence["command"] = command
        if bytes.fromhex(command["hex"]) != b"uname -m":
            raise RuntimeError("host_arch did not call exact uname -m")
        # Offsets bound to verified SHA404042 disassembly, after actual getters.
        for label, offset in [("stdout", 0x70), ("stderr", 0x80), ("exit_code", 0x90)]:
            frame = stop_at(shell + offset)
            raw = frame.FindRegister("x0").GetValueAsUnsigned()
            evidence["checkpoints"][label] = frame.FindRegister("x0").GetValueAsSigned() if label == "exit_code" else text(frame, raw)
        # Return from actual shell_output, recording post-trim text.
        thread = process.GetSelectedThread()
        thread.StepOut()
        if process.GetState() != lldb.eStateStopped:
            raise RuntimeError("shell_output return not observed")
        frame = thread.GetFrameAtIndex(0)
        evidence["trimmed"] = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        thread.StepOut()
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
