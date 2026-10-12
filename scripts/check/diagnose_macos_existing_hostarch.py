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
    def capture_child():
        # Exact SHA404042 facade ABI: x0=text, x1=[text], x2=deadline.
        spawn = symbol("src__lib__nogc_sync_mut__io__process_ops__process_run_timeout_live")
        frame = stop_at(spawn)
        command = bytes.fromhex(text(frame, frame.FindRegister("x0").GetValueAsUnsigned())["hex"]).decode("utf-8")
        raw = frame.FindRegister("x1").GetValueAsUnsigned()
        error = lldb.SBError()
        if raw & 7 != 1 or (raw & ~7) < 4096:
            raise RuntimeError("invalid worker argv tag")
        header = process.ReadMemory(raw & ~7, 32, error)
        if error.Fail() or len(header) != 32 or header[0] != 2 or header[1] & 0x18:
            raise RuntimeError("invalid worker argv array header")
        count = int.from_bytes(header[8:16], "little")
        capacity = int.from_bytes(header[16:24], "little")
        data = int.from_bytes(header[24:32], "little")
        if not 2 <= count <= 128 or capacity < count or data < 4096:
            raise RuntimeError("unbounded worker argv")
        elements = process.ReadMemory(data, count * 8, error)
        if error.Fail() or len(elements) != count * 8:
            raise RuntimeError("worker argv memory unavailable")
        argv = [bytes.fromhex(text(frame, int.from_bytes(elements[i:i+8], "little"))["hex"]).decode("utf-8") for i in range(0, len(elements), 8)]
        if command != os.environ["SIMPLE_BINARY"] or argv[:2] != ["run", "src/app/cli/native_build_worker.spl"]:
            raise RuntimeError("unexpected subprocess; refuse guessed child route")
        names = ["SIMPLE_SCV_SNAPSHOT_ROOT", "SIMPLE_SCV_REVISION_ID", "SIMPLE_SCV_COMMIT_ID", "SIMPLE_SCV_TREE_ID", "SIMPLE_SCV_INVENTORY_DIGEST", "SIMPLE_SCV_SOURCE_INVENTORY_DIGEST", "SIMPLE_SCV_INVENTORY_GENERATION", "SIMPLE_SCV_SOURCE_DRIFTED", "SIMPLE_NATIVE_BUILD_WORKER", "SIMPLE_FRONTEND_CACHE_DIR", "SIMPLE_ICE_DIR", "SIMPLE_ICE_SKIP_MODULES", "SIMPLE_NATIVE_BUILD_WARM_CLOSURE_CANDIDATE"]
        environment = []
        options = lldb.SBExpressionOptions()
        options.SetTimeoutInMicroSeconds(2000000)
        options.SetIgnoreBreakpoints(True)
        for name in names:
            value = frame.EvaluateExpression('(unsigned long long)getenv("%s")' % name, options)
            if value.GetError().Fail():
                raise RuntimeError("required environment accessor unavailable")
            pointer = value.GetValueAsUnsigned()
            if pointer:
                value_text = process.ReadCStringFromMemory(pointer, 4097, error)
                if error.Fail() or len(value_text.encode("utf-8")) > 4096:
                    raise RuntimeError("unbounded child authority environment")
                environment.append(name + "=" + value_text)
        env_map = dict(value.split("=", 1) for value in environment)
        if not env_map.get("SIMPLE_SCV_SNAPSHOT_ROOT") or env_map.get("SIMPLE_NATIVE_BUILD_WORKER") != "1":
            raise RuntimeError("child authority incomplete")
        evidence["child_handoff"] = {"command": command, "argv": argv, "environment": env_map, "cwd": os.getcwd(), "qualification": "UNADMITTED"}
        persist()
        kill_error = process.Kill()
        if kill_error.Fail() or process.GetState() != lldb.eStateExited:
            raise RuntimeError("coordinator termination not confirmed; refuse dual worker")
        # Explicit full inheritance: remove even absent captured keys before overlay.
        launch_environment = dict(os.environ)
        for name in names:
            launch_environment.pop(name, None)
        launch_environment.update(env_map)
        launch_environment.pop("_SIMPLE_STACK_SET", None)  # Frozen Rust spawn owner removes this.
        launch = lldb.SBLaunchInfo(argv)
        launch.SetWorkingDirectory(os.getcwd())
        launch.SetEnvironmentEntries([name + "=" + value for name, value in launch_environment.items()], False)
        launch.SetLaunchFlags(lldb.eLaunchFlagStopAtEntry)
        error = lldb.SBError()
        child = target.Launch(launch, error)
        if error.Fail() or not child.IsValid():
            raise RuntimeError("captured child launch failed")
        # Async Launch may return before its stop-at-entry event is published.
        # Consume that initial stop before bounded_continue records its stop ID.
        launch_listener = lldb.SBListener("hostarch-child-launch")
        child.GetBroadcaster().AddListener(launch_listener, lldb.SBProcess.eBroadcastBitStateChanged)
        deadline = time.monotonic() + 5
        while time.monotonic() < deadline:
            state = child.GetState()
            if state == lldb.eStateStopped and child.GetStopID() > 0:
                evidence["child_launch"] = {"state": "stopped-at-entry", "stop_id": child.GetStopID()}
                persist()
                return child
            if state in [lldb.eStateExited, lldb.eStateDetached]:
                raise RuntimeError("captured child terminated before entry stop")
            event = lldb.SBEvent()
            launch_listener.WaitForEvent(1, event)
        child.Kill()
        raise RuntimeError("captured child entry stop not confirmed")
    try:
        # Capture actual coordinator handoff, then debug its native child directly.
        process = capture_child()
        host = target.FindBreakpointByID(1)
        host_address = symbol(PREFIX + "host_arch")
        if not host.IsValid() or host.GetNumResolvedLocations() != 1 or host.GetLocationAtIndex(0).GetAddress().GetLoadAddress(target) != host_address:
            raise RuntimeError("child host breakpoint relocation not confirmed")
        evidence["child_launch"]["host_breakpoint_load_address"] = host_address
        persist()
        host.SetEnabled(False)
        # SHA404042: exact linker guard call, not any earlier architecture query.
        linker = symbol("src__compiler__backend__linker___LinkerWrapper__native_linking__native_link_with_admitted_inputs_and_engine_v1")
        guard = stop_at(linker + 0x508)
        if guard.GetPC() != linker + 0x508:
            raise RuntimeError("specific linker host-query callsite not reached")
        evidence["link_guard"] = {"owner_load_address": linker, "call_load_address": guard.GetPC(), "expected_call_offset": 0x508}
        persist()
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
        if frame.GetPC() != linker + 0x50c:
            raise RuntimeError("host_arch did not return to exact linker guard")
        evidence["host_arch"] = text(frame, frame.FindRegister("x0").GetValueAsUnsigned())
        evidence["link_guard"]["return_load_address"] = frame.GetPC()
        persist()
        frame = stop_at(linker + 0x510)  # after mov x25,x0
        evidence["link_guard"]["arch_x25"] = text(frame, frame.FindRegister("x25").GetValueAsUnsigned())
        persist()
        frame = stop_at(linker + 0x51c)  # support predicate returned; cbz follows
        supported = frame.FindRegister("x0").GetValueAsUnsigned()
        if supported not in [0, 1]:
            raise RuntimeError("invalid linker support predicate result")
        evidence["link_guard"]["supported"] = supported
        if supported == 0:
            frame = stop_at(linker + 0x898)  # actual error formatter call
            evidence["link_guard"]["error_arch"] = text(frame, frame.FindRegister("x1").GetValueAsUnsigned())
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
