#!/usr/bin/env python3
"""Live stdio smoke test for the Simple editor DAP adapter."""

import json
import os
import subprocess
import tempfile
from pathlib import Path

SIMPLE_BIN = os.environ.get("SIMPLE_BIN", "bin/simple")


def frame(payload):
    body = json.dumps(payload, separators=(",", ":")).encode()
    return b"Content-Length: " + str(len(body)).encode() + b"\r\n\r\n" + body


def read_message(proc):
    headers = {}
    while True:
        line = proc.stdout.readline()
        if line == b"":
            raise AssertionError("adapter closed stdout")
        if line in (b"\r\n", b"\n"):
            break
        name, value = line.decode().split(":", 1)
        headers[name.lower()] = value.strip()
    body = proc.stdout.read(int(headers["content-length"]))
    return json.loads(body.decode())


def send(proc, seq, command, arguments=None):
    payload = {"seq": seq, "type": "request", "command": command}
    if arguments is not None:
        payload["arguments"] = arguments
    proc.stdin.write(frame(payload))
    proc.stdin.flush()


def expect_response(messages, command):
    for message in messages:
        if message.get("type") == "response" and message.get("command") == command:
            if not message.get("success"):
                raise AssertionError(f"{command} failed: {message}")
            return message
    raise AssertionError(f"missing response for {command}: {messages}")


def expect_failed_response(messages, command):
    for message in messages:
        if message.get("type") == "response" and message.get("command") == command:
            if message.get("success"):
                raise AssertionError(f"{command} unexpectedly succeeded: {message}")
            return message
    raise AssertionError(f"missing failed response for {command}: {messages}")


def collect_for(proc, command, count):
    messages = [read_message(proc) for _ in range(count)]
    return expect_response(messages, command), messages


def assert_missing_program_fails():
    proc = subprocess.Popen(
        [SIMPLE_BIN, "run", "src/app/dap/simple_dap_main.spl"],
        stdin=subprocess.PIPE,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    try:
        send(proc, 1, "initialize", {"adapterID": "simple"})
        collect_for(proc, "initialize", 2)
        send(proc, 2, "launch", {"program": "/tmp/simple_dap_missing_program.spl"})
        failed = expect_failed_response([read_message(proc)], "launch")
        assert "program not found" in failed.get("message", "")
        send(proc, 3, "disconnect")
        expect_response([read_message(proc)], "disconnect")
        proc.stdin.close()
        proc.wait(timeout=5)
    finally:
        if proc.poll() is None:
            proc.kill()


def main():
    with tempfile.TemporaryDirectory() as td:
        program = Path(td) / "main.spl"
        program.write_text(
            "fn main() -> i64:\n"
            "    val answer = 42\n"
            "    var status = \"ready\"\n"
            "    answer\n"
            "    panic(\"boom\")\n",
            encoding="utf-8",
        )
        proc = subprocess.Popen(
            [SIMPLE_BIN, "run", "src/app/dap/simple_dap_main.spl"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            send(proc, 1, "initialize", {"adapterID": "simple"})
            init, init_messages = collect_for(proc, "initialize", 2)
            assert init["body"]["supportsConfigurationDoneRequest"] is True
            filters = {item["filter"] for item in init["body"]["exceptionBreakpointFilters"]}
            assert {"caught", "uncaught"}.issubset(filters)
            assert any(m.get("event") == "initialized" for m in init_messages)

            send(proc, 2, "launch", {"program": str(program), "stopOnEntry": True})
            _, launch_messages = collect_for(proc, "launch", 2)
            assert any(m.get("event") == "stopped" for m in launch_messages)

            send(proc, 3, "setBreakpoints", {"source": {"path": str(program)}, "breakpoints": [{"line": 2, "condition": "answer == 42"}]})
            bp, _ = collect_for(proc, "setBreakpoints", 1)
            assert bp["body"]["breakpoints"][0]["verified"] is True
            assert bp["body"]["breakpoints"][0]["line"] == 2
            assert "condition" in bp["body"]["breakpoints"][0]["message"]

            send(proc, 12, "setExceptionBreakpoints", {"filters": ["caught", "uncaught"]})
            expect_response([read_message(proc)], "setExceptionBreakpoints")

            send(proc, 10, "setBreakpoints", {"source": {"path": str(program)}, "breakpoints": [{"line": 999}]})
            bad_bp, _ = collect_for(proc, "setBreakpoints", 1)
            assert bad_bp["body"]["breakpoints"][0]["verified"] is False
            assert bad_bp["body"]["breakpoints"][0]["line"] == 999

            send(proc, 4, "threads")
            threads, _ = collect_for(proc, "threads", 1)
            assert threads["body"]["threads"][0]["name"] == "main"

            send(proc, 5, "stackTrace", {"threadId": 1})
            stack, _ = collect_for(proc, "stackTrace", 1)
            frame0 = stack["body"]["stackFrames"][0]
            assert frame0["name"] == "main"
            assert frame0["source"]["path"] == str(program)
            assert frame0["line"] == 1

            send(proc, 13, "continue", {"threadId": 1})
            _, conditional_messages = collect_for(proc, "continue", 3)
            assert any(m.get("event") == "stopped" and m.get("body", {}).get("reason") == "breakpoint" for m in conditional_messages)
            send(proc, 14, "stackTrace", {"threadId": 1})
            conditional_stack, _ = collect_for(proc, "stackTrace", 1)
            assert conditional_stack["body"]["stackFrames"][0]["line"] == 2

            send(proc, 15, "next", {"threadId": 1})
            _, next_messages = collect_for(proc, "next", 2)
            assert any(m.get("event") == "stopped" for m in next_messages)
            send(proc, 16, "stackTrace", {"threadId": 1})
            stepped_stack, _ = collect_for(proc, "stackTrace", 1)
            assert stepped_stack["body"]["stackFrames"][0]["line"] == 3

            send(proc, 17, "setBreakpoints", {"source": {"path": str(program)}, "breakpoints": [{"line": 4, "hitCondition": "1"}]})
            bp2, _ = collect_for(proc, "setBreakpoints", 1)
            assert bp2["body"]["breakpoints"][0]["verified"] is True
            assert bp2["body"]["breakpoints"][0]["line"] == 4
            assert "hit" in bp2["body"]["breakpoints"][0]["message"]

            send(proc, 18, "continue", {"threadId": 1})
            _, continue_messages = collect_for(proc, "continue", 3)
            assert any(m.get("event") == "continued" for m in continue_messages)
            assert any(m.get("event") == "stopped" and m.get("body", {}).get("reason") == "breakpoint" for m in continue_messages)
            send(proc, 19, "stackTrace", {"threadId": 1})
            breakpoint_stack, _ = collect_for(proc, "stackTrace", 1)
            assert breakpoint_stack["body"]["stackFrames"][0]["line"] == 4

            send(proc, 20, "continue", {"threadId": 1})
            _, exception_messages = collect_for(proc, "continue", 3)
            assert any(m.get("event") == "stopped" and m.get("body", {}).get("reason") == "exception" for m in exception_messages)
            send(proc, 21, "stackTrace", {"threadId": 1})
            exception_stack, _ = collect_for(proc, "stackTrace", 1)
            assert exception_stack["body"]["stackFrames"][0]["line"] == 5

            send(proc, 22, "continue", {"threadId": 1})
            _, terminated_messages = collect_for(proc, "continue", 3)
            assert any(m.get("event") == "terminated" for m in terminated_messages)

            send(proc, 6, "scopes", {"frameId": 1})
            scopes, _ = collect_for(proc, "scopes", 1)
            assert scopes["body"]["scopes"][0]["variablesReference"] == 1

            send(proc, 7, "variables", {"variablesReference": 1})
            variables, _ = collect_for(proc, "variables", 1)
            values = {v["name"]: v["value"] for v in variables["body"]["variables"]}
            assert values["answer"] == "42"
            assert values["status"] == "\"ready\""

            send(proc, 8, "evaluate", {"expression": "answer"})
            evaluated, _ = collect_for(proc, "evaluate", 1)
            assert evaluated["body"]["result"] == "42"

            send(proc, 11, "evaluate", {"expression": "missing_value"})
            missing_eval, _ = collect_for(proc, "evaluate", 1)
            assert missing_eval["body"]["result"] == "<unavailable>"

            send(proc, 23, "restart")
            _, restart_messages = collect_for(proc, "restart", 2)
            assert any(m.get("event") == "stopped" and m.get("body", {}).get("reason") == "entry" for m in restart_messages)
            send(proc, 24, "stackTrace", {"threadId": 1})
            restarted_stack, _ = collect_for(proc, "stackTrace", 1)
            assert restarted_stack["body"]["stackFrames"][0]["line"] == 1

            send(proc, 25, "terminate")
            _, terminate_messages = collect_for(proc, "terminate", 2)
            assert any(m.get("event") == "terminated" for m in terminate_messages)

            send(proc, 9, "disconnect")
            _, disconnect_messages = collect_for(proc, "disconnect", 2)
            assert any(m.get("event") == "terminated" for m in disconnect_messages)
            proc.stdin.close()
            rc = proc.wait(timeout=5)
            if rc != 0:
                raise AssertionError(f"adapter exit {rc}: {proc.stderr.read().decode(errors='replace')}")
        finally:
            if proc.poll() is None:
                proc.kill()
    assert_missing_program_fails()
    print("STATUS: PASS dap_protocol_smoke")


if __name__ == "__main__":
    main()
