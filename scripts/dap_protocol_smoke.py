#!/usr/bin/env python3
"""Live stdio smoke test for the Simple editor DAP adapter."""

import json
import subprocess
import tempfile
from pathlib import Path


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


def collect_for(proc, command, count):
    messages = [read_message(proc) for _ in range(count)]
    return expect_response(messages, command), messages


def main():
    with tempfile.TemporaryDirectory() as td:
        program = Path(td) / "main.spl"
        program.write_text(
            "fn main() -> i64:\n"
            "    val answer = 42\n"
            "    var status = \"ready\"\n"
            "    answer\n",
            encoding="utf-8",
        )
        proc = subprocess.Popen(
            ["bin/simple", "run", "src/app/dap/simple_dap_main.spl"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        try:
            send(proc, 1, "initialize", {"adapterID": "simple"})
            init, init_messages = collect_for(proc, "initialize", 2)
            assert init["body"]["supportsConfigurationDoneRequest"] is True
            assert any(m.get("event") == "initialized" for m in init_messages)

            send(proc, 2, "launch", {"program": str(program), "stopOnEntry": True})
            _, launch_messages = collect_for(proc, "launch", 2)
            assert any(m.get("event") == "stopped" for m in launch_messages)

            send(proc, 3, "setBreakpoints", {"source": {"path": str(program)}, "breakpoints": [{"line": 2}]})
            bp, _ = collect_for(proc, "setBreakpoints", 1)
            assert bp["body"]["breakpoints"][0]["verified"] is True
            assert bp["body"]["breakpoints"][0]["line"] == 2

            send(proc, 4, "threads")
            threads, _ = collect_for(proc, "threads", 1)
            assert threads["body"]["threads"][0]["name"] == "main"

            send(proc, 5, "stackTrace", {"threadId": 1})
            stack, _ = collect_for(proc, "stackTrace", 1)
            frame0 = stack["body"]["stackFrames"][0]
            assert frame0["name"] == "main"
            assert frame0["source"]["path"] == str(program)

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

            send(proc, 9, "disconnect")
            expect_response([read_message(proc)], "disconnect")
            proc.stdin.close()
            rc = proc.wait(timeout=5)
            if rc != 0:
                raise AssertionError(f"adapter exit {rc}: {proc.stderr.read().decode(errors='replace')}")
        finally:
            if proc.poll() is None:
                proc.kill()
    print("STATUS: PASS dap_protocol_smoke")


if __name__ == "__main__":
    main()
