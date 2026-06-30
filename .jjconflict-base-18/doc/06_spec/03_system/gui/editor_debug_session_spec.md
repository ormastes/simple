# Editor Debug Session Specification

> <details>

<!-- sdn-diagram:id=editor_debug_session_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=editor_debug_session_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

editor_debug_session_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=editor_debug_session_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Editor Debug Session Specification

## Scenarios

### editor debug session model

#### parses VSCode-style launch configuration fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"Run current file\",\"type\":\"simple\",\"request\":\"launch\",\"program\":\"src/main.spl\",\"cwd\":\"/repo\",\"args\":[\"--mode\",\"interpreter\"],\"preLaunchTask\":\"build-simple\",\"env\":{\"SIMPLE_LIB\":\"" + r"${workspaceFolder}" + "/src\",\"MODE\":\"debug\"}}"
val config = editor_debug_launch_config_from_json(json)
expect(config.name).to_equal("Run current file")
expect(config.debug_type).to_equal("simple")
expect(config.request).to_equal("launch")
expect(config.program).to_equal("src/main.spl")
expect(config.cwd).to_equal("/repo")
expect(config.args.len()).to_equal(2)
expect(config.args[0]).to_equal("--mode")
expect(config.pre_launch_task).to_equal("build-simple")
expect(config.env.len()).to_equal(2)
expect(config.env[0].key).to_equal("SIMPLE_LIB")
expect(config.env[0].value).to_equal(r"${workspaceFolder}" + "/src")
```

</details>

#### selects matching configurations from VSCode launch.json files

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\":\"0.2.0\",\"configurations\":[{\"name\":\"Run JS\",\"type\":\"node\",\"request\":\"launch\",\"program\":\"app.js\"},{\"name\":\"Run Simple\",\"type\":\"simple\",\"request\":\"launch\",\"program\":\"src/main.spl\",\"args\":[\"--debug\"]}]}"
val configs = editor_debug_launch_configs_from_json(json)
expect(configs.len()).to_equal(2)
expect(configs[0].name).to_equal("Run JS")
expect(configs[1].debug_type).to_equal("simple")

val selected = editor_debug_select_launch_config(json, "simple", "fallback.spl")
expect(selected.name).to_equal("Run Simple")
expect(selected.program).to_equal("src/main.spl")
expect(selected.args[0]).to_equal("--debug")
```

</details>

#### parses VSCode compound launch configurations

<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"version\":\"0.2.0\",\"configurations\":[{\"name\":\"API\",\"type\":\"simple\",\"request\":\"launch\",\"program\":\"api.spl\"},{\"name\":\"Worker\",\"type\":\"simple\",\"request\":\"launch\",\"program\":\"worker.spl\"}],\"compounds\":[{\"name\":\"All\",\"configurations\":[\"API\",\"Worker\"],\"preLaunchTask\":\"build all\"}]}"
val compounds = editor_debug_compound_configs_from_json(json)
expect(compounds.len()).to_equal(1)
expect(editor_debug_compound_config_name(compounds[0])).to_equal("All")
expect(editor_debug_compound_config_member_names(compounds[0])[0]).to_equal("API")
expect(editor_debug_compound_config_member_names(compounds[0])[1]).to_equal("Worker")
val launch_config = editor_debug_compound_as_launch_config(compounds[0])
expect(editor_debug_launch_config_is_compound(launch_config)).to_equal(true)
expect(launch_config.program).to_equal("API|Worker")
expect(launch_config.pre_launch_task).to_equal("build all")
```

</details>

#### resolves VSCode launch variables against workspace and active file

1. env: [EditorDebugEnv
   - Expected: resolved.program equals `/repo/src/main.spl`
   - Expected: resolved.cwd equals `/repo`
   - Expected: resolved.args[0] equals `/repo/src`
   - Expected: resolved.args[1] equals `main.spl`
   - Expected: resolved.args[2] equals `/repo/build`
   - Expected: resolved.pre_launch_task equals `build main.spl`
   - Expected: resolved.env[0].value equals `/repo/src`
   - Expected: dap_args contains `"args":["/repo/src","main.spl","/repo/build"]`
   - Expected: dap_args contains `"preLaunchTask":"build main.spl"`
   - Expected: dap_args contains `"env":{"SIMPLE_LIB":"/repo/src"}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val config = EditorDebugLaunchConfig(
    name: "Vars",
    debug_type: "simple",
    request: "launch",
    program: r"${file}",
    cwd: r"${workspaceFolder}",
    args: [r"${fileDirname}", r"${fileBasename}", r"${workspaceFolder}/build"],
    pre_launch_task: r"build ${fileBasename}",
    env: [EditorDebugEnv(key: "SIMPLE_LIB", value: r"${workspaceFolder}/src")]
)
val resolved = editor_debug_resolve_launch_config(config, "/repo", "/repo/src/main.spl")

expect(resolved.program).to_equal("/repo/src/main.spl")
expect(resolved.cwd).to_equal("/repo")
expect(resolved.args[0]).to_equal("/repo/src")
expect(resolved.args[1]).to_equal("main.spl")
expect(resolved.args[2]).to_equal("/repo/build")
expect(resolved.pre_launch_task).to_equal("build main.spl")
expect(resolved.env[0].value).to_equal("/repo/src")
val dap_args = editor_debug_launch_config_dap_arguments(resolved)
expect(dap_args.contains("\"args\":[\"/repo/src\",\"main.spl\",\"/repo/build\"]")).to_equal(true)
expect(dap_args.contains("\"preLaunchTask\":\"build main.spl\"")).to_equal(true)
expect(dap_args.contains("\"env\":{\"SIMPLE_LIB\":\"/repo/src\"}")).to_equal(true)
```

</details>

#### tracks sessions breakpoints conditions hit counts and watches

1. var registry = editor debug registry new
2. registry = editor debug registry start
   - Expected: editor_debug_session_count(registry) equals `1`
   - Expected: session.status equals `starting`
   - Expected: editor_debug_session_summary(session) equals `starting simple src/main.spl`
3. registry = editor debug add breakpoint
4. registry = editor debug add watch
   - Expected: with_state.breakpoints.len() equals `1`
   - Expected: with_state.breakpoints[0].condition equals `x > 3`
   - Expected: with_state.breakpoints[0].log_message equals `log x`
   - Expected: with_state.breakpoints[0].hit_condition equals `5`
   - Expected: with_state.watches.len() equals `1`
   - Expected: with_state.watches[0].expression equals `x + y`
5. registry = editor debug evaluate
6. registry = editor debug console append
7. registry = editor debug set exception filters
   - Expected: with_console.console.len() equals `2`
   - Expected: with_console.console[0].kind equals `evaluate`
   - Expected: with_console.console[0].text_content equals `x + y`
   - Expected: with_console.exception_filters.len() equals `2`
   - Expected: with_console.exception_filters[1] equals `uncaught`
8. registry = editor debug update watch
9. registry = editor debug evaluate result
   - Expected: with_results.watches[0].last_value equals `42`
   - Expected: with_results.watches[0].status equals `ok`
   - Expected: with_results.console[with_results.console.len() - 1].kind equals `evaluate-result`
   - Expected: with_results.console[with_results.console.len() - 1].text_content equals `x + y = 42`
10. EditorDebugStackFrame
11. EditorDebugScope
12. EditorDebugVariable
   - Expected: with_debug_tree.stack_frames.len() equals `1`
   - Expected: with_debug_tree.stack_frames[0].name equals `main`
   - Expected: with_debug_tree.scopes.len() equals `1`
   - Expected: with_debug_tree.scopes[0].name equals `Locals`
   - Expected: with_debug_tree.scopes[0].variables[0].name equals `answer`
   - Expected: with_debug_tree.scopes[0].variables[0].value equals `42`
13. registry = editor debug continue
   - Expected: editor_debug_first_session(registry).status equals `running`
14. registry = editor debug pause
   - Expected: editor_debug_first_session(registry).status equals `paused`
15. registry = editor debug step
   - Expected: editor_debug_first_session(registry).status equals `stepping`
16. registry = editor debug enable breakpoint
   - Expected: editor_debug_first_session(registry).breakpoints[0].enabled is false
17. registry = editor debug registry terminate
   - Expected: editor_debug_first_session(registry).status equals `terminated`
18. registry = editor debug registry restart
   - Expected: editor_debug_first_session(registry).status equals `restarting`
   - Expected: restarted.console[restarted.console.len() - 1].text_content equals `restart`


<details>
<summary>Executable SSpec</summary>

Runnable source: 70 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var registry = editor_debug_registry_new()
registry = editor_debug_registry_start(registry, editor_debug_launch_config_default("src/main.spl"))
expect(editor_debug_session_count(registry)).to_equal(1)

val session = editor_debug_first_session(registry)
expect(session.status).to_equal("starting")
expect(editor_debug_session_summary(session)).to_equal("starting simple src/main.spl")

registry = editor_debug_add_breakpoint(registry, session.id, "src/main.spl", 12, "x > 3", "log x", "5")
registry = editor_debug_add_watch(registry, session.id, "x + y")
val with_state = editor_debug_first_session(registry)
expect(with_state.breakpoints.len()).to_equal(1)
expect(with_state.breakpoints[0].condition).to_equal("x > 3")
expect(with_state.breakpoints[0].log_message).to_equal("log x")
expect(with_state.breakpoints[0].hit_condition).to_equal("5")
expect(with_state.watches.len()).to_equal(1)
expect(with_state.watches[0].expression).to_equal("x + y")

registry = editor_debug_evaluate(registry, session.id, "x + y")
registry = editor_debug_console_append(registry, session.id, "output", "program started")
registry = editor_debug_set_exception_filters(registry, session.id, ["caught", "uncaught"])
val with_console = editor_debug_first_session(registry)
expect(with_console.console.len()).to_equal(2)
expect(with_console.console[0].kind).to_equal("evaluate")
expect(with_console.console[0].text_content).to_equal("x + y")
expect(with_console.exception_filters.len()).to_equal(2)
expect(with_console.exception_filters[1]).to_equal("uncaught")

registry = editor_debug_update_watch(registry, session.id, "x + y", "42", "ok")
registry = editor_debug_evaluate_result(registry, session.id, "x + y", "42", "ok")
val with_results = editor_debug_first_session(registry)
expect(with_results.watches[0].last_value).to_equal("42")
expect(with_results.watches[0].status).to_equal("ok")
expect(with_results.console[with_results.console.len() - 1].kind).to_equal("evaluate-result")
expect(with_results.console[with_results.console.len() - 1].text_content).to_equal("x + y = 42")

registry = editor_debug_update_stack_frames(registry, session.id, [
    EditorDebugStackFrame(id: 1, name: "main", path: "src/main.spl", line: 12, col: 4)
])
registry = editor_debug_update_scopes(registry, session.id, [
    EditorDebugScope(name: "Locals", variables_reference: 10, variables: [])
])
registry = editor_debug_update_scope_variables(registry, session.id, "Locals", [
    EditorDebugVariable(name: "answer", value: "42", debug_type: "i64", variables_reference: 0)
])
val with_debug_tree = editor_debug_first_session(registry)
expect(with_debug_tree.stack_frames.len()).to_equal(1)
expect(with_debug_tree.stack_frames[0].name).to_equal("main")
expect(with_debug_tree.scopes.len()).to_equal(1)
expect(with_debug_tree.scopes[0].name).to_equal("Locals")
expect(with_debug_tree.scopes[0].variables[0].name).to_equal("answer")
expect(with_debug_tree.scopes[0].variables[0].value).to_equal("42")

registry = editor_debug_continue(registry, session.id)
expect(editor_debug_first_session(registry).status).to_equal("running")
registry = editor_debug_pause(registry, session.id)
expect(editor_debug_first_session(registry).status).to_equal("paused")
registry = editor_debug_step(registry, session.id, "stepOver")
expect(editor_debug_first_session(registry).status).to_equal("stepping")

registry = editor_debug_enable_breakpoint(registry, with_console.breakpoints[0].id, false)
expect(editor_debug_first_session(registry).breakpoints[0].enabled).to_equal(false)

registry = editor_debug_registry_terminate(registry, session.id)
expect(editor_debug_first_session(registry).status).to_equal("terminated")

registry = editor_debug_registry_restart(registry, session.id)
expect(editor_debug_first_session(registry).status).to_equal("restarting")
val restarted = editor_debug_first_session(registry)
expect(restarted.console[restarted.console.len() - 1].text_content).to_equal("restart")
```

</details>

#### builds and parses DAP stack scopes variables requests and responses

1. EditorDebugBreakpoint
2. EditorDebugBreakpoint
3. EditorDebugBreakpoint
   - Expected: bp_request contains `"command":"setBreakpoints"`
   - Expected: bp_request contains `"path":"/tmp/main.spl"`
   - Expected: bp_request contains `"line":2`
   - Expected: bp_request contains `"condition":"answer > 0"`
   - Expected: bp_request contains `"logMessage":"answer"`
   - Expected: bp_request contains `"hitCondition":"3"`
   - Expected: bp_request does not contain `"line":4`
   - Expected: bp_request does not contain `"line":5`
   - Expected: exception_request contains `"command":"setExceptionBreakpoints"`
   - Expected: exception_request contains `"filters":["caught","uncaught"]`
   - Expected: editor_debug_dap_response_command(stack_json) equals `stackTrace`
   - Expected: editor_debug_dap_response_success(stack_json) is true
   - Expected: frames.len() equals `1`
   - Expected: frames[0].name equals `main`
   - Expected: frames[0].path equals `/tmp/main.spl`
   - Expected: frames[0].line equals `2`
   - Expected: frames[0].col equals `4`
   - Expected: scopes.len() equals `1`
   - Expected: scopes[0].name equals `Locals`
   - Expected: scopes[0].variables_reference equals `10`
   - Expected: variables.len() equals `2`
   - Expected: variables[0].name equals `answer`
   - Expected: variables[0].value equals `42`
   - Expected: variables[0].debug_type equals `i64`
   - Expected: variables[1].name equals `status`
   - Expected: variables[1].value equals `"ready"`
   - Expected: editor_debug_evaluate_result_from_dap_response(evaluate_json) equals `42`
   - Expected: parsed.0 equals `stack_json`
   - Expected: parsed.1 equals `framed.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 63 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(editor_debug_dap_stack_trace_request(5, 1).contains("\"command\":\"stackTrace\"")).to_equal(true)
expect(editor_debug_dap_stack_trace_request(5, 1).contains("\"threadId\":1")).to_equal(true)
expect(editor_debug_dap_scopes_request(6, 1).contains("\"command\":\"scopes\"")).to_equal(true)
expect(editor_debug_dap_scopes_request(6, 1).contains("\"frameId\":1")).to_equal(true)
expect(editor_debug_dap_variables_request(7, 10).contains("\"command\":\"variables\"")).to_equal(true)
expect(editor_debug_dap_variables_request(7, 10).contains("\"variablesReference\":10")).to_equal(true)
val eval_request = editor_debug_dap_evaluate_request(8, "answer", 1)
expect(eval_request.contains("\"command\":\"evaluate\"")).to_equal(true)
expect(eval_request.contains("\"expression\":\"answer\"")).to_equal(true)
expect(eval_request.contains("\"frameId\":1")).to_equal(true)
expect(editor_debug_dap_continue_request(9, 1).contains("\"command\":\"continue\"")).to_equal(true)
expect(editor_debug_dap_pause_request(10, 1).contains("\"command\":\"pause\"")).to_equal(true)
expect(editor_debug_dap_step_request(11, "stepIn", 1).contains("\"command\":\"stepIn\"")).to_equal(true)
expect(editor_debug_dap_step_request(12, "stepOver", 1).contains("\"command\":\"next\"")).to_equal(true)
val bp_request = editor_debug_dap_set_breakpoints_request(13, "/tmp/main.spl", [
    EditorDebugBreakpoint(id: 1, path: "/tmp/main.spl", line: 2, enabled: true, condition: "answer > 0", log_message: "answer", hit_condition: "3"),
    EditorDebugBreakpoint(id: 2, path: "/tmp/other.spl", line: 4, enabled: true, condition: "", log_message: "", hit_condition: ""),
    EditorDebugBreakpoint(id: 3, path: "/tmp/main.spl", line: 5, enabled: false, condition: "", log_message: "", hit_condition: "")
])
expect(bp_request.contains("\"command\":\"setBreakpoints\"")).to_equal(true)
expect(bp_request.contains("\"path\":\"/tmp/main.spl\"")).to_equal(true)
expect(bp_request.contains("\"line\":2")).to_equal(true)
expect(bp_request.contains("\"condition\":\"answer > 0\"")).to_equal(true)
expect(bp_request.contains("\"logMessage\":\"answer\"")).to_equal(true)
expect(bp_request.contains("\"hitCondition\":\"3\"")).to_equal(true)
expect(bp_request.contains("\"line\":4")).to_equal(false)
expect(bp_request.contains("\"line\":5")).to_equal(false)
val exception_request = editor_debug_dap_set_exception_breakpoints_request(14, ["caught", "uncaught"])
expect(exception_request.contains("\"command\":\"setExceptionBreakpoints\"")).to_equal(true)
expect(exception_request.contains("\"filters\":[\"caught\",\"uncaught\"]")).to_equal(true)

val stack_json = "{\"seq\":1005,\"type\":\"response\",\"request_seq\":5,\"success\":true,\"command\":\"stackTrace\",\"body\":{\"stackFrames\":[{\"id\":1,\"name\":\"main\",\"line\":2,\"column\":4,\"source\":{\"name\":\"main.spl\",\"path\":\"/tmp/main.spl\"}}],\"totalFrames\":1}}"
val frames = editor_debug_stack_frames_from_dap_response(stack_json)
expect(editor_debug_dap_response_command(stack_json)).to_equal("stackTrace")
expect(editor_debug_dap_response_success(stack_json)).to_equal(true)
expect(frames.len()).to_equal(1)
expect(frames[0].name).to_equal("main")
expect(frames[0].path).to_equal("/tmp/main.spl")
expect(frames[0].line).to_equal(2)
expect(frames[0].col).to_equal(4)

val scopes_json = "{\"seq\":1006,\"type\":\"response\",\"request_seq\":6,\"success\":true,\"command\":\"scopes\",\"body\":{\"scopes\":[{\"name\":\"Locals\",\"variablesReference\":10,\"expensive\":false}]}}"
val scopes = editor_debug_scopes_from_dap_response(scopes_json)
expect(scopes.len()).to_equal(1)
expect(scopes[0].name).to_equal("Locals")
expect(scopes[0].variables_reference).to_equal(10)

val variables_json = "{\"seq\":1007,\"type\":\"response\",\"request_seq\":7,\"success\":true,\"command\":\"variables\",\"body\":{\"variables\":[{\"name\":\"answer\",\"value\":\"42\",\"type\":\"i64\",\"variablesReference\":0},{\"name\":\"status\",\"value\":\"\\\"ready\\\"\",\"type\":\"text\",\"variablesReference\":0}]}}"
val variables = editor_debug_variables_from_dap_response(variables_json)
expect(variables.len()).to_equal(2)
expect(variables[0].name).to_equal("answer")
expect(variables[0].value).to_equal("42")
expect(variables[0].debug_type).to_equal("i64")
expect(variables[1].name).to_equal("status")
expect(variables[1].value).to_equal("\"ready\"")

val evaluate_json = "{\"seq\":1008,\"type\":\"response\",\"request_seq\":8,\"success\":true,\"command\":\"evaluate\",\"body\":{\"result\":\"42\",\"variablesReference\":0}}"
expect(editor_debug_evaluate_result_from_dap_response(evaluate_json)).to_equal("42")

val framed = editor_debug_dap_frame_message(stack_json)
val parsed = editor_debug_dap_parse_frame(framed)
expect(parsed.0).to_equal(stack_json)
expect(parsed.1).to_equal(framed.len())
```

</details>

#### maps DAP lifecycle events to editor debug statuses

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val stopped = "{\"seq\":2002,\"type\":\"event\",\"event\":\"stopped\",\"body\":{\"reason\":\"breakpoint\",\"threadId\":1}}"
expect(editor_debug_dap_message_type(stopped)).to_equal("event")
expect(editor_debug_dap_event_name(stopped)).to_equal("stopped")
expect(editor_debug_dap_event_status(stopped)).to_equal("paused")
expect(editor_debug_dap_event_summary(stopped)).to_equal("debug stopped: breakpoint")

val continued = "{\"seq\":2003,\"type\":\"event\",\"event\":\"continued\",\"body\":{\"threadId\":1}}"
expect(editor_debug_dap_event_status(continued)).to_equal("running")
expect(editor_debug_dap_event_summary(continued)).to_equal("debug continued")

val terminated = "{\"seq\":2004,\"type\":\"event\",\"event\":\"terminated\"}"
expect(editor_debug_dap_event_status(terminated)).to_equal("terminated")
expect(editor_debug_dap_event_summary(terminated)).to_equal("debug terminated")
```

</details>

#### buffers DAP client requests and polls inbound messages

1. var client = EditorDebugDapClient new
   - Expected: cold_stack.1 equals `0`
2. client = editor debug dap client start
   - Expected: initialized.1 equals `1`
   - Expected: launched.1 equals `2`
   - Expected: continued.1 equals `3`
   - Expected: paused.1 equals `4`
   - Expected: stepped.1 equals `5`
   - Expected: exception_filters.1 equals `6`
   - Expected: client.send_buffer.len() equals `6`
   - Expected: client.send_buffer[0] contains `Content-Length:`
   - Expected: client.send_buffer[0] contains `"command":"initialize"`
   - Expected: client.send_buffer[1] contains `"program":"/tmp/main.spl"`
   - Expected: client.send_buffer[4] contains `"command":"stepIn"`
   - Expected: client.pending_requests.len() equals `6`
3. client = editor debug dap client inject message
4. client = editor debug dap client inject message
   - Expected: messages.len() equals `2`
   - Expected: messages[0].message_type equals `response`
   - Expected: messages[0].command equals `continue`
   - Expected: messages[1].message_type equals `event`
   - Expected: messages[1].event_name equals `stopped`
   - Expected: client.pending_requests.len() equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 40 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var client = EditorDebugDapClient.new()
val cold_stack = editor_debug_dap_client_stack_trace(client, 1)
expect(cold_stack.1).to_equal(0)
client = editor_debug_dap_client_start(client)
val initialized = editor_debug_dap_client_initialize(client)
client = initialized.0
expect(initialized.1).to_equal(1)
val launched = editor_debug_dap_client_launch(client, editor_debug_launch_config_default("/tmp/main.spl"))
client = launched.0
expect(launched.1).to_equal(2)
val continued = editor_debug_dap_client_continue_thread(client, 1)
client = continued.0
expect(continued.1).to_equal(3)
val paused = editor_debug_dap_client_pause_thread(client, 1)
client = paused.0
expect(paused.1).to_equal(4)
val stepped = editor_debug_dap_client_step_thread(client, "stepIn", 1)
client = stepped.0
expect(stepped.1).to_equal(5)
val exception_filters = editor_debug_dap_client_set_exception_breakpoints(client, ["caught", "uncaught"])
client = exception_filters.0
expect(exception_filters.1).to_equal(6)
expect(client.send_buffer.len()).to_equal(6)
expect(client.send_buffer[0].contains("Content-Length:")).to_equal(true)
expect(client.send_buffer[0].contains("\"command\":\"initialize\"")).to_equal(true)
expect(client.send_buffer[1].contains("\"program\":\"/tmp/main.spl\"")).to_equal(true)
expect(client.send_buffer[4].contains("\"command\":\"stepIn\"")).to_equal(true)
expect(client.pending_requests.len()).to_equal(6)

client = editor_debug_dap_client_inject_message(client, "{\"seq\":1003,\"type\":\"response\",\"request_seq\":3,\"success\":true,\"command\":\"continue\"}")
client = editor_debug_dap_client_inject_message(client, "{\"seq\":2002,\"type\":\"event\",\"event\":\"stopped\",\"body\":{\"reason\":\"step\",\"threadId\":1}}")
val polled = editor_debug_dap_client_poll_messages(client)
client = polled.0
val messages = polled.1
expect(messages.len()).to_equal(2)
expect(messages[0].message_type).to_equal("response")
expect(messages[0].command).to_equal("continue")
expect(messages[1].message_type).to_equal("event")
expect(messages[1].event_name).to_equal("stopped")
expect(client.pending_requests.len()).to_equal(5)
```

</details>

#### defines process-backed DAP client hooks for native stdio transport

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = read_text("src/lib/editor/services/debug_session_dap.spl")
expect(src.contains("extern fn rt_process_spawn_piped(cmd: text, args: [text]) -> i64")).to_equal(true)
expect(src.contains("extern fn rt_process_write_stdin(pid: i64, data: text) -> bool")).to_equal(true)
expect(src.contains("extern fn rt_process_read_stdout(pid: i64) -> text")).to_equal(true)
expect(src.contains("me start_process(command: text, args: [text]) -> bool")).to_equal(true)
expect(src.contains("rt_process_write_stdin(me.process_pid, framed)")).to_equal(true)
expect(src.contains("rt_process_read_stdout(me.process_pid)")).to_equal(true)
expect(src.contains("editor_debug_dap_parse_frame(me.process_buffer)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gui/editor_debug_session_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- editor debug session model

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
