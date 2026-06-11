# WM Browser Event Routing Evidence

- status: pass
- reason: pass
- window commands: 4
- input events: 3
- blur/tolerance used: false

## Raw Evidence
- wm_browser_event_routing_status=pass
- wm_browser_event_routing_reason=pass
- wm_browser_event_routing_result_path=build/wm_browser_event_routing_evidence/wm-event-check.json
- wm_browser_event_routing_ready=true
- wm_browser_event_routing_wm_found=true
- wm_browser_event_routing_window_cmd_count=4
- wm_browser_event_routing_input_event_count=3
- wm_browser_event_routing_focus_count=1
- wm_browser_event_routing_move_count=1
- wm_browser_event_routing_maximize_count=1
- wm_browser_event_routing_title_command_count=1
- wm_browser_event_routing_text_input_count=1
- wm_browser_event_routing_pointer_down_count=1
- wm_browser_event_routing_pointer_up_count=1
- wm_browser_event_routing_blur_or_tolerance_used=false
- wm_browser_event_routing_exit_code=0

## Probe Output
- WM_EVENT_CHECK {"ready":true,"wm_found":true,"window_cmd_count":4,"input_event_count":3,"focus_count":1,"move_count":1,"maximize_count":1,"title_command_count":1,"text_input_count":1,"pointer_down_count":1,"pointer_up_count":1,"move_payload":{"cmd_type":"move","kind":"move","window_id_hint":"win1","source":"native_event","x":86,"y":86},"title_payload":{"cmd_type":"title_command","kind":"title_command","window_id_hint":"win1","command_text":"/tmp/project","command_kind":"path","command_context":"terminal"},"text_payload":{"surface_id":"win1","widget_id":"field","event":{"kind":"text_input","text":"Hello Simple"}},"expected_move_x":86,"expected_move_y":86,"pass":true}
