# WM Browser Event Routing Evidence

- status: pass
- reason: pass
- window commands: 4
- input events: 3
- title text: Terminal
- traffic buttons: 3
- titlebar height: 34px
- title input: input 144.562px x 24px
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
- wm_browser_event_routing_title_text=Terminal
- wm_browser_event_routing_title_context_text=terminal
- wm_browser_event_routing_traffic_button_count=3
- wm_browser_event_routing_title_input_tag=input
- wm_browser_event_routing_titlebar_height=34px
- wm_browser_event_routing_titlebar_display=flex
- wm_browser_event_routing_titlebar_cursor=grab
- wm_browser_event_routing_titlebar_background=rgb(229, 231, 235)
- wm_browser_event_routing_title_color=rgb(17, 24, 39)
- wm_browser_event_routing_title_input_min_width=142px
- wm_browser_event_routing_title_input_width=144.562px
- wm_browser_event_routing_title_input_width_px=144.562
- wm_browser_event_routing_title_input_height=24px
- wm_browser_event_routing_title_input_cursor=text
- wm_browser_event_routing_title_input_background=rgb(241, 245, 249)
- wm_browser_event_routing_close_button_background=rgb(239, 68, 68)
- wm_browser_event_routing_minimize_button_background=rgb(234, 179, 8)
- wm_browser_event_routing_maximize_button_background=rgb(34, 197, 94)
- wm_browser_event_routing_blur_or_tolerance_used=false
- wm_browser_event_routing_exit_code=0

## Probe Output
- WM_EVENT_CHECK {"ready":true,"wm_found":true,"title_text":"Terminal","title_context_text":"terminal","traffic_button_count":3,"title_input_tag":"input","titlebar_height":"34px","titlebar_display":"flex","titlebar_cursor":"grab","titlebar_background":"rgb(229, 231, 235)","title_color":"rgb(17, 24, 39)","title_font_weight":"700","title_input_min_width":"142px","title_input_width":"144.562px","title_input_width_px":144.562,"title_input_height":"24px","title_input_cursor":"text","title_input_background":"rgb(241, 245, 249)","close_button_background":"rgb(239, 68, 68)","minimize_button_background":"rgb(234, 179, 8)","maximize_button_background":"rgb(34, 197, 94)","window_cmd_count":4,"input_event_count":3,"focus_count":1,"move_count":1,"maximize_count":1,"title_command_count":1,"text_input_count":1,"pointer_down_count":1,"pointer_up_count":1,"move_payload":{"cmd_type":"move","kind":"move","window_id_hint":"win1","source":"native_event","x":86,"y":86},"title_payload":{"cmd_type":"title_command","kind":"title_command","window_id_hint":"win1","command_text":"/tmp/project","command_kind":"path","command_context":"terminal"},"text_payload":{"surface_id":"win1","widget_id":"field","event":{"kind":"text_input","text":"Hello Simple"}},"expected_move_x":86,"expected_move_y":86,"pass":true}
