# GUI WASM Browser Execution Evidence

- status: fail
- reason: widget_matrix-browser-wasm-execution-failed
- targets: hello, widget_matrix, builder_matrix

## hello
- status: pass
- reason: pass
- wasm path: build/gui_wasm_cli_artifact_widget_helpers/hello_wasm_gui.wasm
- proof path: build/gui_wasm_browser_execution_widget_helpers/hello_browser_proof.json
- byte size: 4380
- WebAssembly.validate: true
- WebAssembly.instantiate: true
- import count: 0
- imports: 
- exports: simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- spl_main call: called
- simple_app_init ready code: 1
- simple_app_render call: called
- simple_app_event call: called
- simple_app_render_probe: 8
- simple_app_event_probe: 5
- simple.gui custom sections: 1
- render behavior markers: 7/7
- event behavior markers: 5/5
- retained selectors: 7/7
- retained nonzero boxes: 7/7
- retained event mutations: 4/4
- Electron exit code: 0

## widget_matrix
- status: fail
- reason: browser-wasm-execution-failed
- wasm path: build/gui_wasm_cli_artifact_widget_helpers/widget_matrix_wasm_gui.wasm
- proof path: build/gui_wasm_browser_execution_widget_helpers/widget_matrix_browser_proof.json
- byte size: 12484
- WebAssembly.validate: true
- WebAssembly.instantiate: true
- import count: 0
- imports: 
- exports: simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- spl_main call: called
- simple_app_init ready code: 1
- simple_app_render call: called
- simple_app_event call: called
- simple_app_render_probe: 19
- simple_app_event_probe: 9
- simple.gui custom sections: 1
- render behavior markers: 19/19
- event behavior markers: 23/23
- retained selectors: 23/23
- retained nonzero boxes: 23/23
- retained event mutations: 22/22
- Electron exit code: 2

## builder_matrix
- status: pass
- reason: pass
- wasm path: build/gui_wasm_cli_artifact_widget_helpers/builder_matrix_wasm_gui.wasm
- proof path: build/gui_wasm_browser_execution_widget_helpers/builder_matrix_browser_proof.json
- byte size: 9486
- WebAssembly.validate: true
- WebAssembly.instantiate: true
- import count: 0
- imports: 
- exports: simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- spl_main call: called
- simple_app_init ready code: 1
- simple_app_render call: called
- simple_app_event call: called
- simple_app_render_probe: 48
- simple_app_event_probe: 8
- simple.gui custom sections: 1
- render behavior markers: 10/10
- event behavior markers: 8/8
- retained selectors: 7/7
- retained nonzero boxes: 7/7
- retained event mutations: 5/5
- Electron exit code: 0

## Raw Evidence
- gui_wasm_browser_execution_status=fail
- gui_wasm_browser_execution_reason=widget_matrix-browser-wasm-execution-failed
- gui_wasm_browser_execution_targets=hello,widget_matrix,builder_matrix
- gui_wasm_browser_execution_hello_status=pass
- gui_wasm_browser_execution_hello_reason=pass
- gui_wasm_browser_execution_hello_wasm_path=build/gui_wasm_cli_artifact_widget_helpers/hello_wasm_gui.wasm
- gui_wasm_browser_execution_hello_proof_path=build/gui_wasm_browser_execution_widget_helpers/hello_browser_proof.json
- gui_wasm_browser_execution_hello_byte_size=4380
- gui_wasm_browser_execution_hello_validate=true
- gui_wasm_browser_execution_hello_instantiate=true
- gui_wasm_browser_execution_hello_import_count=0
- gui_wasm_browser_execution_hello_imports=
- gui_wasm_browser_execution_hello_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- gui_wasm_browser_execution_hello_call_spl_main=called
- gui_wasm_browser_execution_hello_call_simple_app_init=1
- gui_wasm_browser_execution_hello_call_simple_app_render=called
- gui_wasm_browser_execution_hello_call_simple_app_event=called
- gui_wasm_browser_execution_hello_simple_app_render_probe=8
- gui_wasm_browser_execution_hello_simple_app_event_probe=5
- gui_wasm_browser_execution_hello_simple_gui_custom_sections=1
- gui_wasm_browser_execution_hello_render_behavior_markers=7/7
- gui_wasm_browser_execution_hello_event_behavior_markers=5/5
- gui_wasm_browser_execution_hello_retained_selectors=7/7
- gui_wasm_browser_execution_hello_retained_nonzero_boxes=7/7
- gui_wasm_browser_execution_hello_retained_event_mutations=4/4
- gui_wasm_browser_execution_hello_electron_exit_code=0
- gui_wasm_browser_execution_widget_matrix_status=fail
- gui_wasm_browser_execution_widget_matrix_reason=browser-wasm-execution-failed
- gui_wasm_browser_execution_widget_matrix_wasm_path=build/gui_wasm_cli_artifact_widget_helpers/widget_matrix_wasm_gui.wasm
- gui_wasm_browser_execution_widget_matrix_proof_path=build/gui_wasm_browser_execution_widget_helpers/widget_matrix_browser_proof.json
- gui_wasm_browser_execution_widget_matrix_byte_size=12484
- gui_wasm_browser_execution_widget_matrix_validate=true
- gui_wasm_browser_execution_widget_matrix_instantiate=true
- gui_wasm_browser_execution_widget_matrix_import_count=0
- gui_wasm_browser_execution_widget_matrix_imports=
- gui_wasm_browser_execution_widget_matrix_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- gui_wasm_browser_execution_widget_matrix_call_spl_main=called
- gui_wasm_browser_execution_widget_matrix_call_simple_app_init=1
- gui_wasm_browser_execution_widget_matrix_call_simple_app_render=called
- gui_wasm_browser_execution_widget_matrix_call_simple_app_event=called
- gui_wasm_browser_execution_widget_matrix_simple_app_render_probe=19
- gui_wasm_browser_execution_widget_matrix_simple_app_event_probe=9
- gui_wasm_browser_execution_widget_matrix_simple_gui_custom_sections=1
- gui_wasm_browser_execution_widget_matrix_render_behavior_markers=19/19
- gui_wasm_browser_execution_widget_matrix_event_behavior_markers=23/23
- gui_wasm_browser_execution_widget_matrix_retained_selectors=23/23
- gui_wasm_browser_execution_widget_matrix_retained_nonzero_boxes=23/23
- gui_wasm_browser_execution_widget_matrix_retained_event_mutations=22/22
- gui_wasm_browser_execution_widget_matrix_electron_exit_code=2
- gui_wasm_browser_execution_builder_matrix_status=pass
- gui_wasm_browser_execution_builder_matrix_reason=pass
- gui_wasm_browser_execution_builder_matrix_wasm_path=build/gui_wasm_cli_artifact_widget_helpers/builder_matrix_wasm_gui.wasm
- gui_wasm_browser_execution_builder_matrix_proof_path=build/gui_wasm_browser_execution_widget_helpers/builder_matrix_browser_proof.json
- gui_wasm_browser_execution_builder_matrix_byte_size=9486
- gui_wasm_browser_execution_builder_matrix_validate=true
- gui_wasm_browser_execution_builder_matrix_instantiate=true
- gui_wasm_browser_execution_builder_matrix_import_count=0
- gui_wasm_browser_execution_builder_matrix_imports=
- gui_wasm_browser_execution_builder_matrix_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- gui_wasm_browser_execution_builder_matrix_call_spl_main=called
- gui_wasm_browser_execution_builder_matrix_call_simple_app_init=1
- gui_wasm_browser_execution_builder_matrix_call_simple_app_render=called
- gui_wasm_browser_execution_builder_matrix_call_simple_app_event=called
- gui_wasm_browser_execution_builder_matrix_simple_app_render_probe=48
- gui_wasm_browser_execution_builder_matrix_simple_app_event_probe=8
- gui_wasm_browser_execution_builder_matrix_simple_gui_custom_sections=1
- gui_wasm_browser_execution_builder_matrix_render_behavior_markers=10/10
- gui_wasm_browser_execution_builder_matrix_event_behavior_markers=8/8
- gui_wasm_browser_execution_builder_matrix_retained_selectors=7/7
- gui_wasm_browser_execution_builder_matrix_retained_nonzero_boxes=7/7
- gui_wasm_browser_execution_builder_matrix_retained_event_mutations=5/5
- gui_wasm_browser_execution_builder_matrix_electron_exit_code=0

## Electron Output

### builder_matrix.electron.out
- [electron:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization
- [electron:ERROR:shared_image_interface_proxy.cc(134)] Buffer handle is null. Not creating a mailbox from it.
- [electron:ERROR:one_copy_raster_buffer_provider.cc(348)] Creation of StagingBuffer's SharedImage failed.
- gui_wasm_browser_execution_proof=/home/ormastes/dev/pub/simple/build/gui_wasm_browser_execution_widget_helpers/builder_matrix_browser_proof.json
- gui_wasm_browser_execution_validate=true
- gui_wasm_browser_execution_instantiate=true
- gui_wasm_browser_execution_import_count=0
- gui_wasm_browser_execution_imports=
- gui_wasm_browser_execution_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- [electron:ERROR:object_proxy.cc(576)] Failed to call method: org.freedesktop.DBus.StartServiceByName: object_path= /org/freedesktop/DBus: org.freedesktop.DBus.Error.NoReply: Did not receive a reply. Possible causes include: the remote application did not send a reply, the message bus security policy blocked the reply, the reply timeout expired, or the network connection was broken.

### hello.electron.out
- [electron:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization
- [electron:ERROR:shared_image_manager.cc(255)] SharedImageManager::ProduceSkia: Trying to produce a Skia representation from an incompatible backing: GLTextureImageBacking
- [electron:ERROR:raster_decoder.cc(1968)] [.RenderWorker-ADDR]GL ERROR :GL_INVALID_VALUE : glCopySubTexture: unknown mailbox
- gui_wasm_browser_execution_proof=/home/ormastes/dev/pub/simple/build/gui_wasm_browser_execution_widget_helpers/hello_browser_proof.json
- gui_wasm_browser_execution_validate=true
- gui_wasm_browser_execution_instantiate=true
- gui_wasm_browser_execution_import_count=0
- gui_wasm_browser_execution_imports=
- gui_wasm_browser_execution_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- [electron:ERROR:object_proxy.cc(576)] Failed to call method: org.freedesktop.DBus.StartServiceByName: object_path= /org/freedesktop/DBus: org.freedesktop.DBus.Error.NoReply: Did not receive a reply. Possible causes include: the remote application did not send a reply, the message bus security policy blocked the reply, the reply timeout expired, or the network connection was broken.

### widget_matrix.electron.out
- [electron:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization
- gui_wasm_browser_execution_proof=/home/ormastes/dev/pub/simple/build/gui_wasm_browser_execution_widget_helpers/widget_matrix_browser_proof.json
- gui_wasm_browser_execution_validate=true
- gui_wasm_browser_execution_instantiate=true
- gui_wasm_browser_execution_import_count=0
- gui_wasm_browser_execution_imports=
- gui_wasm_browser_execution_exports=simple_app_event,simple_app_event_probe,simple_app_init,simple_app_render,simple_app_render_probe,spl_main
- [electron:ERROR:object_proxy.cc(576)] Failed to call method: org.freedesktop.DBus.StartServiceByName: object_path= /org/freedesktop/DBus: org.freedesktop.DBus.Error.NoReply: Did not receive a reply. Possible causes include: the remote application did not send a reply, the message bus security policy blocked the reply, the reply timeout expired, or the network connection was broken.

## Electron Error

### builder_matrix.electron.err

### hello.electron.err

### widget_matrix.electron.err
