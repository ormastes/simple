# Electron Live Bitmap Evidence

- status: pass
- reason: pass
- scene: wm-image-taskbar-command
- dimensions: 96x64
- Node checksum: 225350
- Electron checksum: 225350
- mismatch count: 0
- blur/tolerance used: false
- Node frame us: 944
- Electron frame us: 15342

## Raw Evidence
- electron_live_bitmap_status=pass
- electron_live_bitmap_reason=pass
- electron_live_bitmap_width=96
- electron_live_bitmap_height=64
- electron_live_bitmap_iterations=5
- electron_live_bitmap_node_checksum=225350
- electron_live_bitmap_electron_checksum=225350
- electron_live_bitmap_mismatch_count=0
- electron_live_bitmap_blur_or_tolerance_used=false
- electron_live_bitmap_node_frame_us=944
- electron_live_bitmap_electron_frame_us=15342
- electron_live_bitmap_exit_code=0

## Node Output
- renderer=node-exact-fixture
- width=96
- height=64
- iterations=5
- checksum=225350
- total_checksum=1126750
- frame_us=944
- blur_or_tolerance_used=false

## Electron Output
- [57895:0531/042628.415711:ERROR:viz_main_impl.cc(181)] Exiting GPU process due to errors during initialization
- [57992:0531/042628.799349:ERROR:shared_image_manager.cc(255)] SharedImageManager::ProduceSkia: Trying to produce a Skia representation from an incompatible backing: GLTextureImageBacking
- [57992:0531/042628.799511:ERROR:raster_decoder.cc(1968)] [.RenderWorker-0x2a0c00024100]GL ERROR :GL_INVALID_VALUE : glCopySubTexture: unknown mailbox
- renderer=electron-live-capture-page
- scene=wm-image-taskbar-command
- width=96
- height=64
- iterations=5
- checksum=225350
- expected_checksum=225350
- weighted_checksum=755507810
- expected_weighted_checksum=755507810
- mismatch_count=0
- frame_us=15342
- blur_or_tolerance_used=false
- [57863:0531/042628.982947:ERROR:object_proxy.cc(576)] Failed to call method: org.freedesktop.DBus.StartServiceByName: object_path= /org/freedesktop/DBus: org.freedesktop.DBus.Error.NoReply: Did not receive a reply. Possible causes include: the remote application did not send a reply, the message bus security policy blocked the reply, the reply timeout expired, or the network connection was broken.
