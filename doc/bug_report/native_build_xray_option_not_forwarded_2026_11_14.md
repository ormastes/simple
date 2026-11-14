# Native-build discards/rejects the XRay static request

Status: implementation prepared; changed-compiler execution pending. No instrumentation capability is admitted by this patch.

The bootstrap compiler exposes native-build but its standalone-option whitelist and parsed options did not carry --xray. Full CLI compile already carries CompileOptions.xray_enabled into the shared driver policy. Rebuilding bootstrap_main alone therefore cannot qualify a genuine generated XRay fixture.

The repair adds the flag to the shared native-build whitelist, preserves it in typed parsed options, and forwards it in both authoritative CompileOptions construction paths before normalization. Help states the explicit development/native-output requirements. Shared release/backend/output/target policy remains authoritative; ordinary builds retain false. No observer capability, runtime provider, linker selection, or implicit profile change is introduced.

Planned executable acceptance: test/01_unit/app/native_build_xray_options_spec.spl covers off defaults, explicit dev/one-binary selection, release/prod refusal, dynload-output and Cranelift refusal, malformed flags. It is authored but UNRUN. Existing backend target tests remain responsible for non-Linux target rejection; forwarding does not bypass those gates.

A real changed-producer test must build a small source with native-build --profile dev --mode one-binary --backend llvm --target aarch64-unknown-linux-gnu --xray, inspect the resulting instrumentation/map and execute it with the reviewed provider. Repeat off/release/unsupported-target negative scenarios without claiming a parser test proves emitted sleds. The frozen producer source4b01686d7ed is immutable and does NOT include this change or all unlanded provider owners. A new reviewed capability-specific source freeze is required before that test.
