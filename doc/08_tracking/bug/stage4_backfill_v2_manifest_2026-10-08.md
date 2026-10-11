# Stage4 rejects canonical Cranelift V2 backend exports

Source-only repair; native regression and full compiler qualification pending.

The retained backend-only archive SHA256 3461d5921216912f94923f01dd321732cde73b6c0830c9963e2e1fde65584304 contains 76 rt_cranelift exports and three canonical spl_cranelift V2 definitions. Source 503e5b3fbd780d3658e3bf5b3f494dd6faf4adac admits only the former in stage4_derive_compiler_backfill_manifest, then rejects the latter as foreign ownership. Prior fullCLI RSS failures occurred before linking; this is source/census evidence, not an observed successful or failed capsule execution.

The repair admits only these three exact names, retaining the required rt_cranelift family presence, unique-definition checks, forbidden runtime dependency checks, compatibility-wrapper exclusions and provider-disjoint validation:

- spl_cranelift_new_aot_module_config_v2: nine raw i64 arguments (four pointer/length pairs plus optimization level), raw i64 module handle result.
- spl_cranelift_aot_isa_feature_v2: module handle and feature pointer/length, three raw i64 arguments and raw i64 result.
- spl_cranelift_aot_opt_level_v2: one raw i64 module argument and raw i64 result.

Signatures agree between compiler_rust/compiler/src/codegen/cranelift_sffi.rs, runtime_sffi.rs and src/lib/nogc_sync_mut/sffi/codegen.spl. The latter explicitly decomposes text into borrowed pointer/length arguments. The production cranelift_codegen_adapter.spl constructor and feature/optimization readback consume these APIs. No foreign ABI or implementation changes are made.

The standalone test/04_smoke/native_stage4_backfill_v2_manifest.spl calls the actual manifest owner. Its 17 checks cover exact ELF exports, Mach-O normalization, each duplicate V2 export, arbitrary spl and near-name refusals, rt-family presence, undefined runtime dependencies, forbidden compatibility wrappers, provider overlap and duplicate legacy exports. It is unexecuted. Compile it with the newly qualified Phase2 native-build entry-closure route and execute the resulting binary; importing its compiler owner can expand the closure. No seed/application substitution or old-compiler source-overlay test is claimed.

The backend archive was built from 051ee9 plus the streaming SHA runtime patch; inspected package, included Cranelift SFFI source, lockfile, workspace manifest and Cargo config are unchanged through 503e. That supports pinned external-backend reuse, not a claim the archive was rebuilt at 503e. Its retained census is defined-only; actual Stage4 closure-link/localization/dependency checks and output compiler execution remain required.