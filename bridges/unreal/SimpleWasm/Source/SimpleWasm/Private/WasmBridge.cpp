// WasmBridge.cpp - Core WASM loading and lifecycle
// Part of SimpleWasm Unreal bridge

#include "WasmBridge.h"
#include "Misc/FileHelper.h"
#include "Misc/Paths.h"
#include "HAL/PlatformFileManager.h"

// ── wasmtime C API headers ──────────────────────────────────────────────────
// These ship with the wasmtime-c-api release and must be on the include path.
#include <wasm.h>
#include <wasmtime.h>

// ── Static handle tables ────────────────────────────────────────────────────

HandleTable<AActor>                   USimpleWasmBridge::Entities;
HandleTable<UMaterialInstanceDynamic> USimpleWasmBridge::Materials;
HandleTable<UAudioComponent>          USimpleWasmBridge::AudioSources;
HandleTable<UObject>                  USimpleWasmBridge::Assets;
USimpleWasmBridge*                    USimpleWasmBridge::ActiveBridge = nullptr;

// ============================================================================
// Constructor
// ============================================================================

USimpleWasmBridge::USimpleWasmBridge()
{
    PrimaryComponentTick.bCanEverTick = true;
    PrimaryComponentTick.bStartWithTickEnabled = true;
}

// ============================================================================
// Lifecycle
// ============================================================================

void USimpleWasmBridge::BeginPlay()
{
    Super::BeginPlay();

    if (WasmPath.IsEmpty())
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] WasmPath is empty — nothing to load."));
        return;
    }

    if (!LoadAndInstantiate())
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Failed to load module: %s"), *WasmPath);
        return;
    }

    // Call game_init export
    if (FuncInit >= 0)
    {
        wasmtime_val_t Params[1];
        wasmtime_val_t Results[1];
        wasmtime_context_t* Ctx = wasmtime_store_context(Store);

        wasmtime_func_t InitFunc;
        bool bFound = false;
        wasmtime_extern_t Ext;
        if (wasmtime_instance_export_nth(Ctx, Instance, FuncInit, nullptr, 0, &Ext))
        {
            // Already resolved by index — call it
        }

        // Simpler: use the stored func reference
        wasmtime_error_t* Err = wasmtime_func_call(Ctx, &InitFunc, Params, 0, Results, 0, nullptr);
        if (Err)
        {
            wasm_message_t Msg;
            wasmtime_error_message(Err, &Msg);
            UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] game_init failed: %hs"),
                   (const char*)Msg.data);
            wasm_byte_vec_delete(&Msg);
            wasmtime_error_delete(Err);
        }
    }
}

void USimpleWasmBridge::TickComponent(float DeltaTime, ELevelTick TickType,
                                       FActorComponentTickFunction* ThisTickFunction)
{
    Super::TickComponent(DeltaTime, TickType, ThisTickFunction);

    if (!bModuleLoaded)
        return;

    // Hot-reload check
    if (bEnableHotReload)
    {
        CheckHotReload(DeltaTime);
    }

    // Set ourselves as the active bridge so static functions can find us
    ActiveBridge = this;

    // Call game_update(delta_time)
    if (FuncUpdate >= 0)
    {
        wasmtime_context_t* Ctx = wasmtime_store_context(Store);

        wasmtime_val_t Params[1];
        Params[0].kind = WASMTIME_F32;
        Params[0].of.f32 = DeltaTime;

        wasmtime_val_t Results[1];

        wasmtime_func_t UpdateFunc;
        wasmtime_extern_t Ext;
        if (wasmtime_instance_export_get(Ctx, Instance, "game_update", 11, &Ext)
            && Ext.kind == WASMTIME_EXTERN_FUNC)
        {
            UpdateFunc = Ext.of.func;
        }

        wasmtime_error_t* Err = wasmtime_func_call(Ctx, &UpdateFunc, Params, 1, Results, 0, nullptr);
        if (Err)
        {
            wasm_message_t Msg;
            wasmtime_error_message(Err, &Msg);
            UE_LOG(LogTemp, Warning, TEXT("[SimpleWasm] game_update error: %hs"),
                   (const char*)Msg.data);
            wasm_byte_vec_delete(&Msg);
            wasmtime_error_delete(Err);
        }
    }

    ActiveBridge = nullptr;
}

void USimpleWasmBridge::EndPlay(const EEndPlayReason::Type EndPlayReason)
{
    ActiveBridge = this;

    // Call game_shutdown export
    if (bModuleLoaded && FuncShutdown >= 0)
    {
        wasmtime_context_t* Ctx = wasmtime_store_context(Store);

        wasmtime_func_t ShutdownFunc;
        wasmtime_extern_t Ext;
        if (wasmtime_instance_export_get(Ctx, Instance, "game_shutdown", 13, &Ext)
            && Ext.kind == WASMTIME_EXTERN_FUNC)
        {
            ShutdownFunc = Ext.of.func;
            wasmtime_func_call(Ctx, &ShutdownFunc, nullptr, 0, nullptr, 0, nullptr);
        }
    }

    ActiveBridge = nullptr;
    ShutdownWasm();

    // Clear all handle tables
    Entities.Reset();
    Materials.Reset();
    AudioSources.Reset();
    Assets.Reset();

    Super::EndPlay(EndPlayReason);
}

// ============================================================================
// Module loading
// ============================================================================

bool USimpleWasmBridge::LoadAndInstantiate()
{
    // Resolve path
    FString FullPath = WasmPath;
    if (FPaths::IsRelative(FullPath))
    {
        FullPath = FPaths::Combine(FPaths::ProjectContentDir(), FullPath);
    }
    FullPath = FPaths::ConvertRelativePathToFull(FullPath);

    // Read .wasm bytes
    TArray<uint8> WasmBytes;
    if (!FFileHelper::LoadFileToArray(WasmBytes, *FullPath))
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Cannot read file: %s"), *FullPath);
        return false;
    }

    // Record modification time for hot-reload
    LastModifiedTime = FPlatformFileManager::Get().GetPlatformFile()
                           .GetTimeStamp(*FullPath);

    // ── Create wasmtime engine ──────────────────────────────────────────
    wasm_config_t* Config = wasm_config_new();
    // Enable fuel for bounded execution (optional)
    wasmtime_config_consume_fuel_set(Config, false);

    Engine = wasm_engine_new_with_config(Config);
    if (!Engine)
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] wasm_engine_new failed"));
        return false;
    }

    // ── Create store ────────────────────────────────────────────────────
    Store = wasmtime_store_new(Engine, this, nullptr);
    if (!Store)
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] wasmtime_store_new failed"));
        ShutdownWasm();
        return false;
    }

    wasmtime_context_t* Ctx = wasmtime_store_context(Store);

    // ── Create linker and register all engine_* imports ─────────────────
    Linker = wasmtime_linker_new(Engine);

    // Register WASI (some modules may use basic WASI for memory allocation)
    wasmtime_error_t* WasiErr = wasmtime_linker_define_wasi(Linker);
    if (WasiErr)
    {
        wasmtime_error_delete(WasiErr);
        // Non-fatal: module may not need WASI
    }

    // Register all 68 engine_* bridge functions by category
    SimpleWasm::RegisterEntityFunctions(Linker, Store);
    SimpleWasm::RegisterTransformFunctions(Linker, Store);
    SimpleWasm::RegisterRenderFunctions(Linker, Store);
    SimpleWasm::RegisterInputFunctions(Linker, Store);
    SimpleWasm::RegisterPhysicsFunctions(Linker, Store);
    SimpleWasm::RegisterAudioFunctions(Linker, Store);
    SimpleWasm::RegisterAssetFunctions(Linker, Store);
    SimpleWasm::RegisterDebugFunctions(Linker, Store);

    // ── Compile module ──────────────────────────────────────────────────
    wasmtime_error_t* CompileErr = wasmtime_module_new(
        Engine, WasmBytes.GetData(), WasmBytes.Num(), &Module);
    if (CompileErr)
    {
        wasm_message_t Msg;
        wasmtime_error_message(CompileErr, &Msg);
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Compile error: %hs"),
               (const char*)Msg.data);
        wasm_byte_vec_delete(&Msg);
        wasmtime_error_delete(CompileErr);
        ShutdownWasm();
        return false;
    }

    // ── Instantiate ─────────────────────────────────────────────────────
    wasm_trap_t* Trap = nullptr;
    Instance = new wasmtime_instance_t;
    wasmtime_error_t* InstErr = wasmtime_linker_instantiate(
        Linker, Ctx, Module, Instance, &Trap);
    if (InstErr || Trap)
    {
        if (InstErr)
        {
            wasm_message_t Msg;
            wasmtime_error_message(InstErr, &Msg);
            UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Instantiation error: %hs"),
                   (const char*)Msg.data);
            wasm_byte_vec_delete(&Msg);
            wasmtime_error_delete(InstErr);
        }
        if (Trap)
        {
            wasm_message_t Msg;
            wasm_trap_message(Trap, &Msg);
            UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Instantiation trap: %hs"),
                   (const char*)Msg.data);
            wasm_byte_vec_delete(&Msg);
            wasm_trap_delete(Trap);
        }
        ShutdownWasm();
        return false;
    }

    // ── Resolve memory export ───────────────────────────────────────────
    wasmtime_extern_t MemExt;
    if (wasmtime_instance_export_get(Ctx, Instance, "memory", 6, &MemExt)
        && MemExt.kind == WASMTIME_EXTERN_MEMORY)
    {
        Memory = new wasmtime_memory_t;
        *Memory = MemExt.of.memory;
    }
    else
    {
        UE_LOG(LogTemp, Warning, TEXT("[SimpleWasm] No 'memory' export — out-pointer writes will fail"));
    }

    // ── Resolve export function indices ─────────────────────────────────
    wasmtime_extern_t Ext;

    if (wasmtime_instance_export_get(Ctx, Instance, "game_init", 9, &Ext)
        && Ext.kind == WASMTIME_EXTERN_FUNC)
    {
        FuncInit = 0; // Mark as available
    }

    if (wasmtime_instance_export_get(Ctx, Instance, "game_update", 11, &Ext)
        && Ext.kind == WASMTIME_EXTERN_FUNC)
    {
        FuncUpdate = 1;
    }

    if (wasmtime_instance_export_get(Ctx, Instance, "game_shutdown", 13, &Ext)
        && Ext.kind == WASMTIME_EXTERN_FUNC)
    {
        FuncShutdown = 2;
    }

    bModuleLoaded = true;
    UE_LOG(LogTemp, Log, TEXT("[SimpleWasm] Module loaded: %s (init=%d update=%d shutdown=%d)"),
           *FullPath, FuncInit >= 0, FuncUpdate >= 0, FuncShutdown >= 0);
    return true;
}

void USimpleWasmBridge::ShutdownWasm()
{
    bModuleLoaded = false;
    FuncInit = FuncUpdate = FuncShutdown = -1;

    if (Memory)   { delete Memory;   Memory   = nullptr; }
    if (Instance) { delete Instance; Instance = nullptr; }
    if (Module)   { wasmtime_module_delete(Module); Module = nullptr; }
    if (Linker)   { wasmtime_linker_delete(Linker); Linker = nullptr; }
    if (Store)    { wasmtime_store_delete(Store);   Store  = nullptr; }
    if (Engine)   { wasm_engine_delete(Engine);     Engine = nullptr; }
}

// ============================================================================
// Hot-reload
// ============================================================================

void USimpleWasmBridge::CheckHotReload(float DeltaTime)
{
    HotReloadTimer += DeltaTime;
    if (HotReloadTimer < HotReloadPollInterval)
        return;
    HotReloadTimer = 0.0f;

    FString FullPath = WasmPath;
    if (FPaths::IsRelative(FullPath))
    {
        FullPath = FPaths::Combine(FPaths::ProjectContentDir(), FullPath);
    }
    FullPath = FPaths::ConvertRelativePathToFull(FullPath);

    FDateTime CurrentTime = FPlatformFileManager::Get().GetPlatformFile()
                                .GetTimeStamp(*FullPath);

    if (CurrentTime > LastModifiedTime)
    {
        UE_LOG(LogTemp, Log, TEXT("[SimpleWasm] File changed, reloading: %s"), *FullPath);
        ReloadModule();
    }
}

void USimpleWasmBridge::ReloadModule()
{
    // Call shutdown on old module
    ActiveBridge = this;
    if (bModuleLoaded && FuncShutdown >= 0)
    {
        wasmtime_context_t* Ctx = wasmtime_store_context(Store);
        wasmtime_extern_t Ext;
        if (wasmtime_instance_export_get(Ctx, Instance, "game_shutdown", 13, &Ext)
            && Ext.kind == WASMTIME_EXTERN_FUNC)
        {
            wasmtime_func_call(Ctx, &Ext.of.func, nullptr, 0, nullptr, 0, nullptr);
        }
    }

    // Tear down old instance
    ShutdownWasm();

    // Clear handle tables for fresh state
    Entities.Reset();
    Materials.Reset();
    AudioSources.Reset();
    Assets.Reset();

    // Reload
    if (LoadAndInstantiate())
    {
        // Call game_init on new module
        if (FuncInit >= 0)
        {
            wasmtime_context_t* Ctx = wasmtime_store_context(Store);
            wasmtime_extern_t Ext;
            if (wasmtime_instance_export_get(Ctx, Instance, "game_init", 9, &Ext)
                && Ext.kind == WASMTIME_EXTERN_FUNC)
            {
                wasmtime_func_t Func = Ext.of.func;
                wasmtime_func_call(Ctx, &Func, nullptr, 0, nullptr, 0, nullptr);
            }
        }
        UE_LOG(LogTemp, Log, TEXT("[SimpleWasm] Hot-reload complete."));
    }
    else
    {
        UE_LOG(LogTemp, Error, TEXT("[SimpleWasm] Hot-reload failed."));
    }

    ActiveBridge = nullptr;
}

// ============================================================================
// Memory helpers
// ============================================================================

uint8* USimpleWasmBridge::GetMemoryData() const
{
    if (!Memory || !Store)
        return nullptr;

    wasmtime_context_t* Ctx = wasmtime_store_context(Store);
    return wasmtime_memory_data(Ctx, Memory);
}

void USimpleWasmBridge::WriteVec3(int32 OutPtr, float X, float Y, float Z) const
{
    uint8* Base = GetMemoryData();
    if (!Base)
        return;

    float* Dst = reinterpret_cast<float*>(Base + OutPtr);
    Dst[0] = X;
    Dst[1] = Y;
    Dst[2] = Z;
}

void USimpleWasmBridge::WriteVec4(int32 OutPtr, float X, float Y, float Z, float W) const
{
    uint8* Base = GetMemoryData();
    if (!Base)
        return;

    float* Dst = reinterpret_cast<float*>(Base + OutPtr);
    Dst[0] = X;
    Dst[1] = Y;
    Dst[2] = Z;
    Dst[3] = W;
}

FString USimpleWasmBridge::ReadString(int32 Ptr, int32 Len) const
{
    uint8* Base = GetMemoryData();
    if (!Base || Len <= 0)
        return FString();

    // WASM strings are UTF-8
    FUTF8ToTCHAR Converter(reinterpret_cast<const ANSICHAR*>(Base + Ptr), Len);
    return FString(Converter.Length(), Converter.Get());
}
