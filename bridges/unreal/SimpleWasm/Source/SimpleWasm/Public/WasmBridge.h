// WasmBridge.h - UActorComponent that loads Simple WASM and bridges to Unreal
// Part of SimpleWasm Unreal bridge

#pragma once

#include "CoreMinimal.h"
#include "Components/ActorComponent.h"
#include "HandleTable.h"

// Forward-declare wasmtime opaque types (from wasmtime C API)
struct wasmtime_engine;
struct wasmtime_store;
struct wasmtime_linker;
struct wasmtime_module;
struct wasmtime_instance;
struct wasmtime_memory;
typedef struct wasmtime_engine wasm_engine_t;

#include "WasmBridge.generated.h"

class UAudioComponent;
class UMaterialInstanceDynamic;

// ============================================================================
// Bridge function categories — forward declarations for static registrars
// ============================================================================

namespace SimpleWasm
{
    // Each bridge file provides a static registration function
    void RegisterEntityFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterTransformFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterRenderFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterInputFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterPhysicsFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterAudioFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterAssetFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
    void RegisterDebugFunctions(struct wasmtime_linker* Linker, struct wasmtime_store* Store);
}

// ============================================================================
// USimpleWasmBridge — the main bridge component
// ============================================================================

UCLASS(ClassGroup=(Scripting), meta=(BlueprintSpawnableComponent))
class SIMPLEWASM_API USimpleWasmBridge : public UActorComponent
{
    GENERATED_BODY()

public:
    USimpleWasmBridge();

    // ── Configuration ───────────────────────────────────────────────────

    /** Path to the .wasm file (relative to project Content dir or absolute). */
    UPROPERTY(EditAnywhere, BlueprintReadWrite, Category = "SimpleWasm")
    FString WasmPath;

    /** If true, watch the .wasm file and reload on change. */
    UPROPERTY(EditAnywhere, BlueprintReadWrite, Category = "SimpleWasm")
    bool bEnableHotReload = false;

    /** Interval in seconds to poll the file for changes (hot-reload). */
    UPROPERTY(EditAnywhere, BlueprintReadWrite, Category = "SimpleWasm",
              meta = (EditCondition = "bEnableHotReload", ClampMin = "0.1"))
    float HotReloadPollInterval = 1.0f;

    // ── Lifecycle ───────────────────────────────────────────────────────

    virtual void BeginPlay() override;
    virtual void TickComponent(float DeltaTime, ELevelTick TickType,
                               FActorComponentTickFunction* ThisTickFunction) override;
    virtual void EndPlay(const EEndPlayReason::Type EndPlayReason) override;

    // ── Hot-reload ──────────────────────────────────────────────────────

    /** Force-reload the WASM module right now. */
    UFUNCTION(BlueprintCallable, Category = "SimpleWasm")
    void ReloadModule();

    // ── Handle tables (global, accessed by bridge statics) ──────────────

    static HandleTable<AActor>                     Entities;
    static HandleTable<UMaterialInstanceDynamic>   Materials;
    static HandleTable<UAudioComponent>            AudioSources;
    static HandleTable<UObject>                    Assets;

    /** Currently active bridge instance (set during tick). */
    static USimpleWasmBridge* ActiveBridge;

    // ── WASM memory helpers ─────────────────────────────────────────────

    /** Get pointer into linear WASM memory at the given byte offset. */
    uint8* GetMemoryData() const;

    /** Write 3 floats into WASM memory at byte offset. */
    void WriteVec3(int32 OutPtr, float X, float Y, float Z) const;

    /** Write 4 floats into WASM memory at byte offset. */
    void WriteVec4(int32 OutPtr, float X, float Y, float Z, float W) const;

    /** Read a UTF-8 string from WASM memory. */
    FString ReadString(int32 Ptr, int32 Len) const;

private:
    // ── Internal ────────────────────────────────────────────────────────

    bool LoadAndInstantiate();
    void ShutdownWasm();
    void CheckHotReload(float DeltaTime);

    // wasmtime handles (opaque pointers to avoid exposing C header)
    wasm_engine_t*              Engine   = nullptr;
    struct wasmtime_store*      Store    = nullptr;
    struct wasmtime_linker*     Linker   = nullptr;
    struct wasmtime_module*     Module   = nullptr;
    struct wasmtime_instance*   Instance = nullptr;
    struct wasmtime_memory*     Memory   = nullptr;

    // Export function indices (resolved once after instantiation)
    int32 FuncInit     = -1;
    int32 FuncUpdate   = -1;
    int32 FuncShutdown = -1;

    // Hot-reload state
    FDateTime LastModifiedTime;
    float     HotReloadTimer = 0.0f;
    bool      bModuleLoaded  = false;
};
