// AudioBridge.cpp - engine_audio_* WASM host functions
// Part of SimpleWasm Unreal bridge
//
// Implements 8 functions:
//   engine_audio_load, engine_audio_play, engine_audio_stop,
//   engine_audio_set_volume, engine_audio_set_pitch,
//   engine_audio_set_spatial, engine_audio_set_position,
//   engine_audio_is_playing

#include "WasmBridge.h"

#include "Components/AudioComponent.h"
#include "Sound/SoundWave.h"
#include "Kismet/GameplayStatics.h"
#include "Engine/World.h"
#include "UObject/Package.h"

#include <wasmtime.h>

// ── Helper ──────────────────────────────────────────────────────────────────

namespace
{

void DefineFunc(wasmtime_linker_t* Linker, const char* Name,
                wasmtime_func_callback_t CB,
                const wasm_valtype_t* ParamTypes[], size_t NumParams,
                const wasm_valtype_t* ResultTypes[], size_t NumResults)
{
    wasm_functype_t* FuncType = wasm_functype_new(
        &(wasm_valtype_vec_t){NumParams, const_cast<wasm_valtype_t**>(ParamTypes)},
        &(wasm_valtype_vec_t){NumResults, const_cast<wasm_valtype_t**>(ResultTypes)});

    wasmtime_error_t* Err = wasmtime_linker_define_func(
        Linker, "engine", 6, Name, FCStringAnsi::Strlen(Name),
        FuncType, CB, nullptr, nullptr);

    if (Err) wasmtime_error_delete(Err);
    wasm_functype_delete(FuncType);
}

} // anon namespace

// ── Callback implementations ────────────────────────────────────────────────

static wasm_trap_t* CB_audio_load(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 PathPtr = Args[0].of.i32;
    int32 PathLen = Args[1].of.i32;

    int32 Handle = -1;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString AssetPath = Bridge->ReadString(PathPtr, PathLen);

        // Load the SoundWave asset
        USoundWave* Sound = LoadObject<USoundWave>(nullptr, *AssetPath);
        if (Sound)
        {
            // Create an AudioComponent parented to the bridge's owner actor
            AActor* Owner = Bridge->GetOwner();
            UAudioComponent* AudioComp = NewObject<UAudioComponent>(Owner);
            AudioComp->SetSound(Sound);
            AudioComp->bAutoActivate = false;
            AudioComp->bAutoDestroy = false;
            AudioComp->AttachToComponent(Owner->GetRootComponent(),
                                          FAttachmentTransformRules::KeepRelativeTransform);
            AudioComp->RegisterComponent();

            Handle = USimpleWasmBridge::AudioSources.Add(AudioComp);
        }
        else
        {
            UE_LOG(LogTemp, Warning, TEXT("[SimpleWasm] audio_load: asset not found: %s"), *AssetPath);
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_audio_play(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        Comp->Play();
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_stop(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        Comp->Stop();
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_set_volume(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    float Volume = Args[1].of.f32;

    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        Comp->SetVolumeMultiplier(Volume);
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_set_pitch(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    float Pitch = Args[1].of.f32;

    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        Comp->SetPitchMultiplier(Pitch);
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_set_spatial(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    int32 Entity = Args[1].of.i32;

    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);

    if (Comp && Actor)
    {
        // Detach from current parent and attach to the entity actor
        Comp->DetachFromComponent(FDetachmentTransformRules::KeepWorldTransform);
        Comp->AttachToComponent(Actor->GetRootComponent(),
                                FAttachmentTransformRules::SnapToTargetNotIncludingScale);
        // Enable spatialization
        Comp->bAllowSpatialization = true;
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_set_position(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;
    float X = Args[1].of.f32;
    float Y = Args[2].of.f32;
    float Z = Args[3].of.f32;

    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        Comp->SetWorldLocation(FVector(X, Y, Z));
    }
    return nullptr;
}

static wasm_trap_t* CB_audio_is_playing(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AudioId = Args[0].of.i32;

    bool bPlaying = false;
    UAudioComponent* Comp = USimpleWasmBridge::AudioSources.Get(AudioId);
    if (Comp)
    {
        bPlaying = Comp->IsPlaying();
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPlaying ? 1 : 0;
    return nullptr;
}

// ── Registration ────────────────────────────────────────────────────────────

void SimpleWasm::RegisterAudioFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_audio_load(path_ptr: i32, path_len: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_audio_load",
                   CB_audio_load, P, 2, R, 1);
    }
    // engine_audio_play(audio_id: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_audio_play",
                   CB_audio_play, P, 1, nullptr, 0);
    }
    // engine_audio_stop(audio_id: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_audio_stop",
                   CB_audio_stop, P, 1, nullptr, 0);
    }
    // engine_audio_set_volume(audio_id: i32, volume: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_audio_set_volume",
                   CB_audio_set_volume, P, 2, nullptr, 0);
    }
    // engine_audio_set_pitch(audio_id: i32, pitch: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_audio_set_pitch",
                   CB_audio_set_pitch, P, 2, nullptr, 0);
    }
    // engine_audio_set_spatial(audio_id: i32, entity: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_audio_set_spatial",
                   CB_audio_set_spatial, P, 2, nullptr, 0);
    }
    // engine_audio_set_position(audio_id: i32, x: f32, y: f32, z: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_audio_set_position",
                   CB_audio_set_position, P, 4, nullptr, 0);
    }
    // engine_audio_is_playing(audio_id: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_audio_is_playing",
                   CB_audio_is_playing, P, 1, R, 1);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}
