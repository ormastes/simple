// InputBridge.cpp - engine_input_* WASM host functions
// Part of SimpleWasm Unreal bridge
//
// Implements 8 functions:
//   engine_input_is_key_pressed, engine_input_is_key_just_pressed,
//   engine_input_is_key_just_released, engine_input_get_mouse_position,
//   engine_input_get_mouse_delta, engine_input_is_mouse_button_pressed,
//   engine_input_get_axis, engine_input_is_action_pressed

#include "WasmBridge.h"

#include "GameFramework/PlayerController.h"
#include "Kismet/GameplayStatics.h"
#include "Engine/World.h"
#include "InputCoreTypes.h"

#include <wasmtime.h>

// ── Helpers ─────────────────────────────────────────────────────────────────

namespace
{

/** Map a Simple key code (i32) to an Unreal FKey.
 *  Key code mapping follows the Simple Game3D key enum order. */
FKey KeyCodeToFKey(int32 Code)
{
    // Letters 0-25 → A-Z
    if (Code >= 0 && Code <= 25)
    {
        static const FKey Letters[] = {
            EKeys::A, EKeys::B, EKeys::C, EKeys::D, EKeys::E, EKeys::F,
            EKeys::G, EKeys::H, EKeys::I, EKeys::J, EKeys::K, EKeys::L,
            EKeys::M, EKeys::N, EKeys::O, EKeys::P, EKeys::Q, EKeys::R,
            EKeys::S, EKeys::T, EKeys::U, EKeys::V, EKeys::W, EKeys::X,
            EKeys::Y, EKeys::Z
        };
        return Letters[Code];
    }
    // 26-35 → 0-9
    if (Code >= 26 && Code <= 35)
    {
        static const FKey Digits[] = {
            EKeys::Zero, EKeys::One, EKeys::Two, EKeys::Three, EKeys::Four,
            EKeys::Five, EKeys::Six, EKeys::Seven, EKeys::Eight, EKeys::Nine
        };
        return Digits[Code - 26];
    }
    // Special keys
    switch (Code)
    {
        case 36: return EKeys::SpaceBar;
        case 37: return EKeys::Enter;
        case 38: return EKeys::Escape;
        case 39: return EKeys::Tab;
        case 40: return EKeys::LeftShift;
        case 41: return EKeys::LeftControl;
        case 42: return EKeys::LeftAlt;
        case 43: return EKeys::Up;
        case 44: return EKeys::Down;
        case 45: return EKeys::Left;
        case 46: return EKeys::Right;
        default: return EKeys::Invalid;
    }
}

FKey MouseButtonToFKey(int32 Button)
{
    switch (Button)
    {
        case 0: return EKeys::LeftMouseButton;
        case 1: return EKeys::RightMouseButton;
        case 2: return EKeys::MiddleMouseButton;
        default: return EKeys::Invalid;
    }
}

APlayerController* GetPC()
{
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (!Bridge) return nullptr;

    UWorld* World = Bridge->GetWorld();
    if (!World) return nullptr;

    return UGameplayStatics::GetPlayerController(World, 0);
}

} // anon namespace

// ── Callback implementations ────────────────────────────────────────────────

static wasm_trap_t* CB_input_is_key_pressed(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 KeyCode = Args[0].of.i32;
    APlayerController* PC = GetPC();
    bool bPressed = false;
    if (PC)
    {
        bPressed = PC->IsInputKeyDown(KeyCodeToFKey(KeyCode));
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPressed ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_input_is_key_just_pressed(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 KeyCode = Args[0].of.i32;
    APlayerController* PC = GetPC();
    bool bPressed = false;
    if (PC)
    {
        bPressed = PC->WasInputKeyJustPressed(KeyCodeToFKey(KeyCode));
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPressed ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_input_is_key_just_released(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 KeyCode = Args[0].of.i32;
    APlayerController* PC = GetPC();
    bool bPressed = false;
    if (PC)
    {
        bPressed = PC->WasInputKeyJustReleased(KeyCodeToFKey(KeyCode));
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPressed ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_input_get_mouse_position(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 OutPtr = Args[0].of.i32;
    APlayerController* PC = GetPC();
    float MX = 0.0f, MY = 0.0f;
    if (PC)
    {
        PC->GetMousePosition(MX, MY);
    }
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        uint8* Base = Bridge->GetMemoryData();
        if (Base)
        {
            float* Dst = reinterpret_cast<float*>(Base + OutPtr);
            Dst[0] = MX;
            Dst[1] = MY;
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_input_get_mouse_delta(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 OutPtr = Args[0].of.i32;
    APlayerController* PC = GetPC();
    float DX = 0.0f, DY = 0.0f;
    if (PC)
    {
        PC->GetInputMouseDelta(DX, DY);
    }
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        uint8* Base = Bridge->GetMemoryData();
        if (Base)
        {
            float* Dst = reinterpret_cast<float*>(Base + OutPtr);
            Dst[0] = DX;
            Dst[1] = DY;
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_input_is_mouse_button_pressed(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Button = Args[0].of.i32;
    APlayerController* PC = GetPC();
    bool bPressed = false;
    if (PC)
    {
        bPressed = PC->IsInputKeyDown(MouseButtonToFKey(Button));
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPressed ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_input_get_axis(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 NamePtr = Args[0].of.i32;
    int32 NameLen = Args[1].of.i32;

    float Value = 0.0f;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString AxisName = Bridge->ReadString(NamePtr, NameLen);
        APlayerController* PC = GetPC();
        if (PC)
        {
            Value = PC->GetInputAxisValue(FName(*AxisName));
        }
    }

    Results[0].kind = WASMTIME_F32;
    Results[0].of.f32 = Value;
    return nullptr;
}

static wasm_trap_t* CB_input_is_action_pressed(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 ActionPtr = Args[0].of.i32;
    int32 ActionLen = Args[1].of.i32;

    bool bPressed = false;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString ActionName = Bridge->ReadString(ActionPtr, ActionLen);
        APlayerController* PC = GetPC();
        if (PC)
        {
            bPressed = PC->IsInputKeyDown(FKey(*ActionName));
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = bPressed ? 1 : 0;
    return nullptr;
}

// ── Registration ────────────────────────────────────────────────────────────

namespace
{

/** Helper: define a function in the linker under module "engine". */
void DefineFunc(wasmtime_linker_t* Linker, const char* Name,
                wasmtime_func_callback_t CB,
                const wasm_valtype_t* ParamTypes[], size_t NumParams,
                const wasm_valtype_t* ResultTypes[], size_t NumResults)
{
    wasm_functype_t* FuncType = wasm_functype_new(
        &(wasm_valtype_vec_t){NumParams, const_cast<wasm_valtype_t**>(ParamTypes)},
        &(wasm_valtype_vec_t){NumResults, const_cast<wasm_valtype_t**>(ResultTypes)});

    wasmtime_error_t* Err = wasmtime_linker_define_func(
        Linker, "engine", 6, Name, FString(Name).Len(),
        FuncType, CB, nullptr, nullptr);

    if (Err)
    {
        wasmtime_error_delete(Err);
    }

    wasm_functype_delete(FuncType);
}

} // anon namespace

void SimpleWasm::RegisterInputFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    // Shared valtype singletons
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_input_is_key_pressed(key_code: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_input_is_key_pressed",
                   CB_input_is_key_pressed, P, 1, R, 1);
    }
    // engine_input_is_key_just_pressed(key_code: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_input_is_key_just_pressed",
                   CB_input_is_key_just_pressed, P, 1, R, 1);
    }
    // engine_input_is_key_just_released(key_code: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_input_is_key_just_released",
                   CB_input_is_key_just_released, P, 1, R, 1);
    }
    // engine_input_get_mouse_position(out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_input_get_mouse_position",
                   CB_input_get_mouse_position, P, 1, nullptr, 0);
    }
    // engine_input_get_mouse_delta(out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_input_get_mouse_delta",
                   CB_input_get_mouse_delta, P, 1, nullptr, 0);
    }
    // engine_input_is_mouse_button_pressed(button: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_input_is_mouse_button_pressed",
                   CB_input_is_mouse_button_pressed, P, 1, R, 1);
    }
    // engine_input_get_axis(axis_name_ptr: i32, axis_name_len: i32) -> f32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { F32 };
        DefineFunc(Linker, "engine_input_get_axis",
                   CB_input_get_axis, P, 2, R, 1);
    }
    // engine_input_is_action_pressed(action_ptr: i32, action_len: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_input_is_action_pressed",
                   CB_input_is_action_pressed, P, 2, R, 1);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}
