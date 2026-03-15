// RenderBridge.cpp - engine_render_*, engine_entity_*, engine_transform_*,
//                    engine_asset_*, engine_debug_* WASM host functions
// Part of SimpleWasm Unreal bridge
//
// Implements all remaining functions (40 total):
//   Entity (8), Transform (12), Render (14), Asset (4), Debug (2)

#include "WasmBridge.h"

#include "Engine/World.h"
#include "Engine/StaticMesh.h"
#include "Engine/Texture2D.h"
#include "GameFramework/Actor.h"
#include "EngineUtils.h"
#include "Components/StaticMeshComponent.h"
#include "Components/SceneComponent.h"
#include "Components/LightComponent.h"
#include "Components/PointLightComponent.h"
#include "Components/SpotLightComponent.h"
#include "Components/DirectionalLightComponent.h"
#include "Camera/CameraComponent.h"
#include "Materials/MaterialInstanceDynamic.h"
#include "Kismet/GameplayStatics.h"
#include "DrawDebugHelpers.h"
#include "Sound/SoundWave.h"

#include <wasm.h>
#include <wasmtime.h>

// ── Shared DefineFunc helper ────────────────────────────────────────────────

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

/** Get the engine primitive mesh by type index.
 *  0=Cube, 1=Sphere, 2=Cylinder, 3=Cone, 4=Plane */
UStaticMesh* GetEnginePrimitive(int32 Type)
{
    static const TCHAR* Paths[] = {
        TEXT("/Engine/BasicShapes/Cube.Cube"),
        TEXT("/Engine/BasicShapes/Sphere.Sphere"),
        TEXT("/Engine/BasicShapes/Cylinder.Cylinder"),
        TEXT("/Engine/BasicShapes/Cone.Cone"),
        TEXT("/Engine/BasicShapes/Plane.Plane"),
    };

    if (Type < 0 || Type > 4) Type = 0;
    return LoadObject<UStaticMesh>(nullptr, Paths[Type]);
}

} // anon namespace

// ============================================================================
// Entity callbacks (8)
// ============================================================================

static wasm_trap_t* CB_entity_create(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Handle = -1;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FActorSpawnParameters Params;
            Params.SpawnCollisionHandlingOverride = ESpawnActorCollisionHandlingMethod::AlwaysSpawn;
            AActor* Actor = World->SpawnActor<AActor>(AActor::StaticClass(),
                                                       &FTransform::Identity, Params);
            if (Actor)
            {
                USceneComponent* Root = NewObject<USceneComponent>(Actor, TEXT("Root"));
                Actor->SetRootComponent(Root);
                Root->RegisterComponent();
                Handle = USimpleWasmBridge::Entities.Add(Actor);
            }
        }
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_entity_create_named(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 NamePtr = Args[0].of.i32;
    int32 NameLen = Args[1].of.i32;

    int32 Handle = -1;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString Name = Bridge->ReadString(NamePtr, NameLen);
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FActorSpawnParameters Params;
            Params.Name = FName(*Name);
            Params.SpawnCollisionHandlingOverride = ESpawnActorCollisionHandlingMethod::AlwaysSpawn;
            AActor* Actor = World->SpawnActor<AActor>(AActor::StaticClass(),
                                                       &FTransform::Identity, Params);
            if (Actor)
            {
                USceneComponent* Root = NewObject<USceneComponent>(Actor, TEXT("Root"));
                Actor->SetRootComponent(Root);
                Root->RegisterComponent();
                Actor->SetActorLabel(Name);
                Handle = USimpleWasmBridge::Entities.Add(Actor);
            }
        }
    }
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_entity_destroy(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->Destroy();
        USimpleWasmBridge::Entities.Remove(Entity);
    }
    return nullptr;
}

static wasm_trap_t* CB_entity_set_active(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 Active = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->SetActorHiddenInGame(!Active);
        Actor->SetActorEnableCollision(Active != 0);
        Actor->SetActorTickEnabled(Active != 0);
    }
    return nullptr;
}

static wasm_trap_t* CB_entity_is_active(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = (Actor && !Actor->IsHidden()) ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_entity_set_parent(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 Parent = Args[1].of.i32;

    AActor* Child = USimpleWasmBridge::Entities.Get(Entity);
    AActor* ParentActor = USimpleWasmBridge::Entities.Get(Parent);
    if (Child && ParentActor)
    {
        Child->AttachToActor(ParentActor, FAttachmentTransformRules::KeepRelativeTransform);
    }
    return nullptr;
}

static wasm_trap_t* CB_entity_set_name(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 NamePtr = Args[1].of.i32;
    int32 NameLen = Args[2].of.i32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FString Name = Bridge->ReadString(NamePtr, NameLen);
        Actor->SetActorLabel(Name);
    }
    return nullptr;
}

static wasm_trap_t* CB_entity_find_by_name(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 NamePtr = Args[0].of.i32;
    int32 NameLen = Args[1].of.i32;

    int32 Handle = -1;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString Name = Bridge->ReadString(NamePtr, NameLen);
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            for (TActorIterator<AActor> It(World); It; ++It)
            {
                if (It->GetActorLabel() == Name)
                {
                    Handle = USimpleWasmBridge::Entities.Add(*It);
                    break;
                }
            }
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

// ============================================================================
// Transform callbacks (12)
// ============================================================================

static wasm_trap_t* CB_transform_get_position(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FVector Pos = Actor->GetActorLocation();
        Bridge->WriteVec3(OutPtr, Pos.X, Pos.Y, Pos.Z);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_set_position(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float X = Args[1].of.f32;
    float Y = Args[2].of.f32;
    float Z = Args[3].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->SetActorLocation(FVector(X, Y, Z));
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_get_rotation(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FQuat Rot = Actor->GetActorQuat();
        Bridge->WriteVec4(OutPtr, Rot.X, Rot.Y, Rot.Z, Rot.W);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_set_rotation(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float X = Args[1].of.f32;
    float Y = Args[2].of.f32;
    float Z = Args[3].of.f32;
    float W = Args[4].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->SetActorRotation(FQuat(X, Y, Z, W));
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_get_scale(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FVector Scale = Actor->GetActorScale3D();
        Bridge->WriteVec3(OutPtr, Scale.X, Scale.Y, Scale.Z);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_set_scale(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float X = Args[1].of.f32;
    float Y = Args[2].of.f32;
    float Z = Args[3].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->SetActorScale3D(FVector(X, Y, Z));
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_look_at(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float TX = Args[1].of.f32;
    float TY = Args[2].of.f32;
    float TZ = Args[3].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        FVector Target(TX, TY, TZ);
        FVector Dir = (Target - Actor->GetActorLocation()).GetSafeNormal();
        if (!Dir.IsNearlyZero())
        {
            Actor->SetActorRotation(Dir.Rotation());
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_translate(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float DX = Args[1].of.f32;
    float DY = Args[2].of.f32;
    float DZ = Args[3].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        Actor->AddActorWorldOffset(FVector(DX, DY, DZ));
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_rotate(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float AX = Args[1].of.f32;
    float AY = Args[2].of.f32;
    float AZ = Args[3].of.f32;
    float Angle = Args[4].of.f32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        FQuat Rotation = FQuat(FVector(AX, AY, AZ).GetSafeNormal(), FMath::DegreesToRadians(Angle));
        Actor->AddActorWorldRotation(Rotation);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_get_forward(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FVector Fwd = Actor->GetActorForwardVector();
        Bridge->WriteVec3(OutPtr, Fwd.X, Fwd.Y, Fwd.Z);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_get_up(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FVector Up = Actor->GetActorUpVector();
        Bridge->WriteVec3(OutPtr, Up.X, Up.Y, Up.Z);
    }
    return nullptr;
}

static wasm_trap_t* CB_transform_get_right(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;
    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        FVector Right = Actor->GetActorRightVector();
        Bridge->WriteVec3(OutPtr, Right.X, Right.Y, Right.Z);
    }
    return nullptr;
}

// ============================================================================
// Render callbacks (14)
// ============================================================================

static wasm_trap_t* CB_render_set_mesh(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 MeshType = Args[1].of.i32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        UStaticMeshComponent* MeshComp = Actor->FindComponentByClass<UStaticMeshComponent>();
        if (!MeshComp)
        {
            MeshComp = NewObject<UStaticMeshComponent>(Actor);
            MeshComp->AttachToComponent(Actor->GetRootComponent(),
                                         FAttachmentTransformRules::KeepRelativeTransform);
            MeshComp->RegisterComponent();
        }
        MeshComp->SetStaticMesh(GetEnginePrimitive(MeshType));
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_mesh_asset(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 AssetId = Args[1].of.i32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    UObject* Asset = USimpleWasmBridge::Assets.Get(AssetId);
    if (Actor && Asset)
    {
        UStaticMesh* Mesh = Cast<UStaticMesh>(Asset);
        if (Mesh)
        {
            UStaticMeshComponent* MeshComp = Actor->FindComponentByClass<UStaticMeshComponent>();
            if (!MeshComp)
            {
                MeshComp = NewObject<UStaticMeshComponent>(Actor);
                MeshComp->AttachToComponent(Actor->GetRootComponent(),
                                             FAttachmentTransformRules::KeepRelativeTransform);
                MeshComp->RegisterComponent();
            }
            MeshComp->SetStaticMesh(Mesh);
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_material(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 MaterialId = Args[1].of.i32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    UMaterialInstanceDynamic* Mat = USimpleWasmBridge::Materials.Get(MaterialId);
    if (Actor && Mat)
    {
        UStaticMeshComponent* MeshComp = Actor->FindComponentByClass<UStaticMeshComponent>();
        if (MeshComp)
        {
            MeshComp->SetMaterial(0, Mat);
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_create_material(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Handle = -1;

    UMaterialInterface* BaseMat = LoadObject<UMaterialInterface>(
        nullptr, TEXT("/Engine/EngineMaterials/DefaultMaterial.DefaultMaterial"));
    if (BaseMat)
    {
        UMaterialInstanceDynamic* MID = UMaterialInstanceDynamic::Create(BaseMat, nullptr);
        if (MID)
        {
            Handle = USimpleWasmBridge::Materials.Add(MID);
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_render_set_material_color(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 MaterialId = Args[0].of.i32;
    float R = Args[1].of.f32;
    float G = Args[2].of.f32;
    float B = Args[3].of.f32;
    float A = Args[4].of.f32;

    UMaterialInstanceDynamic* Mat = USimpleWasmBridge::Materials.Get(MaterialId);
    if (Mat)
    {
        Mat->SetVectorParameterValue(FName("BaseColor"), FLinearColor(R, G, B, A));
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_material_texture(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 MaterialId = Args[0].of.i32;
    int32 Slot = Args[1].of.i32;
    int32 TextureId = Args[2].of.i32;

    UMaterialInstanceDynamic* Mat = USimpleWasmBridge::Materials.Get(MaterialId);
    UObject* TexObj = USimpleWasmBridge::Assets.Get(TextureId);
    UTexture* Tex = TexObj ? Cast<UTexture>(TexObj) : nullptr;

    if (Mat && Tex)
    {
        // Slot 0 = BaseColor texture, 1 = Normal, 2 = Roughness
        static const FName SlotNames[] = {
            FName("BaseColorTexture"),
            FName("NormalTexture"),
            FName("RoughnessTexture"),
        };
        FName ParamName = (Slot >= 0 && Slot <= 2) ? SlotNames[Slot] : SlotNames[0];
        Mat->SetTextureParameterValue(ParamName, Tex);
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_material_float(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 MaterialId = Args[0].of.i32;
    int32 Param = Args[1].of.i32;
    float Value = Args[2].of.f32;

    UMaterialInstanceDynamic* Mat = USimpleWasmBridge::Materials.Get(MaterialId);
    if (Mat)
    {
        // Param 0=Metallic, 1=Roughness, 2=Specular, 3=Opacity
        static const FName ParamNames[] = {
            FName("Metallic"), FName("Roughness"),
            FName("Specular"), FName("Opacity"),
        };
        FName ParamName = (Param >= 0 && Param <= 3) ? ParamNames[Param] : ParamNames[0];
        Mat->SetScalarParameterValue(ParamName, Value);
    }
    return nullptr;
}

static wasm_trap_t* CB_render_create_light(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 LightType = Args[0].of.i32;
    int32 Handle = -1;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FActorSpawnParameters Params;
            Params.SpawnCollisionHandlingOverride = ESpawnActorCollisionHandlingMethod::AlwaysSpawn;
            AActor* LightActor = World->SpawnActor<AActor>(AActor::StaticClass(),
                                                            &FTransform::Identity, Params);
            if (LightActor)
            {
                USceneComponent* Root = NewObject<USceneComponent>(LightActor, TEXT("Root"));
                LightActor->SetRootComponent(Root);
                Root->RegisterComponent();

                ULightComponent* LightComp = nullptr;
                switch (LightType)
                {
                    case 0: // Point
                        LightComp = NewObject<UPointLightComponent>(LightActor);
                        break;
                    case 1: // Spot
                        LightComp = NewObject<USpotLightComponent>(LightActor);
                        break;
                    case 2: // Directional
                        LightComp = NewObject<UDirectionalLightComponent>(LightActor);
                        break;
                    default:
                        LightComp = NewObject<UPointLightComponent>(LightActor);
                        break;
                }

                if (LightComp)
                {
                    LightComp->AttachToComponent(Root,
                                                  FAttachmentTransformRules::KeepRelativeTransform);
                    LightComp->RegisterComponent();
                }

                Handle = USimpleWasmBridge::Entities.Add(LightActor);
            }
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_render_set_light_color(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Light = Args[0].of.i32;
    float R = Args[1].of.f32;
    float G = Args[2].of.f32;
    float B = Args[3].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Light);
    if (Actor)
    {
        ULightComponent* LightComp = Actor->FindComponentByClass<ULightComponent>();
        if (LightComp)
        {
            LightComp->SetLightColor(FLinearColor(R, G, B));
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_light_intensity(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Light = Args[0].of.i32;
    float Intensity = Args[1].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Light);
    if (Actor)
    {
        ULightComponent* LightComp = Actor->FindComponentByClass<ULightComponent>();
        if (LightComp)
        {
            LightComp->SetIntensity(Intensity);
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_create_camera(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Handle = -1;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FActorSpawnParameters Params;
            Params.SpawnCollisionHandlingOverride = ESpawnActorCollisionHandlingMethod::AlwaysSpawn;
            AActor* CamActor = World->SpawnActor<AActor>(AActor::StaticClass(),
                                                          &FTransform::Identity, Params);
            if (CamActor)
            {
                USceneComponent* Root = NewObject<USceneComponent>(CamActor, TEXT("Root"));
                CamActor->SetRootComponent(Root);
                Root->RegisterComponent();

                UCameraComponent* CamComp = NewObject<UCameraComponent>(CamActor);
                CamComp->AttachToComponent(Root,
                                            FAttachmentTransformRules::KeepRelativeTransform);
                CamComp->RegisterComponent();

                Handle = USimpleWasmBridge::Entities.Add(CamActor);
            }
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_render_set_camera_fov(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Camera = Args[0].of.i32;
    float FOV = Args[1].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Camera);
    if (Actor)
    {
        UCameraComponent* CamComp = Actor->FindComponentByClass<UCameraComponent>();
        if (CamComp)
        {
            CamComp->SetFieldOfView(FOV);
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_set_camera_active(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Camera = Args[0].of.i32;
    int32 Active = Args[1].of.i32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Camera);
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Actor && Bridge)
    {
        UCameraComponent* CamComp = Actor->FindComponentByClass<UCameraComponent>();
        if (CamComp && Active)
        {
            APlayerController* PC = UGameplayStatics::GetPlayerController(Bridge->GetWorld(), 0);
            if (PC)
            {
                PC->SetViewTargetWithBlend(Actor, 0.0f);
            }
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_render_create_primitive(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 PrimType = Args[0].of.i32;
    int32 Handle = -1;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FActorSpawnParameters Params;
            Params.SpawnCollisionHandlingOverride = ESpawnActorCollisionHandlingMethod::AlwaysSpawn;
            AActor* Actor = World->SpawnActor<AActor>(AActor::StaticClass(),
                                                       &FTransform::Identity, Params);
            if (Actor)
            {
                USceneComponent* Root = NewObject<USceneComponent>(Actor, TEXT("Root"));
                Actor->SetRootComponent(Root);
                Root->RegisterComponent();

                UStaticMeshComponent* MeshComp = NewObject<UStaticMeshComponent>(Actor);
                MeshComp->SetStaticMesh(GetEnginePrimitive(PrimType));
                MeshComp->AttachToComponent(Root,
                                             FAttachmentTransformRules::KeepRelativeTransform);
                MeshComp->RegisterComponent();

                Handle = USimpleWasmBridge::Entities.Add(Actor);
            }
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

// ============================================================================
// Asset callbacks (4)
// ============================================================================

static wasm_trap_t* CB_asset_load(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 PathPtr = Args[0].of.i32;
    int32 PathLen = Args[1].of.i32;
    int32 AssetType = Args[2].of.i32;

    int32 Handle = -1;
    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString Path = Bridge->ReadString(PathPtr, PathLen);
        UObject* Asset = nullptr;

        switch (AssetType)
        {
            case 0: // StaticMesh
                Asset = LoadObject<UStaticMesh>(nullptr, *Path);
                break;
            case 1: // Texture
                Asset = LoadObject<UTexture2D>(nullptr, *Path);
                break;
            case 2: // Sound
                Asset = LoadObject<USoundWave>(nullptr, *Path);
                break;
            case 3: // Material
                Asset = LoadObject<UMaterialInterface>(nullptr, *Path);
                break;
            default:
                Asset = LoadObject<UObject>(nullptr, *Path);
                break;
        }

        if (Asset)
        {
            Handle = USimpleWasmBridge::Assets.Add(Asset);
        }
        else
        {
            UE_LOG(LogTemp, Warning, TEXT("[SimpleWasm] asset_load: not found: %s (type=%d)"),
                   *Path, AssetType);
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

static wasm_trap_t* CB_asset_is_loaded(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AssetId = Args[0].of.i32;
    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = USimpleWasmBridge::Assets.Contains(AssetId) ? 1 : 0;
    return nullptr;
}

static wasm_trap_t* CB_asset_unload(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 AssetId = Args[0].of.i32;
    USimpleWasmBridge::Assets.Remove(AssetId);
    return nullptr;
}

static wasm_trap_t* CB_asset_load_texture(
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
        FString Path = Bridge->ReadString(PathPtr, PathLen);
        UTexture2D* Tex = LoadObject<UTexture2D>(nullptr, *Path);
        if (Tex)
        {
            Handle = USimpleWasmBridge::Assets.Add(Tex);
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = Handle;
    return nullptr;
}

// ============================================================================
// Debug callbacks (2)
// ============================================================================

static wasm_trap_t* CB_debug_log(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 MsgPtr = Args[0].of.i32;
    int32 MsgLen = Args[1].of.i32;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        FString Msg = Bridge->ReadString(MsgPtr, MsgLen);
        UE_LOG(LogTemp, Log, TEXT("[SimpleWasm] %s"), *Msg);

        if (GEngine)
        {
            GEngine->AddOnScreenDebugMessage(-1, 5.0f, FColor::Cyan, Msg);
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_debug_draw_line(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    float X1 = Args[0].of.f32;
    float Y1 = Args[1].of.f32;
    float Z1 = Args[2].of.f32;
    float X2 = Args[3].of.f32;
    float Y2 = Args[4].of.f32;
    float Z2 = Args[5].of.f32;
    float R  = Args[6].of.f32;
    float G  = Args[7].of.f32;
    float B  = Args[8].of.f32;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FColor Color(
                FMath::Clamp(static_cast<int32>(R * 255.0f), 0, 255),
                FMath::Clamp(static_cast<int32>(G * 255.0f), 0, 255),
                FMath::Clamp(static_cast<int32>(B * 255.0f), 0, 255)
            );
            DrawDebugLine(World,
                          FVector(X1, Y1, Z1),
                          FVector(X2, Y2, Z2),
                          Color,
                          false,  // bPersistentLines
                          -1.0f,  // LifeTime (one frame)
                          0,      // DepthPriority
                          1.0f);  // Thickness
        }
    }
    return nullptr;
}

// ============================================================================
// Registration — Entity, Transform, Render, Asset, Debug
// ============================================================================

void SimpleWasm::RegisterEntityFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);

    // engine_entity_create() -> i32
    {
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_entity_create",
                   CB_entity_create, nullptr, 0, R, 1);
    }
    // engine_entity_create_named(name_ptr: i32, name_len: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_entity_create_named",
                   CB_entity_create_named, P, 2, R, 1);
    }
    // engine_entity_destroy(entity: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_entity_destroy",
                   CB_entity_destroy, P, 1, nullptr, 0);
    }
    // engine_entity_set_active(entity: i32, active: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_entity_set_active",
                   CB_entity_set_active, P, 2, nullptr, 0);
    }
    // engine_entity_is_active(entity: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_entity_is_active",
                   CB_entity_is_active, P, 1, R, 1);
    }
    // engine_entity_set_parent(entity: i32, parent: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_entity_set_parent",
                   CB_entity_set_parent, P, 2, nullptr, 0);
    }
    // engine_entity_set_name(entity: i32, name_ptr: i32, name_len: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32, I32 };
        DefineFunc(Linker, "engine_entity_set_name",
                   CB_entity_set_name, P, 3, nullptr, 0);
    }
    // engine_entity_find_by_name(name_ptr: i32, name_len: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_entity_find_by_name",
                   CB_entity_find_by_name, P, 2, R, 1);
    }

    wasm_valtype_delete(I32);
}

void SimpleWasm::RegisterTransformFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_transform_get_position(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_position",
                   CB_transform_get_position, P, 2, nullptr, 0);
    }
    // engine_transform_set_position(entity: i32, x: f32, y: f32, z: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_set_position",
                   CB_transform_set_position, P, 4, nullptr, 0);
    }
    // engine_transform_get_rotation(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_rotation",
                   CB_transform_get_rotation, P, 2, nullptr, 0);
    }
    // engine_transform_set_rotation(entity: i32, x: f32, y: f32, z: f32, w: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_set_rotation",
                   CB_transform_set_rotation, P, 5, nullptr, 0);
    }
    // engine_transform_get_scale(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_scale",
                   CB_transform_get_scale, P, 2, nullptr, 0);
    }
    // engine_transform_set_scale(entity: i32, x: f32, y: f32, z: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_set_scale",
                   CB_transform_set_scale, P, 4, nullptr, 0);
    }
    // engine_transform_look_at(entity: i32, x: f32, y: f32, z: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_look_at",
                   CB_transform_look_at, P, 4, nullptr, 0);
    }
    // engine_transform_translate(entity: i32, dx: f32, dy: f32, dz: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_translate",
                   CB_transform_translate, P, 4, nullptr, 0);
    }
    // engine_transform_rotate(entity: i32, axis_x: f32, axis_y: f32, axis_z: f32, angle: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32, F32 };
        DefineFunc(Linker, "engine_transform_rotate",
                   CB_transform_rotate, P, 5, nullptr, 0);
    }
    // engine_transform_get_forward(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_forward",
                   CB_transform_get_forward, P, 2, nullptr, 0);
    }
    // engine_transform_get_up(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_up",
                   CB_transform_get_up, P, 2, nullptr, 0);
    }
    // engine_transform_get_right(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_transform_get_right",
                   CB_transform_get_right, P, 2, nullptr, 0);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}

void SimpleWasm::RegisterRenderFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_render_set_mesh(entity: i32, mesh_type: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_render_set_mesh",
                   CB_render_set_mesh, P, 2, nullptr, 0);
    }
    // engine_render_set_mesh_asset(entity: i32, asset_id: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_render_set_mesh_asset",
                   CB_render_set_mesh_asset, P, 2, nullptr, 0);
    }
    // engine_render_set_material(entity: i32, material_id: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_render_set_material",
                   CB_render_set_material, P, 2, nullptr, 0);
    }
    // engine_render_create_material() -> i32
    {
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_render_create_material",
                   CB_render_create_material, nullptr, 0, R, 1);
    }
    // engine_render_set_material_color(material: i32, r: f32, g: f32, b: f32, a: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32, F32 };
        DefineFunc(Linker, "engine_render_set_material_color",
                   CB_render_set_material_color, P, 5, nullptr, 0);
    }
    // engine_render_set_material_texture(material: i32, slot: i32, texture_id: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32, I32 };
        DefineFunc(Linker, "engine_render_set_material_texture",
                   CB_render_set_material_texture, P, 3, nullptr, 0);
    }
    // engine_render_set_material_float(material: i32, param: i32, value: f32)
    {
        const wasm_valtype_t* P[] = { I32, I32, F32 };
        DefineFunc(Linker, "engine_render_set_material_float",
                   CB_render_set_material_float, P, 3, nullptr, 0);
    }
    // engine_render_create_light(light_type: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_render_create_light",
                   CB_render_create_light, P, 1, R, 1);
    }
    // engine_render_set_light_color(light: i32, r: f32, g: f32, b: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_render_set_light_color",
                   CB_render_set_light_color, P, 4, nullptr, 0);
    }
    // engine_render_set_light_intensity(light: i32, intensity: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_render_set_light_intensity",
                   CB_render_set_light_intensity, P, 2, nullptr, 0);
    }
    // engine_render_create_camera() -> i32
    {
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_render_create_camera",
                   CB_render_create_camera, nullptr, 0, R, 1);
    }
    // engine_render_set_camera_fov(camera: i32, fov: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_render_set_camera_fov",
                   CB_render_set_camera_fov, P, 2, nullptr, 0);
    }
    // engine_render_set_camera_active(camera: i32, active: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_render_set_camera_active",
                   CB_render_set_camera_active, P, 2, nullptr, 0);
    }
    // engine_render_create_primitive(prim_type: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_render_create_primitive",
                   CB_render_create_primitive, P, 1, R, 1);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}

void SimpleWasm::RegisterAssetFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);

    // engine_asset_load(path_ptr: i32, path_len: i32, asset_type: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_asset_load",
                   CB_asset_load, P, 3, R, 1);
    }
    // engine_asset_is_loaded(asset_id: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_asset_is_loaded",
                   CB_asset_is_loaded, P, 1, R, 1);
    }
    // engine_asset_unload(asset_id: i32)
    {
        const wasm_valtype_t* P[] = { I32 };
        DefineFunc(Linker, "engine_asset_unload",
                   CB_asset_unload, P, 1, nullptr, 0);
    }
    // engine_asset_load_texture(path_ptr: i32, path_len: i32) -> i32
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_asset_load_texture",
                   CB_asset_load_texture, P, 2, R, 1);
    }

    wasm_valtype_delete(I32);
}

void SimpleWasm::RegisterDebugFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_debug_log(msg_ptr: i32, msg_len: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_debug_log",
                   CB_debug_log, P, 2, nullptr, 0);
    }
    // engine_debug_draw_line(x1,y1,z1,x2,y2,z2, r,g,b)
    {
        const wasm_valtype_t* P[] = { F32, F32, F32, F32, F32, F32, F32, F32, F32 };
        DefineFunc(Linker, "engine_debug_draw_line",
                   CB_debug_draw_line, P, 9, nullptr, 0);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}
