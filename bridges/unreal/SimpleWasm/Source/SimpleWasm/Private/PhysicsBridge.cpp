// PhysicsBridge.cpp - engine_physics_* WASM host functions
// Part of SimpleWasm Unreal bridge
//
// Implements 12 functions:
//   engine_physics_add_rigidbody, engine_physics_set_mass,
//   engine_physics_set_velocity, engine_physics_get_velocity,
//   engine_physics_add_force, engine_physics_add_impulse,
//   engine_physics_add_collider_box, engine_physics_add_collider_sphere,
//   engine_physics_add_collider_capsule, engine_physics_raycast,
//   engine_physics_set_gravity, engine_physics_set_collision_layer

#include "WasmBridge.h"

#include "Components/PrimitiveComponent.h"
#include "Components/BoxComponent.h"
#include "Components/SphereComponent.h"
#include "Components/CapsuleComponent.h"
#include "Engine/World.h"
#include "PhysicsEngine/PhysicsSettings.h"
#include "CollisionQueryParams.h"

#include <wasmtime.h>

// ── Helpers ─────────────────────────────────────────────────────────────────

namespace
{

/** Get the first UPrimitiveComponent on the actor for physics ops. */
UPrimitiveComponent* GetPrimitive(int32 EntityHandle)
{
    AActor* Actor = USimpleWasmBridge::Entities.Get(EntityHandle);
    if (!Actor) return nullptr;
    return Cast<UPrimitiveComponent>(Actor->GetRootComponent());
}

// Forward-declare the DefineFunc helper (shared pattern)
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

// body_type: 0=static, 1=kinematic, 2=dynamic
static wasm_trap_t* CB_physics_add_rigidbody(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 BodyType = Args[1].of.i32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Prim->SetSimulatePhysics(BodyType == 2); // dynamic
        if (BodyType == 1)
        {
            // Kinematic: simulate off but enable physics body
            Prim->SetSimulatePhysics(false);
            Prim->BodyInstance.SetCollisionEnabled(ECollisionEnabled::QueryAndPhysics);
        }
        Prim->SetEnableGravity(BodyType == 2);
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_set_mass(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float Mass = Args[1].of.f32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Prim->SetMassOverrideInKg(NAME_None, Mass, true);
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_set_velocity(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float VX = Args[1].of.f32;
    float VY = Args[2].of.f32;
    float VZ = Args[3].of.f32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Prim->SetPhysicsLinearVelocity(FVector(VX, VY, VZ));
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_get_velocity(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 OutPtr = Args[1].of.i32;

    FVector Vel = FVector::ZeroVector;
    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Vel = Prim->GetPhysicsLinearVelocity();
    }

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        Bridge->WriteVec3(OutPtr, Vel.X, Vel.Y, Vel.Z);
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_add_force(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float FX = Args[1].of.f32;
    float FY = Args[2].of.f32;
    float FZ = Args[3].of.f32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Prim->AddForce(FVector(FX, FY, FZ));
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_add_impulse(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float IX = Args[1].of.f32;
    float IY = Args[2].of.f32;
    float IZ = Args[3].of.f32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        Prim->AddImpulse(FVector(IX, IY, IZ));
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_add_collider_box(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float HX = Args[1].of.f32;
    float HY = Args[2].of.f32;
    float HZ = Args[3].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        UBoxComponent* Box = NewObject<UBoxComponent>(Actor);
        Box->SetBoxExtent(FVector(HX, HY, HZ));
        Box->SetCollisionEnabled(ECollisionEnabled::QueryAndPhysics);
        Box->SetGenerateOverlapEvents(true);
        Box->AttachToComponent(Actor->GetRootComponent(),
                               FAttachmentTransformRules::KeepRelativeTransform);
        Box->RegisterComponent();
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_add_collider_sphere(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float Radius = Args[1].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        USphereComponent* Sphere = NewObject<USphereComponent>(Actor);
        Sphere->SetSphereRadius(Radius);
        Sphere->SetCollisionEnabled(ECollisionEnabled::QueryAndPhysics);
        Sphere->SetGenerateOverlapEvents(true);
        Sphere->AttachToComponent(Actor->GetRootComponent(),
                                  FAttachmentTransformRules::KeepRelativeTransform);
        Sphere->RegisterComponent();
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_add_collider_capsule(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    float Radius = Args[1].of.f32;
    float Height = Args[2].of.f32;

    AActor* Actor = USimpleWasmBridge::Entities.Get(Entity);
    if (Actor)
    {
        UCapsuleComponent* Capsule = NewObject<UCapsuleComponent>(Actor);
        Capsule->SetCapsuleSize(Radius, Height * 0.5f);
        Capsule->SetCollisionEnabled(ECollisionEnabled::QueryAndPhysics);
        Capsule->SetGenerateOverlapEvents(true);
        Capsule->AttachToComponent(Actor->GetRootComponent(),
                                   FAttachmentTransformRules::KeepRelativeTransform);
        Capsule->RegisterComponent();
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_raycast(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    float OX = Args[0].of.f32;
    float OY = Args[1].of.f32;
    float OZ = Args[2].of.f32;
    float DX = Args[3].of.f32;
    float DY = Args[4].of.f32;
    float DZ = Args[5].of.f32;
    float MaxDist = Args[6].of.f32;
    int32 OutPtr = Args[7].of.i32;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    int32 HitEntity = -1;

    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            FVector Start(OX, OY, OZ);
            FVector Dir(DX, DY, DZ);
            Dir.Normalize();
            FVector End = Start + Dir * MaxDist;

            FHitResult Hit;
            FCollisionQueryParams QueryParams;
            QueryParams.bTraceComplex = false;
            QueryParams.bReturnPhysicalMaterial = false;

            if (World->LineTraceSingleByChannel(Hit, Start, End,
                                                 ECC_Visibility, QueryParams))
            {
                // Write hit result: [hit_x, hit_y, hit_z, hit_normal_x, hit_normal_y, hit_normal_z, distance]
                uint8* Base = Bridge->GetMemoryData();
                if (Base)
                {
                    float* Dst = reinterpret_cast<float*>(Base + OutPtr);
                    Dst[0] = Hit.ImpactPoint.X;
                    Dst[1] = Hit.ImpactPoint.Y;
                    Dst[2] = Hit.ImpactPoint.Z;
                    Dst[3] = Hit.ImpactNormal.X;
                    Dst[4] = Hit.ImpactNormal.Y;
                    Dst[5] = Hit.ImpactNormal.Z;
                    Dst[6] = Hit.Distance;
                }

                // Try to find the hit actor in our entity table
                // (linear scan — fine for typical entity counts)
                AActor* HitActor = Hit.GetActor();
                if (HitActor)
                {
                    // Search entities for matching actor
                    // HandleTable doesn't expose iteration, so we check known handles
                    // In a production build, maintain a reverse map
                    HitEntity = 0; // Placeholder — hit detected but entity unknown
                }
            }
        }
    }

    Results[0].kind = WASMTIME_I32;
    Results[0].of.i32 = HitEntity;
    return nullptr;
}

static wasm_trap_t* CB_physics_set_gravity(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    float GX = Args[0].of.f32;
    float GY = Args[1].of.f32;
    float GZ = Args[2].of.f32;

    USimpleWasmBridge* Bridge = USimpleWasmBridge::ActiveBridge;
    if (Bridge)
    {
        UWorld* World = Bridge->GetWorld();
        if (World)
        {
            // Unreal uses cm/s^2. Simple uses m/s^2 convention — scale by 100.
            AWorldSettings* Settings = World->GetWorldSettings();
            if (Settings)
            {
                Settings->GlobalGravityZ = GZ * 100.0f;
            }
        }
    }
    return nullptr;
}

static wasm_trap_t* CB_physics_set_collision_layer(
    void* Env, wasmtime_caller_t* Caller,
    const wasmtime_val_t* Args, size_t NumArgs,
    wasmtime_val_t* Results, size_t NumResults)
{
    int32 Entity = Args[0].of.i32;
    int32 Layer = Args[1].of.i32;
    int32 Mask = Args[2].of.i32;

    UPrimitiveComponent* Prim = GetPrimitive(Entity);
    if (Prim)
    {
        // Map layer/mask to Unreal collision channels
        // Layer 0-5 maps to ECC_GameTraceChannel1-6
        ECollisionChannel Channel = static_cast<ECollisionChannel>(
            ECC_GameTraceChannel1 + FMath::Clamp(Layer, 0, 5));

        Prim->SetCollisionObjectType(Channel);

        // Apply mask as response channels
        FCollisionResponseContainer Response;
        Response.SetAllChannels(ECR_Ignore);
        for (int32 i = 0; i < 6; ++i)
        {
            if (Mask & (1 << i))
            {
                Response.SetResponse(
                    static_cast<ECollisionChannel>(ECC_GameTraceChannel1 + i),
                    ECR_Block);
            }
        }
        Prim->SetCollisionResponseToChannels(Response);
    }
    return nullptr;
}

// ── Registration ────────────────────────────────────────────────────────────

void SimpleWasm::RegisterPhysicsFunctions(wasmtime_linker_t* Linker, wasmtime_store_t* Store)
{
    wasm_valtype_t* I32 = wasm_valtype_new(WASM_I32);
    wasm_valtype_t* F32 = wasm_valtype_new(WASM_F32);

    // engine_physics_add_rigidbody(entity: i32, body_type: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_physics_add_rigidbody",
                   CB_physics_add_rigidbody, P, 2, nullptr, 0);
    }
    // engine_physics_set_mass(entity: i32, mass: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_physics_set_mass",
                   CB_physics_set_mass, P, 2, nullptr, 0);
    }
    // engine_physics_set_velocity(entity: i32, vx: f32, vy: f32, vz: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_physics_set_velocity",
                   CB_physics_set_velocity, P, 4, nullptr, 0);
    }
    // engine_physics_get_velocity(entity: i32, out_ptr: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32 };
        DefineFunc(Linker, "engine_physics_get_velocity",
                   CB_physics_get_velocity, P, 2, nullptr, 0);
    }
    // engine_physics_add_force(entity: i32, fx: f32, fy: f32, fz: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_physics_add_force",
                   CB_physics_add_force, P, 4, nullptr, 0);
    }
    // engine_physics_add_impulse(entity: i32, ix: f32, iy: f32, iz: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_physics_add_impulse",
                   CB_physics_add_impulse, P, 4, nullptr, 0);
    }
    // engine_physics_add_collider_box(entity: i32, hx: f32, hy: f32, hz: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32, F32 };
        DefineFunc(Linker, "engine_physics_add_collider_box",
                   CB_physics_add_collider_box, P, 4, nullptr, 0);
    }
    // engine_physics_add_collider_sphere(entity: i32, radius: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32 };
        DefineFunc(Linker, "engine_physics_add_collider_sphere",
                   CB_physics_add_collider_sphere, P, 2, nullptr, 0);
    }
    // engine_physics_add_collider_capsule(entity: i32, radius: f32, height: f32)
    {
        const wasm_valtype_t* P[] = { I32, F32, F32 };
        DefineFunc(Linker, "engine_physics_add_collider_capsule",
                   CB_physics_add_collider_capsule, P, 3, nullptr, 0);
    }
    // engine_physics_raycast(ox,oy,oz, dx,dy,dz, max_dist, out_ptr) -> i32
    {
        const wasm_valtype_t* P[] = { F32, F32, F32, F32, F32, F32, F32, I32 };
        const wasm_valtype_t* R[] = { I32 };
        DefineFunc(Linker, "engine_physics_raycast",
                   CB_physics_raycast, P, 8, R, 1);
    }
    // engine_physics_set_gravity(gx: f32, gy: f32, gz: f32)
    {
        const wasm_valtype_t* P[] = { F32, F32, F32 };
        DefineFunc(Linker, "engine_physics_set_gravity",
                   CB_physics_set_gravity, P, 3, nullptr, 0);
    }
    // engine_physics_set_collision_layer(entity: i32, layer: i32, mask: i32)
    {
        const wasm_valtype_t* P[] = { I32, I32, I32 };
        DefineFunc(Linker, "engine_physics_set_collision_layer",
                   CB_physics_set_collision_layer, P, 3, nullptr, 0);
    }

    wasm_valtype_delete(I32);
    wasm_valtype_delete(F32);
}
