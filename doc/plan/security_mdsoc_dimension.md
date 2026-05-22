# Security as an MDSOC Dimension

## Core Idea

For Simple, security should be modeled as a dimension in MDSOC, not as scattered checks inside services.

MDSOC's original point is that concerns can be decomposed across multiple dimensions instead of being trapped in one hierarchy; Hyper/Net describes MDSOC as decomposition by dimensions and concerns, with units composed through rules.  Simple already has first-class MDSOC manifests, architecture-aware structure, AOP pointcuts, compile-time weaving, SDN-backed project data, runtime-family boundaries, and mock/security-like enforcement gates, so the security model should extend these existing mechanisms instead of inventing a separate framework.

The rule should be:

Business code cannot directly call privileged code.
Only declared security gates may cross security boundaries.
AOP/weaving inserts and verifies those gates.
SDN/source policy declares which crossings are legal.
Sandbox policy is generated from the same graph.


---

## 1. Security Dimensions for MDSOC

Define at least these dimensions:

layer:      ui | api | service | domain | infra | driver | kernel
feature:    user | admin | billing | auth | audit | debug
security:   public | authenticated | user_private | admin_only | system
trust:      app | plugin | third_party | untrusted | kernel
runtime:    gc | nogc | async | baremetal | sandboxed

Then every module/file/class/function gets a coordinate:

@mdsoc(
    layer = service,
    feature = user,
    security = user_private,
    trust = app,
)
class UserProfileService:
    ...

Folder convention should infer most of it:

src/feature/user/service/profile.spl
=> layer=service, feature=user

src/feature/admin/service/user_admin.spl
=> layer=service, feature=admin

src/security/user_gate.spl
=> feature=security, layer=security_gate

Do not require annotation everywhere. Use annotation only for exceptions.


---

## 2. Layer-Skipping Prevention

Most architectures check only this:

ui -> service -> domain -> infra

But the dangerous case is skipping:

user/ui -> user/domain -> admin/infra

So enforce two independent constraints:

Layer rule:
    ui may call api/service only
    service may call domain/security_gate only
    domain may call port/interface only
    infra may implement port only

Feature rule:
    user feature cannot call admin feature
    admin feature may call user feature only through declared gate
    any feature crossing must use security gate

Example forbidden call:

# src/feature/user/service/profile.spl

class UserProfileService:
    fn delete_user(id: UserId):
        AdminUserRepo.delete(id)   # compile error

Diagnostic:

SEC201 forbidden feature crossing:
  from: feature=user, layer=service
  to:   feature=admin, layer=infra

Use one of:
  security.user_admin_gate.delete_user(...)
  declare allow in security.sdn
  move shared logic to feature=common


---

## 3. Security Gate as Mandatory Mediation Point

Create a special construct:

security gate UserAdminGate:
    from feature user
    to feature admin
    allow fn request_delete_user(actor: UserActor, target: UserId) -> DeleteRequest
    require policy CanRequestUserDelete
    audit UserDeleteRequested

Implementation must live only under security folder:

src/security/gate/user_admin_gate.spl
src/security/policy/can_request_user_delete.spl
src/security/audit/user_delete_audit.spl

Then user feature code can call only the gate:

class UserProfileService:
    init(gate: UserAdminGate):
        self.gate = gate

    fn request_delete(id: UserId):
        self.gate.request_delete_user(current_user(), id)

The gate performs policy, logging, capability narrowing, and optional sandbox transition.

security gate UserAdminGate:
    from feature user
    to feature admin

    fn request_delete_user(actor: UserActor, target: UserId) -> DeleteRequest:
        require actor.authenticated
        require policy CanRequestUserDelete(actor, target)
        audit UserDeleteRequested(actor.id, target)
        return AdminDeleteRequest(target)

Important: ordinary business folders cannot define security gate.

Only src/security/** or folder marked security_root may define gates.

This prevents security logic scattering.


---

## 4. AOP Rule: Gate Insertion and Gate Verification

Use AOP for two things:

1. Prevent bypass: reject direct calls crossing restricted dimensions.
2. Insert checks: weave policy/audit/sandbox code around gate methods.

Simple already has predicate-based AOP pointcuts with execution, within, attr, deterministic before/after/around advice, compile-time weaving by default, and scoped runtime interception.  That is almost exactly what this security system needs.

Proposed syntax:

security aspect GateEnforcement:
    forbid call from feature(user) to feature(admin)
        unless through security_gate(UserAdminGate)

    around execution(security_gate.*):
        SecurityRuntime.enter_gate(this_gate)
        try:
            proceed()
        finally:
            SecurityRuntime.exit_gate(this_gate)

More concrete:

security aspect FeatureBoundary:
    forbid call:
        from feature user
        to feature admin
        unless gate UserAdminGate

    forbid import:
        from feature user
        to feature admin
        unless target is interface and layer is port

The compiler should build a call/import graph and fail build if a crossing has no declared gate.


---

## 5. Source Policy Grammar

Use security block as first-class grammar.

security AppSecurity:
    root src/security

    dimension layer:
        order ui -> api -> service -> domain -> port -> infra
        forbid skip_layer unless gate

    dimension feature:
        isolate user
        isolate admin
        allow admin -> user through AdminUserGate
        allow user -> admin through UserAdminGate

    gate UserAdminGate:
        from feature user
        to feature admin
        policy CanRequestAdminAction
        audit all
        sandbox admin_sandbox

    gate AuthGate:
        from security public
        to security authenticated
        policy RequireLogin
        audit failure

Use security instead of only generic AOP because security needs stronger compiler semantics.

AOP should be the implementation mechanism; security should be the user-facing DSL.


---

## 6. SDN Security Config

Equivalent SDN:

security:
    root: src/security
    default: deny

    dimensions:
        layer:
            order: [ui, api, service, domain, port, infra]
            forbid_skip: true

        feature:
            isolated: [user, admin, billing, debug]
            shared: [common, auth, security]

    gates:
        UserAdminGate:
            from:
                feature: user
            to:
                feature: admin
            policy: CanRequestAdminAction
            audit: all
            sandbox: admin_sandbox

        AuthGate:
            from:
                security: public
            to:
                security: authenticated
            policy: RequireLogin
            audit: failure

    allow:
        - from: { feature: admin, layer: service }
          to:   { feature: user, layer: service }
          through: AdminUserGate

    deny:
        - from: { feature: user }
          to:   { feature: admin }
          except: [UserAdminGate]

For large projects, table format:

security_gate |name, from_feature, to_feature, policy, audit, sandbox|
    UserAdminGate, user, admin, CanRequestAdminAction, all, admin_sandbox
    AuthGate, public, authenticated, RequireLogin, failure, web_sandbox

security_deny |from_feature, to_feature, except_gate|
    user, admin, UserAdminGate
    plugin, infra, PluginInfraGate


---

## 7. Sandbox as Another Security Effect

Sandbox should be attachable to:

whole app
library
feature
layer
folder
class
function
gate
runtime plugin

Example source syntax:

sandbox admin_sandbox:
    backend landlock
    fs:
        read ["/etc/simple/admin.conf"]
        write ["/var/lib/simple/audit"]
    net:
        deny all
    env:
        allow ["SIMPLE_ENV"]
    syscall:
        profile strict

Example use:

security gate UserAdminGate:
    from feature user
    to feature admin
    sandbox admin_sandbox
    policy CanRequestAdminAction

Meaning:

When user feature enters admin feature through this gate,
execute target in admin_sandbox or under admin_sandbox restrictions.

For Linux, Landlock is a good backend model because it restricts ambient rights such as filesystem/network access and stacks with existing system access controls.  For portable plugin/module sandboxing, WASI is a useful reference because WASI is capability-based: external resource access is provided by explicit capabilities.  Capsicum is another useful OS design reference because it is a lightweight capability/sandbox framework.

So Simple should define an abstract sandbox policy and lower it to:

Target                  Backend
Linux hosted app        Landlock + seccomp + namespaces
FreeBSD/Simple OS idea  Capsicum-like capability mode
Simple VM/plugin        WASM/WASI-like capabilities
Baremetal               linker sections + MPU/MMU regions
Simple OS future        native object-capability handles


---

## 8. Capability-Based API Should Replace Raw Global Access

Do not let sandboxed code call:

File.open("/etc/passwd")
Network.connect("...")
Env.get("SECRET")

Instead require explicit capabilities:

class ReportPlugin:
    init(fs: ReadDir["/reports"], log: AuditLog):
        self.fs = fs
        self.log = log

Gate grants narrowed capabilities:

security gate PluginGate:
    from trust app
    to trust plugin
    sandbox plugin_sandbox

    grant:
        ReadDir["/reports"]
        WriteDir["/tmp/plugin"]
        AuditLog

Then plugin code cannot accidentally escape because it has no ambient authority.

This is the same design direction as WASI: do not ask "who is the user?" first; ask "which capabilities did this module receive?"


---

## 9. Prevent Security Scattering

Add compiler rule:

SECURITY_ROOT rule:
    Files outside security roots cannot:
      - define security policies
      - perform authorization decisions
      - call raw permission APIs
      - create sandbox/capability grants
      - suppress security diagnostics

Allowed:

src/security/**
src/feature/*/security_interface.spl

Forbidden:

# src/feature/user/service/profile.spl

if current_user().is_admin:       # warning/error if used as authorization
    AdminRepo.delete(id)

Instead:

self.gate.request_delete_user(current_user(), id)

Use lints:

SEC301 scattered authorization:
  Authorization predicate used outside security root:
    current_user().is_admin

Move this check to:
  src/security/policy/*.spl
or mark as non-authoritative:
  @security_observation

Need exception for UI hiding:

@security_observation
fn can_show_admin_button() -> Bool:
    return current_user().has_hint("admin")

Observation can hide UI, but cannot authorize.


---

## 10. Layer + Feature Access Matrix

Generate a matrix from source and SDN:

                to user     to admin    to billing   to infra
from user       allow       gate only   deny         deny
from admin      gate only   allow       gate only    deny direct
from billing    deny        deny        allow        port only
from plugin     deny        deny        deny         gate only

Compiler emits:

build/security/access_matrix.generated.sdn
build/security/gate_inventory.md
build/security/sandbox_manifest.sdn
build/security/violations.sdn

This is important for Simple because SDN-backed project metadata already exists in the repo story.


---

## 11. Suggested Language Additions

### 11.1 security block

security AppSecurity:
    root src/security
    default deny

    allow feature admin -> feature user through AdminUserGate
    deny feature user -> feature admin except UserAdminGate

### 11.2 security gate

security gate UserAdminGate:
    from feature user
    to feature admin
    policy CanRequestAdminAction
    audit all
    sandbox admin_sandbox

    fn request_delete_user(actor: UserActor, target: UserId) -> DeleteRequest:
        ...

### 11.3 sandbox

sandbox plugin_sandbox:
    backend auto
    fs read ["/app/plugins/data"]
    fs write ["/tmp/simple/plugin"]
    net deny all
    cpu max_ms 50
    memory max_mb 64

### 11.4 capability

capability ReadUserProfile:
    resource UserProfile
    actions [read]
    scope actor.user_id == resource.owner_id

### 11.5 @dimension

@dimension(feature = user, layer = service)
class UserProfileService:
    ...

### 11.6 @security_observation

For UI-only hints:

@security_observation
fn show_admin_menu(user: User) -> Bool:
    user.roles.contains("admin")

This cannot guard privileged execution.


---

## 12. AOP Integration Design

Security DSL lowers into AOP plus graph checks.

security AppSecurity:
    deny feature user -> feature admin except UserAdminGate

lowers into:

aspect GeneratedSecurityBoundary:
    forbid call:
        from within(feature=user)
        to within(feature=admin)
        unless within(security_gate=UserAdminGate)

Gate:

security gate UserAdminGate:
    policy CanRequestAdminAction
    audit all

lowers into:

aspect GeneratedUserAdminGateAdvice:
    around execution(UserAdminGate.*):
        SecurityContext.push_gate("UserAdminGate")
        PolicyRuntime.require(CanRequestAdminAction, args)
        Audit.log_start(...)
        try:
            result = proceed()
            Audit.log_success(...)
            return result
        except e:
            Audit.log_failure(...)
            raise e
        finally:
            SecurityContext.pop_gate()

Compile-time weaving should be default. Runtime interception only for dynamic plugins or debugging, matching Simple's existing AOP backend distinction.


---

## 13. Sandbox Lowering Pipeline

security.sdn / source security block
        |
security graph
        |
gate graph + capability graph
        |
sandbox manifest
        |
backend lowering
        +-- Linux: Landlock/seccomp/namespaces
        +-- WASM: WASI capabilities
        +-- Simple VM: bytecode/module capability table
        +-- Baremetal: linker section + MPU/MMU
        +-- Simple OS: native capability handles

Example generated sandbox manifest:

sandbox_manifest:
    PluginSandbox:
        backend: auto
        capabilities:
            - ReadDir("/app/plugins/data")
            - WriteDir("/tmp/simple/plugin")
            - AuditLog
        deny:
            - Network
            - ProcessSpawn
            - RawDevice


---

## 14. Handling Admin/User Feature Example

Folder tree:

src/
  feature/
    user/
      service/profile.spl
      domain/user_profile.spl
    admin/
      service/user_admin.spl
      infra/admin_user_repo.spl
  security/
    gate/user_admin_gate.spl
    policy/can_request_admin_action.spl
    sandbox/admin_sandbox.spl

Policy:

security AppSecurity:
    root src/security
    default deny

    allow feature user -> feature admin through UserAdminGate
    allow feature admin -> feature user through AdminUserGate

    forbid feature user -> feature admin direct
    forbid layer service -> layer infra direct

Gate:

security gate UserAdminGate:
    from feature user
    to feature admin
    policy CanRequestAdminAction
    audit all
    sandbox admin_sandbox

    fn request_user_delete(actor: UserActor, target: UserId) -> DeleteRequest:
        require CanRequestAdminAction(actor, "request_user_delete", target)
        return DeleteRequest(target)

User code:

class UserProfileService:
    init(gate: UserAdminGate):
        self.gate = gate

    fn request_delete_my_account(actor: UserActor):
        self.gate.request_user_delete(actor, actor.user_id)

Forbidden:

class UserProfileService:
    fn bad(actor: UserActor):
        AdminUserRepo.delete(actor.user_id)

Compiler:

SEC201 feature-boundary violation:
  user.service.UserProfileService.bad
  directly calls admin.infra.AdminUserRepo.delete

Required crossing:
  UserAdminGate.request_user_delete


---

## 15. Build/Test Hardening

Add commands:

simple security check
simple security matrix
simple security explain src/feature/user/service/profile.spl
simple security sandbox-manifest
simple security audit-gates

CI should run:

simple verify security
simple verify architecture
simple test system --security-gates

Security tests:

spec "user feature cannot bypass admin gate":
    expect_compile_error SEC201:
        """
        class Bad:
            fn run():
                AdminUserRepo.delete(UserId(1))
        """

Given Simple already has SPipe, SDoctest, traceability, generated spec docs, and system-test mock policy gates, this should be implemented as another verification gate rather than only a runtime library.


---

## 16. Best Implementation Order

1. MDSOC metadata inference
   infer layer, feature, trust, security from folder and annotations.

2. Import/call graph builder
   start with imports and statically resolvable calls.
   later add dynamic call approximations.

3. Security policy parser
   source security block first.
   SDN override second.

4. Compile-time violations
   layer skip.
   feature crossing.
   raw privileged API usage.
   security logic outside security root.

5. Gate construct
   security gate.
   gate inventory.
   generated AOP advice.

6. Sandbox manifest
   generate only at first.
   then lower to Linux Landlock/seccomp.
   later WASI/Simple VM/Simple OS.

7. Capability typed APIs
   replace raw file/network/env/process APIs in sandboxed contexts.


---

## 17. Final Recommended Design

Use this model:

MDSOC dimensions describe where code belongs.
Security policy describes which dimension crossings are legal.
Security gates are the only legal crossing points.
AOP enforces and weaves the gates.
SDN config supplies environment/profile policy.
Sandbox manifests are generated from the same policy.
Capabilities replace ambient authority inside sandboxed code.

The minimal grammar worth adding:

security AppSecurity:
    root src/security
    default deny

    dimension layer:
        order ui -> api -> service -> domain -> port -> infra
        forbid skip_layer unless gate

    allow feature user -> feature admin through UserAdminGate
    deny feature user -> feature admin direct

security gate UserAdminGate:
    from feature user
    to feature admin
    policy CanRequestAdminAction
    audit all
    sandbox admin_sandbox

sandbox admin_sandbox:
    fs read ["/etc/simple/admin.conf"]
    fs write ["/var/lib/simple/audit"]
    net deny all

This gives Simple a security model stronger than ordinary layered architecture: it prevents layer skipping, feature boundary bypass, security logic scattering, and ambient authority leakage, while still fitting the existing Simple direction: MDSOC, SDN, compile-time AOP, runtime-family enforcement, and generated verification artifacts.

---

## 18. Implementation Checkpoint

Current compiler-front-end slice:

1. `security AppSecurity:` is parsed and lowered as first-class HIR with conventions enabled by default, so projects get folder/source-policy behavior without boilerplate config.
2. `security gate Name:` is parsed and lowered with `from`, `to`, `policy`, `audit`, `sandbox`, and `grant` metadata for later AOP weaving and gate verification.
3. `sandbox name:` is parsed and lowered as the common input for generated sandbox manifests.
4. A diagnostic inventory builder now renders the planned outputs:
   - `gate_inventory.md`
   - `access_matrix.generated.sdn`
   - `security_aspects.generated.spl`
   - `security_aop.generated.sdn`
   - `capability_manifest.sdn`
   - `sandbox_manifest.sdn`
   - `violations.sdn`
5. `simple security check` writes the security artifacts under `build/security/` or an explicit `--out` directory.
6. Default convention inference maps `src/feature/<feature>/<layer>/**` to feature/layer coordinates and treats `src/security/**` as a security root.
7. Initial `SEC201` detection reports direct feature-boundary references such as user-service code reaching admin code without a gate.
8. Initial `SEC301` detection reports authoritative authorization predicates outside security roots while allowing `@security_observation` for UI-only hints.
9. Initial `SEC401` detection reports raw ambient authority calls such as `File.open`, `Network.connect`, `Env.get`, and `Process.spawn`, pointing callers toward narrowed native object-capability handles.
10. Security policies and gates render an AOP-facing artifact: `GeneratedSecurityBoundary` for allow/forbid crossing rules and one generated around-advice aspect per gate for policy, audit, sandbox, and gate runtime entry/exit.
11. Security gates now also lower into real HIR AOP advices (`HirAopAdvice`) with `around` form and `execution(* Gate.*(..))` predicates, so the existing compile-time weaver can consume them without runtime reflection or global config.
12. Security deny/allow policy rules lower into HIR architecture rules (`HirArchRule`) where they can be consumed by the existing architecture-rule engine; the machine-readable lowering is emitted as `security_aop.generated.sdn`.
13. Generated gate advice now has a concrete compiler data contract (`SecurityAdvicePlan`) with ordered steps for `enter_gate`, `require_policy`, `enter_sandbox`, `audit_start`, `proceed`, `audit_success`, `audit_failure`, `exit_sandbox`, and `exit_gate`.
14. The compile-time weaver now accepts security advice plans through `WeavingConfig::from_hir_module` and materializes security around advice into ordered MIR runtime call targets such as `rt_security_enter_gate`, `rt_security_require_policy`, `rt_security_enter_sandbox`, audit calls, and cleanup calls.
15. The runtime exports fixed `rt_security_*` handlers for generated gate advice, including gate entry/exit, policy checks, sandbox entry/exit, audit start/success/failure, and testable counters. These are registered in the runtime symbol list as hosted security symbols without per-gate dynamic exports.
16. Gate, policy, sandbox, and audit names now lower to deterministic metadata IDs. The weaver emits those IDs as MIR `ConstInt` arguments to the fixed `rt_security_*` handlers, and the runtime records the last-seen IDs for verification and future policy/sandbox lookup.
17. The runtime now has explicit policy and sandbox registries keyed by those metadata IDs. Policy lookup defaults to allowed unless a policy is explicitly denied, preserving zero-config convention behavior while still letting generated/project config harden selected gates.
18. `SEC201` now builds a structured source import/call feature graph instead of emitting directly from line scanning. It applies declared `allow ... through` and `deny ... except` gate rules to diagnostics, reports whether the edge is an import or call, and allows cross-feature `port` imports while still rejecting direct privileged calls.
19. The weaver no longer emits `audit_failure` as part of the normal linear success path for generated security gate advice. Failure audit remains in the advice plan, but needs MIR error-edge routing before it is materialized.
20. `capability Name:` is parsed and lowered as a first-class native object-capability declaration. `simple security check` now writes `capability_manifest.sdn`, gate grants are validated against declared or built-in capability handles, and `SEC401` recommends the specific narrowed handle family for each raw ambient API.
21. The runtime can now load generated `security_aop.generated.sdn` text through `rt_security_load_registry_sdn`, registering policy IDs and sandbox IDs into the fixed `rt_security_*` registry without reflection or per-gate dynamic exports.
22. Hosted native builds now generate a `__module_init_security_registry` object when security declarations are present. The object embeds the generated security AOP registry text and uses the existing module-init caller to invoke `rt_security_load_registry_sdn` before `spl_main`, preserving zero-config startup behavior.
23. Static archive builds now include the generated security registry init object and `__simple_call_module_inits` caller when security declarations are present, so hosted archive consumers get the same zero-config registry startup path as direct native links.
24. `SEC201` can now consume lowered HIR modules when available, adding compiler-resolved import edges and resolved global call edges to the existing source fallback. This keeps default convention checks useful before full-project lowering while moving gate enforcement toward resolved compiler facts.
25. `SEC401` now also consumes lowered HIR modules when available, detecting resolved ambient authority calls such as `File.open` through HIR global/method call facts without relying only on source text scanning.
26. `SEC301` now also consumes lowered HIR modules when available, detecting resolved authorization predicates such as `current_user.is_admin`, `authorize`, and `check_permission` outside security roots without relying only on source text scanning.
27. Security diagnostics now carry inferred `trust` and `runtime` coordinates from default folder conventions, including `feature=plugin`, `trust=plugin`, and `runtime=sandboxed` for sandbox/plugin paths. This starts tying `SEC301` and `SEC401` findings to the MDSOC trust/runtime dimensions instead of only feature/layer names.
28. The HIR-resolved `SEC401` path now honors explicit narrowed capability handles on function parameters and locals. A resolved raw API call such as `File.open` is reported only when the function lacks a matching handle such as `ReadFile` or `WriteFile`, preserving the native object-capability model without requiring per-call config.
29. `SEC201` now prefers the compiler-resolved HIR import/call graph whenever a full lowered workspace is available. The source scanner remains as the zero-config fallback for partial or no HIR, but full-workspace checks no longer inherit source-level false positives from textual references.
30. `SEC301` and `SEC401` now also prefer resolved HIR facts whenever a full lowered workspace is available. Source scanning remains the zero-config fallback for partial/no HIR, but full-workspace authorization and ambient-authority diagnostics are driven by typed resolved calls and capability-handle facts.
31. The standard security enforcement library now exports first-class native object-capability handles for raw authority replacements: `ReadFile.read_text`, `WriteFile.write_text`, `NetworkEndpoint.connect`, `EnvVar.get`, and `ProcessSpawner.run`. `SEC401` diagnostics now point directly to those replacement methods instead of only naming the handle family.

Remaining implementation order:

1. Extend source fallback suppression once raw file/network/env/process calls lower to typed capability-handle APIs in partial-workspace checks.
2. Route real MIR failure edges to `audit_failure` and extend generated security registry startup loading beyond hosted executable/archive builds where needed.
