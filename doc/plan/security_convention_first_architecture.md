# Simple Language Security Architecture: Convention-First MDSOC + AOP Gates + Sandbox + Remote UI Policy

## 0. Executive Summary

Simple should treat security as an architecture-level compile-time concern, not as scattered runtime checks.

The best model is:

src/<layer>/<feature_group>/<feature_leaf>/...

Then Simple infers:

layer   = first folder under src
feature = remaining folder path

With only this minimal config:

security:
    layers ui -> api -> service -> domain -> infra

the compiler can enforce:

1. Same feature may flow downward through declared layers.
2. Layer skipping is blocked by default.
3. Cross-feature calls are blocked by default.
4. Feature crossing requires a security gate.
5. Authorization logic may live only in security roots.
6. UI permission checks are observations, not authorization.
7. Sandbox rules attach to feature/layer/folder/gate.
8. SecurityContext is typed and explicit in semantics.
9. Task-local/thread-local is only a runtime cache.
10. Remote clients receive permission snapshots, not authority.

This keeps the Ruby/Rails-like "convention over configuration" experience while still giving strong static enforcement. Rails explicitly promotes convention over configuration; Simple can apply the same idea to security and architecture, but with compiler checks instead of framework convention only.


---

## 1. Folder Model: Layers Are Top-Level Folders

Your corrected model is the right one:

src/
  ui/
  api/
  service/
  domain/
  infra/
  security/

Each layer repeats the same or similar feature tree.

Example:

src/
  ui/
    user/profile/page.spl
    admin/user/page.spl

  api/
    user/profile_api.spl
    admin/user_api.spl

  service/
    user/profile/profile_service.spl
    admin/user/admin_user_service.spl

  domain/
    user/profile/profile.spl
    admin/user/user_admin.spl

  infra/
    user/profile/user_repo_sql.spl
    admin/user/admin_user_repo_sql.spl

  security/
    gate/user_admin.spl
    gate/admin_user.spl
    policy/can_request_user_delete.spl
    sandbox/admin_sandbox.spl

Inferred coordinates:

src/service/user/profile/profile_service.spl
=> layer=service
=> feature=user.profile

src/domain/admin/user/user_admin.spl
=> layer=domain
=> feature=admin.user

src/infra/user/profile/user_repo_sql.spl
=> layer=infra
=> feature=user.profile

src/security/gate/user_admin.spl
=> layer=security
=> security_kind=gate
=> gate=user_admin

The user should not need to annotate this.


---

## 2. Minimal Security Grammar

### 2.1 Smallest Useful Form

security:
    layers ui -> api -> service -> domain -> infra

This should be enough for most projects.

It means:

Top-level folders are layers.
Path after the layer is the feature path.
Same feature can call downward.
Layer skipping is forbidden.
Cross-feature access requires a gate.
Security logic must be inside src/security.
Default policy is deny when uncertain.

### 2.2 Medium Project

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

Meaning:

user <-> admin   requires gate
user <-> billing requires gate
admin <-> billing requires gate

### 2.3 Larger Project

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

    allow user -> admin through UserAdmin
    allow admin -> user through AdminUser

Still very short.


---

## 3. Default Access Rules

With:

security:
    layers ui -> api -> service -> domain -> infra

Simple should derive these default rules.

### 3.1 Same Feature, Normal Layer Descent: Allowed

src/ui/user/profile
  -> src/api/user/profile
  -> src/service/user/profile
  -> src/domain/user/profile
  -> src/infra/user/profile

Allowed when each call follows the declared layer path.

### 3.2 Layer Skipping: Denied

Denied:

src/ui/user/profile -> src/domain/user/profile

because it skips api and service.

Diagnostic:

SEC101 layer skip denied:
  from: layer=ui      feature=user.profile
  to:   layer=domain  feature=user.profile

Expected path:
  ui -> api -> service -> domain

Fix:
  call the service/api layer
  or declare an explicit gate/port exception

### 3.3 Cross-Feature Access: Denied

Denied:

src/service/user/profile -> src/service/admin/user

because user.profile crosses into admin.user.

Diagnostic:

SEC201 cross-feature access denied:
  from: layer=service feature=user.profile
  to:   layer=service feature=admin.user

Use gate:
  src/security/gate/user_admin.spl

### 3.4 Domain to Infra: Port Only

Domain should not call concrete infra directly.

Allowed:

src/domain/user/profile/port/user_repo.spl
src/infra/user/profile/user_repo_sql.spl

Denied:

domain/user/profile -> infra/user/profile/UserRepoSql

unless through a declared port.


---

## 4. Feature Group and Feature Leaf

Feature path should be split as:

src/<layer>/<feature_group>/<feature_leaf>/...

Example:

src/service/admin/user/delete_user.spl

means:

layer         = service
feature_group = admin
feature_leaf  = user
feature_full  = admin.user

Recommended defaults:

same full feature:
    allowed by layer rule

same feature group, different leaf:
    allowed only through group API or __init__.spl export

different feature group:
    security gate required

Examples:

admin.user -> admin.role

same group, different leaf. Allow only through:

src/service/admin/__init__.spl
src/service/admin/api.spl

But:

user.profile -> admin.user

requires a security gate.


---

## 5. Security Gates

A gate is the only legal crossing point between protected features or security levels.

### 5.1 Convention-First Gate Naming

If this file exists:

src/security/gate/user_admin.spl

compiler infers:

from feature group: user
to feature group: admin
gate name: UserAdmin

So this minimal gate is enough:

# src/security/gate/user_admin.spl

gate UserAdmin:
    fn request_delete_user(actor: UserActor, target: UserId) -> DeleteRequest:
        require CanRequestUserDelete(actor, target)
        audit UserDeleteRequested(actor.id, target)
        return DeleteRequest(target)

No need to write:

from user
to admin

because the path already says it.

### 5.2 Explicit Gate Only When Needed

gate UserProfileToAdminUser:
    from user.profile
    to admin.user

    fn request_delete_user(actor: UserActor, target: UserId):
        require CanRequestUserDelete(actor, target)

Use explicit form only when convention is insufficient.


---

## 6. Gate Usage Example

Allowed:

# src/service/user/profile/profile_service.spl

class ProfileService:
    init(gate: UserAdmin):
        self.gate = gate

    fn request_delete_my_account(actor: UserActor):
        self.gate.request_delete_user(actor, actor.id)

Denied:

# src/service/user/profile/profile_service.spl

class ProfileService:
    fn bad(actor: UserActor):
        AdminUserService.delete(actor.id)

Compiler error:

SEC201 cross-feature access denied:
  from src/service/user/profile/profile_service.spl
       layer=service feature=user.profile
  to   src/service/admin/user/admin_user_service.spl
       layer=service feature=admin.user

Required gate:
  src/security/gate/user_admin.spl


---

## 7. AOP as Enforcement Backend

User-facing syntax should be security and gate, but implementation should lower to AOP.

Simple already has AOP-oriented design in the repo direction, so security can reuse the same infrastructure. The important difference is that security AOP is not optional advice. It is compiler-enforced mandatory mediation.

Source:

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin

Compiler lowers into an internal aspect like:

aspect GeneratedSecurityBoundary:
    forbid call:
        from feature user
        to feature admin
        unless through gate UserAdmin

    forbid call:
        from layer ui
        to layer domain
        unless through gate or port

Gate:

gate UserAdmin:
    fn request_delete_user(actor: UserActor, target: UserId):
        require CanRequestUserDelete(actor, target)
        audit UserDeleteRequested(actor.id, target)

Compiler lowers into:

aspect GeneratedUserAdminGateAdvice:
    around execution(UserAdmin.*):
        SecurityRuntime.enter_gate("UserAdmin")
        try:
            PolicyRuntime.require_all(this_gate.policies, args)
            Audit.log_start(this_gate, args)
            result = proceed()
            Audit.log_success(this_gate, result)
            return result
        except e:
            Audit.log_failure(this_gate, e)
            raise e
        finally:
            SecurityRuntime.exit_gate("UserAdmin")

Security AOP should default to compile-time weaving. Runtime interception is only for plugin/runtime dynamic cases.


---

## 8. Preventing Scattered Security Logic

Business code should not directly authorize privileged actions.

Forbidden outside src/security/**:

if current_user().is_admin:
    AdminUserRepo.delete(id)

Compiler diagnostic:

SEC301 scattered authorization:
  authorization predicate used outside security root:
    current_user().is_admin

Move this check to:
  src/security/policy/*.spl
or mark as UI-only observation:
  @security_observation

Allowed UI-only hint:

@security_observation
fn show_admin_button(user: UserActor) -> Bool:
    return user.ui_hints.contains("admin")

But this cannot guard server-side privileged execution.

This matches the OWASP direction: authorization logic must be robust, maintainable, and appropriate to business context; UI visibility cannot be treated as authorization.


---

## 9. Security Root

Default security root:

src/security/**

Only this root may define:

gate
policy
sandbox
capability grants
authorization decisions
audit classification
security diagnostic suppression

Recommended structure:

src/security/
  gate/
    user_admin.spl
    admin_user.spl

  policy/
    can_request_user_delete.spl
    can_view_admin_panel.spl

  audit/
    user_delete_audit.spl

  sandbox/
    admin_sandbox.spl
    plugin_sandbox.spl

  capability/
    file_caps.spl
    network_caps.spl


---

## 10. SecurityContext Model

### 10.1 Do Not Use Thread-Local as the Semantic Model

Thread-local is fast but insufficient for:

async tasks
fibers/coroutines
RPC
web requests
mobile clients
background jobs
distributed systems

Best model:

Semantic model:
    explicit typed SecurityContext

Default runtime:
    task-local SecurityContext

Optimization:
    thread-local cache only when runtime is sync/thread-bound

Remote:
    signed token + safe propagated headers + server-side reconstruction

UI:
    permission snapshot only

So Simple should treat this:

fn update_profile(input: ProfileUpdate):
    require can(UserProfileWrite(input.user_id))

as sugar for:

fn update_profile(ctx: SecurityContext, input: ProfileUpdate):
    require ctx.can(UserProfileWrite(input.user_id))

The source is short, but the IR is explicit.

### 10.2 Why This Matters

W3C Trace Context exists because request context must propagate across process/service boundaries using standardized headers, not thread-local memory.

So Simple should support context propagation directly instead of relying on implementation tricks.


---

## 11. Remote Client UI and Efficient Permission Sharing

For browser/app clients, do not send full server policy.

Use three layers.

### 11.1 Server-Side Authoritative Gate

Always enforce on server:

gate UserAdmin:
    fn request_delete_user(actor: UserActor, target: UserId):
        require CanRequestUserDelete(actor, target)

This is the source of truth.

### 11.2 Client-Side Permission Snapshot

Server sends compact UI hints:

{
  "sub": "user_123",
  "scope": ["user.profile.read", "user.profile.write"],
  "ui": {
    "profile.edit": true,
    "account.delete.request": true,
    "admin.panel.view": false
  },
  "policy_version": 42,
  "exp": 1770000000
}

Client uses this only for:

show/hide UI
enable/disable buttons
avoid useless network calls

Never for authorization.

### 11.3 Gate Call on Action

When user clicks:

client -> server gate endpoint
server reconstructs SecurityContext
server verifies policy
server executes or denies

This is efficient because the client receives only compact permission hints, not the whole policy engine.


---

## 12. Remote Context Grammar

Suggested Simple syntax:

remote context SecurityContext:
    header Authorization as token
    header traceparent as trace
    header baggage allow tenant_id, policy_version, request_class
    forbid baggage user_role, raw_permission, secret

Recommended split:

Authorization token:
    identity, session, coarse scopes, expiry

Permission snapshot:
    UI hints, feature flags, policy version

Trace context:
    traceparent, tracestate

Safe baggage:
    tenant_id, request_class, policy_version

Server context:
    full actor, roles, groups, tenant, session, policy engine state

W3C Trace Context standardizes request context propagation headers, and Baggage-style context is appropriate only for safe application metadata, not authorization authority.


---

## 13. UI Policy DSL

Put UI security hints in one place, not scattered components.

ui_policy UserProfileUi:
    show EditProfileButton when can(UserProfileWrite(self.user_id))
    show DeleteAccountButton when can(UserDeleteRequest(self.user_id))
    show AdminPanelLink when can(AdminPanelView)

Generated snapshot:

ui_policy:
    EditProfileButton: true
    DeleteAccountButton: true
    AdminPanelLink: false
    policy_version: 42

Client code:

if ui.can(EditProfileButton):
    show EditProfileButton

Server still checks the gate when action is invoked.


---

## 14. Sandbox Model

Sandbox should attach to:

whole app
library
layer
feature group
feature leaf
folder
gate
plugin
runtime component

Minimal syntax:

sandbox plugin:
    fs read "./plugins"
    fs write "./tmp/plugin"
    net deny

Attach by convention:

src/plugin/** -> sandbox plugin
src/infra/unsafe/** -> sandbox strict
src/admin/** -> sandbox admin

Or by config:

security:
    sandbox feature plugin with plugin
    sandbox feature admin with admin

SDN form:

sandbox:
    plugin:
        fs: read ./plugins, write ./tmp/plugin
        net: deny

    admin:
        fs: read ./config/admin.sdn, write ./audit
        net: deny

Linux Landlock is a good backend reference because it is designed to restrict ambient rights such as filesystem access and stack with existing access-control mechanisms.

For plugins, WASI is a strong reference because its design is capability-based: modules receive explicit capabilities for external resources rather than ambient access.


---

## 15. Capability-Based APIs

Sandboxed code should not use ambient global APIs:

File.open("/etc/passwd")
Network.connect("example.com")
Env.get("SECRET")
Process.spawn("sh")

Instead, use injected capabilities:

class ReportPlugin:
    init(fs: ReadDir["/reports"], out: WriteDir["/tmp/report"], log: AuditLog):
        self.fs = fs
        self.out = out
        self.log = log

Gate grants narrowed capabilities:

gate PluginHost:
    sandbox plugin

    grant:
        ReadDir["/reports"]
        WriteDir["/tmp/report"]
        AuditLog

    fn run_plugin(plugin: ReportPlugin):
        require CanRunPlugin(plugin.id)
        return plugin.run()

This prevents ambient authority leakage and confused-deputy-style mistakes.


---

## 16. Sandbox Lowering Pipeline

Simple should define an abstract sandbox manifest and lower it per backend.

source security block / security.sdn
        |
security graph
        |
gate graph + capability graph
        |
sandbox manifest
        |
backend lowering
        +-- Linux: Landlock + seccomp + namespaces
        +-- WASM/plugin: WASI-style capabilities
        +-- Baremetal: linker section + MPU/MMU regions
        +-- Simple VM: module capability table
        +-- Simple OS: native capability handles

Generated manifest:

sandbox_manifest:
    PluginSandbox:
        capabilities:
            - ReadDir("./plugins")
            - WriteDir("./tmp/plugin")
            - AuditLog
        deny:
            - Network
            - ProcessSpawn
            - RawDevice


---

## 17. DI Integration

DI and security should share one graph.

Earlier DI model:

inject AppGraph compile:
    root App
    bind UserRepo = SqlUserRepo
    slot PaymentProvider runtime

Security should extend it:

inject AppGraph compile:
    root App

    bind UserRepo = SqlUserRepo
    bind UserAdmin = UserAdminGate
    bind SecurityContext = RequestSecurityContext scoped

    slot PaymentProvider runtime sandbox payment_plugin

Gate injection:

class ProfileService:
    init(gate: UserAdmin):
        self.gate = gate

The DI compiler should know:

UserAdmin is a security gate.
SecurityContext is scoped/task-local.
PaymentProvider is runtime and sandboxed.

This allows lifetime/security checks together:

SEC-DI004:
  singleton AdminService depends on scoped SecurityContext

Fix:
  make AdminService scoped
  or inject Provider[SecurityContext]


---

## 18. Source + SDN Policy Merge

Source should define architecture defaults. SDN should define deployment/profile exceptions.

Source:

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

SDN:

security:
    profile: prod

    allow:
        - from: { feature: admin }
          to:   { feature: user }
          through: AdminUser

    sandbox:
        plugin:
            fs: read ./plugins, write ./tmp/plugin
            net: deny

Precedence:

1. compiler built-in safety invariants
2. source security block
3. profile-specific SDN additions
4. local dev/test override, if explicitly enabled

Important rule:

SDN can relax policy only if source marks the rule configurable.

Example:

security:
    isolate user, admin configurable
    deny user -> admin final

final cannot be weakened by config.


---

## 19. Policy Examples

### 19.1 Minimal App

security:
    layers ui -> service -> domain -> infra

### 19.2 Feature-Isolated App

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

### 19.3 Gate-Enabled App

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

    allow user -> admin through UserAdmin
    allow admin -> user through AdminUser

### 19.4 Sandbox-Enabled App

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin, billing

    sandbox feature plugin with plugin
    sandbox feature admin with admin

### 19.5 Strict System App

security:
    layers ui -> service -> domain -> infra -> driver
    isolate user, admin, driver, debug

    deny debug -> driver final
    sandbox feature plugin with plugin
    forbid ambient File, Network, Process


---

## 20. Generated Artifacts

Compiler should generate:

build/security/layer_map.sdn
build/security/feature_map.sdn
build/security/gate_map.sdn
build/security/access_matrix.sdn
build/security/sandbox_manifest.sdn
build/security/ui_policy.sdn
build/security/violations.sdn
build/security/report.md

Example access matrix:

                user      admin      billing    infra
user            allow     gate       gate       deny direct
admin           gate      allow      gate       deny direct
billing         gate      gate       allow      deny direct
plugin          deny      deny       deny       gate only

This is useful for architecture review, audits, and LLM-based code review.


---

## 21. CLI Tools

Recommended commands:

simple security check
simple security map
simple security matrix
simple security explain src/service/user/profile/profile_service.spl
simple security gates
simple security sandbox-manifest
simple security ui-policy
simple security audit

Example:

simple security explain src/service/user/profile/profile_service.spl

Output:

file: src/service/user/profile/profile_service.spl

layer:
  service

feature:
  user.profile

allowed same-feature calls:
  api/user/profile
  domain/user/profile

allowed gates:
  UserAdmin

forbidden:
  service/admin/**
  infra/** direct
  domain/** skip from ui


---

## 22. Diagnostics

### 22.1 Layer Skip

SEC101 layer skip denied:
  from: ui/user/profile
  to:   domain/user/profile

Expected:
  ui -> api -> service -> domain

### 22.2 Cross-Feature Access

SEC201 cross-feature access denied:
  from: service/user/profile
  to:   service/admin/user

Required gate:
  src/security/gate/user_admin.spl

### 22.3 Scattered Authorization

SEC301 scattered authorization:
  current_user().is_admin used outside src/security

Move to:
  src/security/policy/*.spl

### 22.4 Sandbox Violation

SEC401 sandbox violation:
  plugin code attempted Network.connect

Sandbox:
  plugin.net = deny

### 22.5 Context Misuse

SEC501 unsafe SecurityContext access:
  thread_local SecurityContext used inside async function

Use:
  task-local context
  explicit ctx parameter


---

## 23. Testing Model

Security rules should be testable as compile-time specs.

spec "user feature cannot call admin service directly":
    expect_compile_error SEC201:
        """
        class Bad:
            fn run():
                AdminUserService.delete(UserId(1))
        """

Gate test:

spec "user delete request goes through UserAdmin gate":
    given actor = UserActor(id=1)
    when result = UserAdmin.request_delete_user(actor, UserId(1))
    then audit contains UserDeleteRequested

System-test rule:

System tests may replace external/HAL gates.
System tests may not mock internal security policy.


---

## 24. Performance Model

Compile-time checks:

folder scan
import graph
call graph
feature/layer coordinate inference
gate inventory
sandbox manifest generation

Runtime checks:

gate entry/exit
policy evaluation
audit emission
capability lookup
sandbox transition, if needed

Optimization:

static gate calls are inlined when safe
constant policy parts are folded
permission snapshots are cached per policy_version
SecurityContext is task-local by default
thread-local cache only for sync runtimes

Remote UI efficiency:

do not send full policy
send compact UI snapshot
include policy_version
refresh only when version/session changes
server remains authoritative


---

## 25. Recommended Implementation Order

Phase 1: path-derived coordinates

Implement:

layer = first folder under src
feature = remaining folder path

Add:

security:
    layers ui -> api -> service -> domain -> infra

Generate layer_map.sdn and feature_map.sdn.

Phase 2: static architecture checks

Implement:

layer skip detection
cross-feature import detection
domain-to-infra direct dependency detection

Start with import graph before full call graph.

Phase 3: gates

Implement:

src/security/gate/*.spl
gate Name:
    fn ...

Infer from/to from filename.

Phase 4: scattered security prevention

Detect:

role checks
permission checks
raw auth APIs
security suppressions

outside src/security/**.

Phase 5: AOP lowering

Generate internal security aspects:

boundary forbid aspects
gate around aspects
audit aspects
policy aspects

Phase 6: SecurityContext

Add typed SecurityContext sugar:

require can(X)

desugars to context-aware IR.

Phase 7: sandbox manifest

Generate abstract manifest first.

Then lower to:

Linux Landlock/seccomp
WASI-style plugin capabilities
Simple VM capability table

Phase 8: remote UI policy

Add:

ui_policy:
    show Button when can(...)

Generate compact permission snapshot.


---

## 26. Final Recommended Design

The final Simple security model should be:

Convention-first:
    src/<layer>/<feature_group>/<feature_leaf>/...

Minimal config:
    security:
        layers ui -> api -> service -> domain -> infra

Compiler inference:
    layer from first folder
    feature from remaining path
    vertical feature slices across layers
    feature group from first feature segment
    gate direction from src/security/gate/<from>_<to>.spl

Default enforcement:
    no layer skipping
    no cross-feature access without gate
    no direct infra dependency except port
    no authorization logic outside security root
    no ambient authority inside sandboxed code

AOP:
    security DSL lowers to mandatory compile-time aspects
    gates get policy/audit/sandbox advice
    runtime AOP only for dynamic plugins

SecurityContext:
    explicit typed semantic model
    task-local default runtime
    thread-local only as optimization
    remote propagation via signed token + safe headers
    HMAC token validation before remote headers can authenticate a request
    UI receives permission snapshot only

Sandbox:
    attach to app/lib/layer/feature/folder/gate/plugin
    compile to sandbox manifest
    install lowered metadata in the hosted runtime security registry
    lower to Landlock/seccomp/namespaces on Linux
    lower to WASI/capability model for plugins
    lower to native object-capability handles in Simple OS
    enforce WASI env/preopen grants with explicit capability tables
    keep baremetal .simple.sandbox* and .simple.mpu* sections and fail closed when metadata is missing

DI:
    inject gates and SecurityContext like normal dependencies
    enforce lifetime + security rules together
    wire remote SecurityContext validation through replicated session and opaque key rollout adapters

Output:
    access matrix
    gate inventory
    sandbox manifest
    sandbox lowering
    UI policy snapshot
    audit/security report

Remaining implementation after generated lowering:
    add hardware-specific baremetal MPU/PMP register programming from generated metadata
    add concrete Redis/quorum session-store and vendor KMS/HSM clients behind the hosted adapter seams

The minimal example should look like this:

security:
    layers ui -> api -> service -> domain -> infra
    isolate user, admin

# src/security/gate/user_admin.spl

gate UserAdmin:
    fn request_delete_user(actor: UserActor, target: UserId):
        require CanRequestUserDelete(actor, target)
        audit UserDeleteRequested(actor.id, target)

# src/service/user/profile/profile_service.spl

class ProfileService:
    init(gate: UserAdmin):
        self.gate = gate

    fn request_delete_my_account(actor: UserActor):
        self.gate.request_delete_user(actor, actor.id)

That is the core: very little typing, strong compile-time architecture enforcement, centralized security gates, and runtime sandbox/context support only where needed.
