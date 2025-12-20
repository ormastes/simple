# Test Rules and Coverage Guidelines

## Overview

This document defines testing rules for layered/package-based architectures.
Each package or layer contains multiple classes with defined boundaries.

```
+------------------------------------------------------------------+
|                        SYSTEM BOUNDARY                           |
|  +------------------------------------------------------------+  |
|  |                    Package / Layer A                       |  |
|  |  +-------------+  +-------------+  +-------------+         |  |
|  |  | Class A1    |  | Class A2    |  | Class A3    |         |  |
|  |  | (Interface) |  | (Internal)  |  | (Internal)  |         |  |
|  |  +-------------+  +-------------+  +-------------+         |  |
|  +------------------------------------------------------------+  |
|  +------------------------------------------------------------+  |
|  |                    Package / Layer B                       |  |
|  |  +-------------+  +-------------+  +-------------+         |  |
|  |  | Class B1    |  | Class B2    |  | Class B3    |         |  |
|  |  | (Interface) |  | (Internal)  |  | (Ext Lib)   |         |  |
|  |  +-------------+  +-------------+  +-------------+         |  |
|  +------------------------------------------------------------+  |
+------------------------------------------------------------------+
         ^                                          ^
         |                                          |
    [GUI/API]                                 [External Libs]
```

---

## Test Types Hierarchy

```
+---------------------------------------------------------------------+
|  TEST PYRAMID                                                       |
|                                                                     |
|        /\            System Test (E2E)                              |
|       /  \           - Out of process                               |
|      /    \          - Covers all interfaces + external libs        |
|     /------\                                                        |
|    /        \        Service Test (SVC)                             |
|   /          \       - In process                                   |
|  /            \      - More corner cases than System                |
| /--------------\     - Covers interfaces + external lib touch       |
|/                \    Integration Test (INT)                         |
|                      - Package/class level                          |
|                      - Public interface + neighbor interaction      |
+---------------------------------------------------------------------+
```

---

## 1. System Test (E2E)

### Characteristics

| Property          | Value                                      |
|-------------------|--------------------------------------------|
| Process Model     | Out of Process                             |
| Scope             | Entire system boundary                     |
| Build Mode        | Library build can be in-process            |
| Element Unit      | Package / Layer                            |

### Coverage Requirements

System tests MUST touch:

1. **All Interface Classes** - GUI, API, CLI entry points
2. **All External Library Integrations** - DB, HTTP, File I/O, etc.
3. **All Enclosing Packages/Layers** - Every package in system

```
+---------------------------+
| SYSTEM TEST SCOPE         |
+---------------------------+
|                           |
|  [GUI] -----> [Package A] |
|                   |       |
|               [Package B] |
|                   |       |
|  [API] -----> [Package C] |
|                   |       |
|              [Ext Lib]    |
|                           |
+---------------------------+
   ^                    ^
   |                    |
 Interface           External
 Classes             Libraries
 (MUST TOUCH)        (MUST TOUCH)
```

### Quality Metrics

| Metric                      | Target  | Description                         |
|-----------------------------|---------|-------------------------------------|
| Interface Class Touch Cov   | 100%    | All interface classes executed      |
| External Lib Touch Cov      | 100%    | All external lib calls exercised    |
| Package/Layer Touch Cov     | 100%    | All packages have test paths        |

---

## 2. Service Test (SVC)

### Characteristics

| Property          | Value                                      |
|-------------------|--------------------------------------------|
| Process Model     | In Process                                 |
| Scope             | Service/Component boundary                 |
| Corner Cases      | More than System Test                      |
| Element Unit      | Package / Layer                            |

### Coverage Requirements

Service tests MUST:

1. Cover all interfaces within service boundary
2. Touch all external library integration points
3. Test MORE corner cases than system tests
4. Touch all enclosing packages/layers

```
+----------------------------------+
| SERVICE TEST SCOPE               |
+----------------------------------+
|                                  |
|  +----------------------------+  |
|  | Service Boundary           |  |
|  |                            |  |
|  |  [Interface] --> [Logic]   |  |
|  |       |            |       |  |
|  |       v            v       |  |
|  |  [Package A]  [Package B]  |  |
|  |       |            |       |  |
|  |       v            v       |  |
|  |     [Ext Lib Touch Points] |  |
|  +----------------------------+  |
|                                  |
|  Corner Cases:                   |
|  - Edge values                   |
|  - Error conditions              |
|  - Boundary conditions           |
|  - Concurrent scenarios          |
|                                  |
+----------------------------------+
```

### Quality Metrics

| Metric                      | Target  | Description                         |
|-----------------------------|---------|-------------------------------------|
| Interface Class Touch Cov   | 100%    | All service interfaces executed     |
| External Lib Touch Cov      | 100%    | All ext lib calls exercised         |
| Package/Layer Touch Cov     | 100%    | All packages have test paths        |
| Corner Case Coverage        | > Sys   | More paths than system test         |

---

## 3. Integration Test (INT)

### Characteristics

| Property          | Value                                      |
|-------------------|--------------------------------------------|
| Process Model     | In Process                                 |
| Scope             | Multi-package / Multi-layer                |
| Element Unit      | Class                                      |
| Focus             | Public interfaces + Neighbor interaction   |

### Coverage Requirements

Integration tests MUST:

1. Cover all PUBLIC interfaces of each package
2. Test neighbor package interactions
3. Touch all classes within scope (element = class)

```
+------------------------------------------------+
| INTEGRATION TEST SCOPE                         |
+------------------------------------------------+
|                                                |
|  +------------------+    +------------------+  |
|  | Package A        |    | Package B        |  |
|  |                  |    |                  |  |
|  | +-----+ +-----+  |    | +-----+ +-----+  |  |
|  | |Cls1 | |Cls2 |  |    | |Cls1 | |Cls2 |  |  |
|  | |pub  | |priv |  |    | |pub  | |priv |  |  |
|  | +--+--+ +-----+  |    | +--+--+ +-----+  |  |
|  |    |             |    |    ^             |  |
|  +----+-------------+    +----+-------------+  |
|       |                       |                |
|       +--------> Neighbor <---+                |
|                Interaction                     |
|                                                |
+------------------------------------------------+
     ^                              ^
     |                              |
  Public Interface              Class Touch
  Coverage                      Coverage
```

### Quality Metrics

| Metric                      | Target  | Description                         |
|-----------------------------|---------|-------------------------------------|
| Public Interface Cov        | 100%    | All public methods tested           |
| Class Touch Cov             | 100%    | All classes in scope touched        |
| Neighbor Interaction Cov    | 100%    | All package boundaries tested       |

---

## 4. Element Touch Rules Summary

```
+---------------------------------------------------------------+
| TEST TYPE    | ELEMENT UNIT      | TOUCH REQUIREMENT          |
+---------------------------------------------------------------+
| System       | Package / Layer   | All packages touched       |
| Service      | Package / Layer   | All packages touched       |
| Integration  | Class             | All classes touched        |
+---------------------------------------------------------------+
```

### Touch Coverage Formula

```
                    Number of Touched Elements
Touch Coverage = --------------------------------- x 100%
                    Total Number of Elements

Where Elements:
  - System/Service Test: Packages or Layers
  - Integration Test: Classes
```

---

## 5. Architecture Test

### Purpose

Architecture tests enforce structural rules to maintain system integrity.

### Rules

```
+---------------------------------------------------------------+
| RULE                                  | ENFORCEMENT            |
+---------------------------------------------------------------+
| No mocks in production implementation | Static analysis        |
| Proper layer connections only         | Dependency check       |
| Interface contracts respected         | Contract verification  |
| No circular dependencies              | Graph analysis         |
+---------------------------------------------------------------+
```

### Mock Prevention

```
+----------------------------------+
| PRODUCTION CODE                  |
+----------------------------------+
|                                  |
|  class RealService:              |
|      def __init__(self):         |
|          # NO MOCK INJECTION     |
|          # ALLOWED HERE          |
|          self.db = RealDB()      |
|                                  |
+----------------------------------+
              ^
              |
         ARCH TEST
         VALIDATES
              |
              v
+----------------------------------+
| TEST CODE ONLY                   |
+----------------------------------+
|                                  |
|  class TestService:              |
|      def setup(self):            |
|          # MOCKS ALLOWED         |
|          # ONLY IN TESTS         |
|          self.db = MockDB()      |
|                                  |
+----------------------------------+
```

### Proper Connection Validation

```
+------------------------------------------------+
|                                                |
|  Layer 1 (Presentation)                        |
|      |                                         |
|      v  (allowed)                              |
|  Layer 2 (Business)                            |
|      |                                         |
|      v  (allowed)                              |
|  Layer 3 (Data)                                |
|      ^                                         |
|      |                                         |
|  Layer 1 --X--> Layer 3  (FORBIDDEN: skip)     |
|                                                |
+------------------------------------------------+
```

---

## 6. Coverage Metrics Summary

### System / Service Test Quality Metrics

| Metric                   | Formula                                    |
|--------------------------|--------------------------------------------|
| Ext Lib Touch Cov        | (Touched Ext Libs / Total Ext Libs) x 100  |
| Interface Class Touch    | (Touched Interfaces / Total Interfaces)    |
| Element (Pkg) Touch Cov  | (Touched Packages / Total Packages) x 100  |

### Integration Test Quality Metrics

| Metric                   | Formula                                    |
|--------------------------|--------------------------------------------|
| Class Touch Cov          | (Touched Classes / Total Classes) x 100    |
| Public Interface Cov     | (Tested Methods / Total Public Methods)    |
| Neighbor Cov             | (Tested Interactions / Total Interactions) |

---

## 7. Test Execution Order

```
+------------------------------------------------------------------+
|                                                                  |
|  1. Architecture Tests (Fast, Static)                            |
|     |                                                            |
|     v                                                            |
|  2. Integration Tests (In-Process, Class Level)                  |
|     |                                                            |
|     v                                                            |
|  3. Service Tests (In-Process, Package Level, Corner Cases)      |
|     |                                                            |
|     v                                                            |
|  4. System Tests (Out-of-Process, Full E2E)                      |
|                                                                  |
+------------------------------------------------------------------+
```

---

## 8. Checklist

### Before Release

- [ ] All system tests pass
- [ ] All service tests pass  
- [ ] All integration tests pass
- [ ] All architecture tests pass
- [ ] Interface class touch coverage = 100%
- [ ] External lib touch coverage = 100%
- [ ] Package/layer touch coverage = 100% (sys/svc)
- [ ] Class touch coverage = 100% (integration)
- [ ] No mocks in production code
- [ ] All layer connections valid

---

## Appendix: Quick Reference

```
+===================================================================+
|                     TEST RULES QUICK REFERENCE                    |
+===================================================================+
| TYPE        | PROCESS     | ELEMENT  | MUST TOUCH                |
+-------------+-------------+----------+---------------------------+
| System      | Out-of-Proc | Package  | All Interfaces            |
|             |             |          | All Ext Libs              |
|             |             |          | All Packages              |
+-------------+-------------+----------+---------------------------+
| Service     | In-Process  | Package  | All Interfaces            |
|             |             |          | All Ext Libs              |
|             |             |          | All Packages              |
|             |             |          | + More Corner Cases       |
+-------------+-------------+----------+---------------------------+
| Integration | In-Process  | Class    | All Public Interfaces     |
|             |             |          | All Classes               |
|             |             |          | Neighbor Interactions     |
+-------------+-------------+----------+---------------------------+
| Arch        | Static      | -        | No Mock in Prod           |
|             |             |          | Valid Connections         |
+===================================================================+
```

