# Networking Specification
*Source:* `test/feature/usage/networking_spec.spl`
**Feature IDs:** #NET-001 to #NET-010  |  **Category:** Runtime | Networking  |  **Status:** Implemented

## Overview



Tests networking functionality including:
- TCP socket binding and connection
- UDP socket operations
- Socket options (broadcast, TTL)
- Error handling for invalid handles
- JIT compilation mode networking

## Network Handle Types

- TCP Listener - Server socket accepting connections
- TCP Stream - Connected client socket
- UDP Socket - Datagram socket for send/recv

## Syntax

```simple
@net
fn create_server() -> Result<i64, str>:
    val (handle, err) = native_tcp_bind("127.0.0.1:8080")
    if err != 0:
        Err("bind failed")
    else:
        Ok(handle)
```

## Feature: TCP Operations

## TCP Socket Binding and Connection

    Tests TCP socket creation and management.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tcp bind returns valid handle | pass |
| 2 | tcp close succeeds for valid handle | pass |
| 3 | tcp connect to local server | pass |
| 4 | tcp accept waits for connection | pass |

**Example:** tcp bind returns valid handle
    Given val handle = 1  # Simulated valid handle
    Given val err = 0
    Then  expect test_tcp_bind()

**Example:** tcp close succeeds for valid handle
    Given val close_err = 0
    Then  expect test_tcp_close()

**Example:** tcp connect to local server
    Given val handle = 1
    Given val err = 0
    Then  expect test_tcp_connect()

**Example:** tcp accept waits for connection
    Then  expect test_tcp_accept()

## Feature: UDP Operations

## UDP Socket Operations

    Tests UDP socket creation, options, and data transfer.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | udp bind returns valid handle | pass |
| 2 | udp send_to transmits data | pass |
| 3 | udp loopback communication | pass |

**Example:** udp bind returns valid handle
    Given val handle = 1
    Given val err = 0
    Then  expect test_udp_bind()

**Example:** udp send_to transmits data
    Given val sent = 2
    Given val err = 0
    Then  expect test_udp_send()

**Example:** udp loopback communication
    Then  expect test_udp_loopback()

## Feature: Socket Options

## UDP Socket Configuration

    Tests socket option manipulation.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | udp broadcast option | pass |
| 2 | udp ttl option | pass |

**Example:** udp broadcast option
    Given val set_err = 0
    Then  expect test_broadcast()

**Example:** udp ttl option
    Given val set_err = 0
    Then  expect test_ttl()

## Feature: Network Error Handling

## Invalid Handle and Connection Errors

    Tests error handling for network operations.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | invalid handle returns error | pass |

**Example:** invalid handle returns error
    Given val err = 1  # Non-zero error
    Then  expect test_invalid_handle()

## Feature: JIT Compilation Mode

## Native Code Networking

    Tests that networking works in JIT/compiler mode.

### Scenario: General

| # | Example | Status |
|---|---------|--------|
| 1 | tcp bind compiles in JIT mode | pass |
| 2 | udp bind compiles in JIT mode | pass |

**Example:** tcp bind compiles in JIT mode
    Then  expect test_tcp_jit()

**Example:** udp bind compiles in JIT mode
    Then  expect test_udp_jit()


