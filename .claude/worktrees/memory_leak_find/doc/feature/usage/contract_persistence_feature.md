# Create and save a contract
*Source:* `test/feature/usage/contract_persistence_feature_spec.spl`

## Overview

Enables saving consumer-driven contracts to JSON files for
    provider verification and Pact broker integration.

    Contracts are serialized to Pact-compatible JSON format and written
    to the filesystem using the file_io module.

## Feature: Feature #2401: Contract Persistence - File I/O

Enables saving consumer-driven contracts to JSON files for
    provider verification and Pact broker integration.

    Contracts are serialized to Pact-compatible JSON format and written
    to the filesystem using the file_io module.

### Scenario: Contract serialization

Tests contract JSON serialization to Pact-compatible format.

| # | Example | Status |
|---|---------|--------|
| 1 | converts contract to valid JSON | pass |
| 2 | includes all interaction details in JSON | pass |

**Example:** converts contract to valid JSON
    Given val contract = ct.Contract__new("web-app", "user-api")
    Given val request = ct.HttpRequest__new("GET", "/users/1")
    Given val response = ct.HttpResponse__new(200)
    Given val interaction = ct.Interaction__new("get user", request, response)
    Given val json = contract.to_pact_json()

**Example:** includes all interaction details in JSON
    Given val contract = ct.Contract__new("app", "api")
    Given val request = ct.HttpRequest__new("POST", "/data")
    Given val response = ct.HttpResponse__new(201)
    Given val interaction = ct.Interaction__new("create resource", request, response)
    Given val json = contract.to_pact_json()

### Scenario: Contract file persistence

Tests saving contracts to files.

| # | Example | Status |
|---|---------|--------|
| 1 | saves contract to file | pass |
| 2 | returns error when save fails | pass |

**Example:** saves contract to file
    Given val contract = ct.Contract__new("client", "provider")
    Given val request = ct.HttpRequest__new("GET", "/api/data")
    Given val response = ct.HttpResponse__new(200)
    Given val interaction = ct.Interaction__new("fetch data", request, response)
    Given val result = contract.save("/tmp/contract-test.json")

**Example:** returns error when save fails
    Given val contract = ct.Contract__new("client", "provider")
    Given val result = contract.save("/root/invalid/path/contract.json")

### Scenario: Pact broker integration

Tests contracts ready for Pact broker publishing.

| # | Example | Status |
|---|---------|--------|
| 1 | enables contracts for broker publishing | pass |

**Example:** enables contracts for broker publishing
    Given val contract = ct.ContractBuilder__new("consumer", "provider")
    Given val broker = ct.PactBroker__new("https://broker.example.com")
    Given val result = broker.publish(contract, "1.0.0")

### Scenario: Usage examples

- Uses file_io module for file system access
    - Contracts serialized to Pact-compatible JSON format
    - Errors returned as Result<(), text> for proper error handling
    - Mock implementation ready for broker integration

| # | Example | Status |
|---|---------|--------|
| 1 | demonstrates saving contracts | pass |


