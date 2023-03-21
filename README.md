# ABC Protocol Verification

## Requirement

Coq 8.16.1

## Status

- only `Module Type`s, no implementations
- mostly vanilla Coq proof (for development speed); for SSReflect, only `ssreflect.SsrSyntax` and `ssrbool` are used

## Organization

- `Systems/Address.v`: about node addresses
- `Structures/Types.v`: about values, certificates, crypto primitives and accountability proof generators
- `Systems/Protocol.v`: about per-node states, messages and handlers
- `Systems/States.v`: about global states
- `Systems/Network.v`: network semantics
- `Properties/Invariant.v`: definitions and proof of properties (including invariants)
