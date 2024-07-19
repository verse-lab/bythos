# Bythos

Bythos is a framework embedded in the Coq proof assistant for users to implement, compose and verify Byzantine distributed protocols. By including a simple shim layer, Bythos also enables running the OCaml protocol implementation generated using the extraction mechanism of Coq. 

This is the document accompanying the research artefact for the paper *Compositional Verification of Composite Byzantine Protocols* to appear in the proceedings of the 31st ACM Conference on Computer and Communications Security (CCS 2024). 

## Getting Started

To get started, you will need to first compile the whole project, and then do a test run of the extracted OCaml implementation. Check [`INSTALL.md`](./INSTALL.md) for details. 

## Recommended Order of Artefact Evaluation

We recommend starting by reviewing the implementations of the case study protocols, and then checking their safety and liveness specifications. During this process, sometimes it may help to refer to the code belonging to the Bythos framework. For information on file organisation and the mapping between paper sections and code, please see the sections below. 

After reviewing the Coq formalisations, We recommend trying to run the extracted protocols and observing the nodes' behaviour in different scenarios. For details, please refer to the `Extraction/` directory and its `scripts/` subdirectory. 

## Organisation

For reference, we present the file organisation of the entire project, along with brief explanations of the contents of each directory and file. The directories are listed in dependency order (below depends on above). 
- `Utils/`: Utility files, including a small extension of CoqTLA and other non-specific lemmas, definitions and tactics
- `Structures/`: Formalisation of datatypes
  - `Address.v`: Axiomatisation of the address type, and some instantiations
  - `Types.v`: Axiomatisations of commonly used datatypes, and some instantiations (the former half being about cryptographic primitives, while the latter half being about messages, packets and others)
- `Systems/`: Formalisation of generic distributed systems with Byzantine fault model
  - `Protocol.v`: Axiomatisation of Byzantine distributed protocols
  - `States.v`: Definitions related to system state and packet soup
  - `Network.v`: Definition of system semantics and some generic lemmas about it
- `Properties/`: Useful tools for helping prove safety and liveness specifications for given protocols
- `Composition/`: Definitions of sequentially composed protocols that build on top of sub-protocols, and lemmas for deriving properties of the composed protocol from those of sub-protocols
- `Protocols/`: Formalized protocols and proofs about their specifications
- `Extraction/`: Toolset for extracting protocols defined in Coq, and running their extracted OCaml implementation

Each formalised protocol has a corresponding directory in `Protocols/`, which typically contains the following files: 
- `Types.v`: Definitions and instantiations of datatypes used by the protocol
- `Protocol.v`: Instantiation of the protocol
- `Network.v`: Instantiation of the `byzConstraint` for the protocol, and the system semantics instantiated by the protocol
- `Invariant.v`: Proofs of knowledge lemmas
- `Safety.v`: Proofs of safety specifications
- `Liveness.v`: Proofs of liveness specifications, in a form more primitive than the TLA-style ones
- `Liveness_tla.v`: Proofs of TLA-style liveness specifications

## Paper-Code Mapping

For reference, we indicate the source files along with the definitions in them related to each section of the paper. 
1. Introduction
2. Overview
   - 2.1 Provable Broadcast, Formally
     - Fig 1: [`Protocols/PB/Types.v`](Protocols/PB/Types.v) and [`Protocols/PB/Protocol.v`](Protocols/PB/Protocol.v)
     - 2.1.1 Specification of Cryptographic Primitives
       - [`Structures/Types.v`](Structures/Types.v): `ThresholdSignatureScheme`
     - 2.1.2 Protocol Definition
       - [`Protocols/PB/Protocol.v`](Protocols/PB/Protocol.v)
   - 2.2 Proving Safety Properties
     - 2.2.1 System Model
       - [`Systems/Network.v`](Systems/Network.v): `system_step`
     - 2.2.2 Modelling Byzantine Faults
       - [`Protocols/PB/Network.v`](Protocols/PB/Network.v)
       - Fig 2: `producible_CombinedSignatures` in [`Protocols/PB/Safety.v`](Protocols/PB/Safety.v)
     - 2.2.3 Safety Properties
     - 2.2.4 Knowledge Lemmas as Incremental Invariants
     - 2.2.5 Knowledge-Driven Proof of Safety
       - [`Protocols/PB/Invariant.v`](Protocols/PB/Invariant.v)
       - [`Protocols/PB/Safety.v`](Protocols/PB/Safety.v)
   - 2.3 Reasoning about Liveness
     - 2.3.1 Liveness Properties
     - 2.3.2 Fair Delivery
     - 2.3.3 Knowledge-Driven Proofs of Liveness
       - [`Protocols/PB/Liveness.v`](Protocols/PB/Liveness.v)
       - [`Protocols/PB/Liveness_tla.v`](Protocols/PB/Liveness_tla.v)
   - 2.4 Verifying Protocol Composition
     - Files in `Protocols/PB/Iterated/`
3. Bythos Under the Hood
   - 3.1 Instantiating a Byzantine System in Bythos
     - 3.1.1 Basic Data Types
       - [`Structures/Address.v`](Structures/Address.v)
       - [`Structures/Types.v`](Structures/Types.v): `MessageType`, `PacketType`, `SimplePacket`
     - 3.1.2 Byzantine Resilience Threshold
       - [`Systems/Protocol.v`](Systems/Protocol.v): `ByzThreshold`, `ClassicByzThreshold`
     - 3.1.3 Protocol and System State
       - [`Systems/Protocol.v`](Systems/Protocol.v): `Protocol`
       - [`Systems/States.v`](Systems/States.v): `NetState`
     - 3.1.4 Byzantine Nodes and Their Behaviour
       - [`Systems/Network.v`](Systems/Network.v): `ByzSetting`, `RestrictedByzSetting`, `Adversary`
     - 3.1.5 System Semantics
       - Fig 3: `system_step` in [`Systems/Network.v`](Systems/Network.v)
       - [`Systems/Network.v`](Systems/Network.v): `Network`
     - 3.1.6 Extracting an Executable Implementation
       - Files in `Extraction/`
   - 3.2 Specifying and Proving Liveness
     - Fig 4: `termination_in_tla` in [`Protocols/PB/Liveness_tla.v`](Protocols/PB/Liveness_tla.v)
     - [`Utils/TLAmore.v`](Utils/TLAmore.v)
     - [`Properties/Liveness_tla.v`](Properties/Liveness_tla.v)
   - 3.3 A Functor for Protocol Composition
     - Files in `Composition/`
4. More Case Studies
   - 4.1 Reliable Broadcast
     - Files in `Protocols/RB/`
     - 4.1.1 Knowledge-Driven Proofs of Safety
       - [`Protocols/RB/Invariant.v`](Protocols/RB/Invariant.v)
     - 4.1.2 Knowledge-Driven Proofs of Liveness
       - [`Protocols/RB/Liveness.v`](Protocols/RB/Liveness.v)
       - [`Protocols/RB/Liveness_tla.v`](Protocols/RB/Liveness_tla.v)
   - 4.2 Accountable Byzantine Confirmer
     - Files in `Protocols/ABC/` (excluding `Protocols/ABC/OldProofs/`)
     - 4.2.1 Uncovering Implicit Assumptions
       - [`Protocols/ABC/Protocol.v`](Protocols/ABC/Protocol.v): Check the use of `msg_buffer`
     - 4.2.2 Liveness Proof
       - [`Protocols/ABC/Liveness.v`](Protocols/ABC/Liveness.v)
       - [`Protocols/ABC/Liveness_tla.v`](Protocols/ABC/Liveness_tla.v)
   - 4.3 Accountable Reliable Broadcast
     - Files in `Protocols/RBABC/`
     - 4.3.1 Compositional Liveness Proof
       - [`Protocols/RBABC/Liveness_tla.v`](Protocols/RBABC/Liveness_tla.v)
5. Related Work
