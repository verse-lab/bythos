# Proof Explanation

Main efforts are put on organizing the proof. 

## What this proof does not depend on

- the concrete value of $t_0$
  - any $t_0 < N$ shall make sense
- the assumption that at least two honest nodes exist

## Invariant statement

Divided into three parts:
- coherence (`Coh`)
- node invariants (should hold on every *honest* node)
  - relate $(n, sig)$ in $cert = \langle v, nsigs\rangle$ with $\mathsf{SubmitMsg} \in P_{sent}$
  - relate $c \in certs$ with $\mathsf{ConfirmMsg} \in P_{sent}$
  - relate $conf$ with the size of $cert$
- $P_{sent}$ invariants (should hold on every sent messages)
  - relate $\mathsf{SubmitMsg} \in P_{sent}$ with the submitted value in $cert$
  - relate $\mathsf{ConfirmMsg} \in P_{sent}$ with $cert$ and $conf$, and *also the history*
    - using another argument with type $\mathsf{PacketSoup}$ to represent the history

## Proof of Inductivity

The proof is relatively straightforward, but some notions must be captured to avoid writing (too many) repeated proof scripts. 

Here, one of the notions can be called *monoticity*. The intuition is
- In this protocol (and possibly also in some other protocols), information increases monotonically. For example, the size of $P_{sent}$ will never decrease. And the set of received certificates on a node (from $\mathsf{ConfirmMsg}$s) will never be reduced (at least for the current design). 
- Some growing information only affects related components of the invariant. That is, after a system step, some information will change; and in order to re-establish the invariant, we only need to prove those components affected by the changed information. 

### Monoticity of $P_{sent}$

For $P_{sent}, P_{sent}'$, define
- $P_{sent} \approx P_{sent}'$ if
  - $P_{sent}' = P_{sent}$
  - $P_{sent}' = \mathsf{consume}(p, P_{sent})$, where $\mathsf{consume}(p, P_{sent})$ is the result of removing a undelivered packet $p$ from $P_{sent}$, marking $p$ as delivered (by modifying its `consumed` field) and putting $p$ back into $P_{sent}$. 
- $P_{sent} \lesssim P_{sent}'$ if $\exists P_{sent}'', P_{sent} \approx P_{sent}'', P_{sent}'' \subseteq P_{sent}'$

Check `psent_mnt` for formal definition. The `bool` indicates whether this is $\approx$ (`false`) or $\lesssim$ (`true`). 

### Monoticity of Node State

For node states $\delta, \delta'$, define $\delta \approx \delta'$ and $\delta \lesssim \delta'$ similarly as above. Here $\delta \approx \delta'$ is simpler: $\delta \approx \delta'$ iff $\delta = \delta'$. Check `state_mnt` for formal definition. 

### Some Main Results (Informally)

Use `0` to denote $\approx$ and `1` to denote $\lesssim$. 
- `inv_preserve_10`: if there is some node whose state is updated from $\delta$ to $\delta'$ and $\delta \lesssim \delta'$, but $P_{sent}$ keeps intact, then we can re-establish the global invariant as long as $\delta'$ satisfies the node invariant with regard to $P_{sent}$. 
- `inv_preserve_01`: if the state map keeps intact but $P_{sent}$ is updated to $P_{sent}'$ and $P_{sent} \lesssim P_{sent}'$, then we can re-establish the global invariant as long as the newly added packets in $P_{sent}'$ satisfies the $P_{sent}$ invariant *with $P_{sent}$ being the history*. 
- `inv_preserve_00`: if the state map keeps intact and $P_{sent}$ is updated to $P_{sent}'$ where $P_{sent} \approx P_{sent}'$, then we can re-establish the global invariant. 

### Proof Outline

Apply `inv_preserve_10`, `inv_preserve_01`, `inv_preserve_00` when needed. The only case which does not fall in them is that both a node's state and the packet soup are updated. In this case, applying `inv_preserve_01` and then `inv_preserve_10` suffices.  

## Proof of Soundness

Reduce the $2\times 2$ case-analysis (i.e., for the two senders of $\mathsf{ConfirmMsg}$s, discuss whether a sender is Byzantine or not) into a remark: 
- If the $\mathsf{ConfirmMsg}(\langle v, nsigs\rangle)$ is correct (i.e., satisfies the corresponding $P_{sent}$ invariant) and there is a valid signature $sig$ of a honest node $n$ such that $(n, sig) \in nsigs$, then the submitted value in $n$'s state is $v$. 

  Proof: exactly by discussing whether the sender of $\mathsf{ConfirmMsg}$ is Byzantine or not. In both cases we know that $n$ must have sent $\mathsf{SubmitMsg}(v, sig)$ in the history, and by using the $P_{sent}$ invariant for $\mathsf{SubmitMsg}$ we can conclude that the submitted value in $n$'s state is $v$. 

Then by using the remark two times, we know that this honest node $n$ has two different submitted values, which leads to a contradiction. 
