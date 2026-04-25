# Max-Flow Min-Cut: a comprehensive proof process

This note gives a complete proof-process view of the Lean development in
[`combinatoric_optimization/max_flow_min_cut/`](./).

The goal is not just to state the final theorem, but to list the actual statements used along the way, in natural English and with formulas.

The development is organized into six layers:

1. path simplification
2. basic flow and cut bookkeeping
3. cut decomposition and weak duality
4. residual graph and reachable cut
5. augmentation along a residual path
6. terminal-flow existence and the max-flow / min-cut theorem

---

## 0. Objects and notation

The basic data are defined in
[`Network.lean`](./MaxFlowMinCut/Network.lean).

### Network

A network consists of:

- a finite vertex set `V`
- a source `s`
- a sink `t`
- a capacity function `c : V × V → ℕ`

with:

$$ s \neq t $$
$$ \forall v,\ c(v,s)=0 $$
$$ \forall v,\ c(t,v)=0 $$

So no edge can carry capacity into the source, and no edge can carry capacity out of the sink.

### Flow

A flow is a function

$$ f : V \times V \to \mathbb N $$

satisfying:

1. capacity constraint:
$$ f(u,v) \le c(u,v) $$

2. conservation at every interior vertex $x \ne s,t$:
$$ \sum_u f(u,x) = \sum_w f(x,w) $$

### Derived quantities

For a flow $f$:

$$ \mathrm{outflow}_f(v)=\sum_w f(v,w) $$
$$ \mathrm{inflow}_f(v)=\sum_u f(u,v) $$
$$ \mathrm{value}(f)=\mathrm{outflow}_f(s) $$

For a cut $S \subseteq V$ with $s \in S$ and $t \notin S$:

$$ \mathrm{cutCapacity}(S)=\sum_{u\in S,\ v\notin S} c(u,v) $$
$$ \mathrm{outAcross}_f(S)=\sum_{u\in S,\ v\notin S} f(u,v) $$
$$ \mathrm{inAcross}_f(S)=\sum_{u\in S,\ v\notin S} f(v,u) $$

The two bookkeeping expressions used throughout are:

$$ \mathrm{netOn}_f(S)=\sum_{v\in S}\mathrm{outflow}_f(v)-\sum_{v\in S}\mathrm{inflow}_f(v) $$
$$ \mathrm{cutFlow}_f(S)=\mathrm{outAcross}_f(S)-\mathrm{inAcross}_f(S) $$

---

## 1. Path simplification

These statements are in
[`QuiverPath.lean`](./MaxFlowMinCut/QuiverPath.lean).

They are generic path lemmas, not specific to flows.

### `length_cast`

Changing the path endpoint by equality does not change its length.

$$ \mathrm{length}(h \triangleright p)=\mathrm{length}(p) $$

### `end_eq`

The endpoint recorded by a path is the target vertex.

$$ p.end=b $$

### `shorten_of_not_nodup`

If a path repeats a vertex, then one can remove the cycle and obtain a strictly shorter path with the same endpoints.

$$ \neg \mathrm{Nodup}(p.vertices) \;\Rightarrow\; \exists q,\ q:a\to b,\ \mathrm{length}(q)<\mathrm{length}(p) $$

This is the formal statement behind the familiar idea:

> if a path goes around a loop, you can cut the loop out.

### `exists_nodup_vertices`

Every path can be replaced by a simple path with no repeated vertices.

$$ \forall p:a\to b,\ \exists q:a\to b,\ \mathrm{Nodup}(q.vertices) $$

This matters later because augmentation is easiest to verify on simple residual paths.

---

## 2. Basic flow bookkeeping

These statements are in
[`Network.lean`](./MaxFlowMinCut/Network.lean).

### `val_to_source_eq_zero`

No flow enters the source.

$$ f(u,s)=0 $$

This follows from the capacity axiom $c(u,s)=0$.

### `val_from_sink_eq_zero`

No flow leaves the sink.

$$ f(t,v)=0 $$

This follows from $c(t,v)=0$.

### `inflow_source_eq_zero`

The source has zero inflow.

$$ \mathrm{inflow}_f(s)=0 $$

### `netOn_empty`

The empty set has zero net flow.

$$ \mathrm{netOn}_f(\varnothing)=0 $$

### `netOn_insert`

Adding a vertex to a set changes net flow by that vertex’s local imbalance.

$$ \mathrm{netOn}_f(S\cup\{x\}) = \mathrm{netOn}_f(S) + \mathrm{outflow}_f(x) - \mathrm{inflow}_f(x) $$

### `netOn_eq_zero_of_conserved_subset`

If every vertex in $S$ is an interior vertex, then the total net flow on $S$ is zero.

$$ (\forall v\in S,\ v\neq s \land v\neq t) \Rightarrow \mathrm{netOn}_f(S)=0 $$

This is just conservation summed over a set.

### `netOn_eq_value_of_isCut`

If $S$ is a source-side cut, then the net flow on $S$ equals the flow value.

$$ s\in S,\ t\notin S \Rightarrow \mathrm{netOn}_f(S)=\mathrm{value}(f) $$

This is the first key cut identity.

---

## 3. Cut decomposition and weak duality

These statements are in
[`CutFlow.lean`](./MaxFlowMinCut/CutFlow.lean).

This file turns local flow bookkeeping into the standard inequality
$$ \mathrm{value}(f)\le \mathrm{cutCapacity}(S). $$

### `outAcross_eq_filter_aux`

For fixed $u$, summing only over vertices outside $S$ is the same as summing over all vertices with an indicator.

$$ \sum_v \mathbf 1_{v\notin S}\, f(u,v) = \sum_{v\notin S} f(u,v) $$

### `inAcross_eq_filter_aux`

The same for incoming terms.

$$ \sum_v \mathbf 1_{v\notin S}\, f(v,u) = \sum_{v\notin S} f(v,u) $$

### `outflow_split`

Outflow from $u$ splits into inside-target and outside-target parts.

$$ \mathrm{outflow}_f(u) = \sum_{v\in S} f(u,v) + \sum_{v\notin S} f(u,v) $$

### `inflow_split`

Inflow into $u$ splits into inside-source and outside-source parts.

$$ \mathrm{inflow}_f(u) = \sum_{v\in S} f(v,u) + \sum_{v\notin S} f(v,u) $$

### `outAcross_eq_filter`

The total out-across quantity can be rewritten as

$$ \mathrm{outAcross}_f(S) = \sum_{u\in S}\sum_{v\notin S} f(u,v) $$

### `inAcross_eq_filter`

Likewise,

$$ \mathrm{inAcross}_f(S) = \sum_{u\in S}\sum_{v\notin S} f(v,u) $$

### `outflow_sum_eq`

Total outflow from $S$ splits into internal flow plus flow leaving $S$.

$$ \sum_{u\in S}\mathrm{outflow}_f(u) = \sum_{u\in S}\sum_{v\in S} f(u,v) + \mathrm{outAcross}_f(S) $$

### `inflow_sum_eq`

Total inflow into $S$ splits into internal flow plus flow entering $S$.

$$ \sum_{u\in S}\mathrm{inflow}_f(u) = \sum_{u\in S}\sum_{v\in S} f(v,u) + \mathrm{inAcross}_f(S) $$

### `internal_sum_comm`

The internal double sum is the same whether read as outgoing or incoming.

$$ \sum_{u\in S}\sum_{v\in S} f(v,u) = \sum_{u\in S}\sum_{v\in S} f(u,v) $$

This is the exact algebraic reason the internal flow cancels.

### `netOn_eq_cutFlow`

Net flow on a set equals net boundary flow across the cut of that set.

$$ \mathrm{netOn}_f(S)=\mathrm{cutFlow}_f(S) $$

In expanded form:

$$ \sum_{v\in S}\mathrm{outflow}_f(v) - \sum_{v\in S}\mathrm{inflow}_f(v) = \mathrm{outAcross}_f(S)-\mathrm{inAcross}_f(S) $$

### `outAcross_le_cutCapacity`

The flow leaving a cut is at most the capacity of the cut.

$$ \mathrm{outAcross}_f(S)\le \mathrm{cutCapacity}(S) $$

This is just the edgewise inequality $f(u,v)\le c(u,v)$, summed over all cut edges.

### `value_le_cutCapacity`

This is weak duality: every flow is bounded by every cut.

$$ S\text{ is a cut} \Rightarrow \mathrm{value}(f)\le \mathrm{cutCapacity}(S) $$

The proof is:

1. $\mathrm{value}(f)=\mathrm{netOn}_f(S)$
2. $\mathrm{netOn}_f(S)=\mathrm{cutFlow}_f(S)$
3. $\mathrm{cutFlow}_f(S)=\mathrm{outAcross}_f(S)-\mathrm{inAcross}_f(S)\le \mathrm{outAcross}_f(S)$
4. $\mathrm{outAcross}_f(S)\le \mathrm{cutCapacity}(S)$

So

$$ \mathrm{value}(f)\le \mathrm{cutCapacity}(S). $$

---

## 4. Residual graph and the reachable cut

These statements are in
[`Residual.lean`](./MaxFlowMinCut/Residual.lean).

For a flow $f$, a residual edge $u\to v$ exists in either of two ways:

- forward:
$$ f(u,v)<c(u,v) $$
- backward:
$$ 0<f(v,u) $$

This is the usual residual graph.

### `mem_reachable_iff`

Define `reachable(f)` to be the set of vertices reachable from $s$ in the residual graph.

$$ v\in \mathrm{reachable}(f) \iff \exists \text{ residual path } s\leadsto v $$

### `source_mem_reachable`

The source is always reachable from itself.

$$ s\in \mathrm{reachable}(f) $$

### `mem_reachable_of_mem_reachable_of_edge`

Reachability is closed under following residual edges.

$$ u\in \mathrm{reachable}(f),\ u\to v\text{ residual} \Rightarrow v\in \mathrm{reachable}(f) $$

### `no_edge_of_mem_reachable_of_not_mem_reachable`

There is no residual edge from a reachable vertex to an unreachable one.

$$ u\in R,\ v\notin R \Rightarrow \text{no residual edge }u\to v $$

where $R=\mathrm{reachable}(f)$.

This is simply because such an edge would make $v$ reachable.

### `val_eq_cap_of_mem_reachable_of_not_mem_reachable`

If $u\in R$ and $v\notin R$, then the forward edge $u\to v$ is saturated.

$$ u\in R,\ v\notin R \Rightarrow f(u,v)=c(u,v) $$

Reason: if $f(u,v)<c(u,v)$, there would be a forward residual edge $u\to v$, impossible.

### `val_rev_eq_zero_of_mem_reachable_of_not_mem_reachable`

If $u\in R$ and $v\notin R$, then there is no backward residual edge across the frontier, so the reverse flow must be zero.

$$ u\in R,\ v\notin R \Rightarrow f(v,u)=0 $$

Reason: if $0<f(v,u)$, there would be a backward residual edge $u\to v$, impossible.

### `reachable_isCut`

If there is no residual path from $s$ to $t$, then the reachable set is a cut.

$$ \neg(\exists \text{ residual path } s\leadsto t) \Rightarrow s\in R,\ t\notin R $$

### `outAcross_reachable_eq_cutCapacity`

Across the reachable cut, every outward edge is saturated, so flow out equals cut capacity.

$$ \mathrm{outAcross}_f(R)=\mathrm{cutCapacity}(R) $$

### `inAcross_reachable_eq_zero`

Across the reachable cut, there is no incoming reverse flow.

$$ \mathrm{inAcross}_f(R)=0 $$

### `value_eq_cutCapacity_reachable`

If there is no residual path from $s$ to $t$, then the value of the flow equals the capacity of the reachable cut.

$$ \neg(\exists \text{ residual path } s\leadsto t) \Rightarrow \mathrm{value}(f)=\mathrm{cutCapacity}(R) $$

This is the standard textbook certificate:

1. $R$ is a cut
2. $\mathrm{value}(f)=\mathrm{cutFlow}_f(R)$
3. $\mathrm{cutFlow}_f(R)=\mathrm{outAcross}_f(R)-\mathrm{inAcross}_f(R)$
4. $\mathrm{outAcross}_f(R)=\mathrm{cutCapacity}(R)$
5. $\mathrm{inAcross}_f(R)=0$

So

$$ \mathrm{value}(f)=\mathrm{cutCapacity}(R). $$

### `isMaxFlow_of_noResidualPath`

If there is no residual $s\to t$ path, then $f$ is a maximum flow.

$$ \neg(s\leadsto t \text{ residual}) \Rightarrow f \text{ is max flow} $$

Proof: for any other flow $g$,

$$ \mathrm{value}(g)\le \mathrm{cutCapacity}(R)=\mathrm{value}(f) $$

by weak duality plus the previous equality.

### `isMinCut_reachable_of_noResidualPath`

If there is no residual $s\to t$ path, then the reachable set is a minimum cut.

$$ \neg(s\leadsto t \text{ residual}) \Rightarrow R \text{ is a min cut} $$

Proof: for any cut $T$,

$$ \mathrm{cutCapacity}(R)=\mathrm{value}(f)\le \mathrm{cutCapacity}(T) $$

again by weak duality.

### `isMaxFlow_and_isMinCut_of_noResidualPath`

Combine the previous two:

$$ \neg(s\leadsto t \text{ residual}) \Rightarrow f \text{ is max flow and } R \text{ is min cut} $$

---

## 5. Augmentation along a residual path

These statements are in
[`Augment.lean`](./MaxFlowMinCut/Augment.lean).

This is the algorithmic half:

> if a residual $s\to t$ path exists, we can improve the flow.

To formalize this, the code builds a new value function by updating entries along the path one by one.

### Auxiliary bookkeeping: `augOut`, `augIn`, `augBal`

For any matrix-like function $g$:

$$ \mathrm{augOut}(g,x)=\sum_y g(x,y) $$
$$ \mathrm{augIn}(g,x)=\sum_y g(y,x) $$
$$ \mathrm{augBal}(g,x)=\mathrm{augOut}(g,x)-\mathrm{augIn}(g,x) $$

This is the balance of vertex $x$ under $g$.

### `addEntry`

Add one unit to a single edge $(a,b)$:

$$ (\mathrm{addEntry}(g,a,b))(x,y)= \begin{cases} g(x,y)+1 & (x,y)=(a,b)\\ g(x,y) & \text{otherwise} \end{cases} $$

### `subEntry`

Subtract one unit from a single edge $(a,b)$:

$$ (\mathrm{subEntry}(g,a,b))(x,y)= \begin{cases} g(x,y)-1 & (x,y)=(a,b)\\ g(x,y) & \text{otherwise} \end{cases} $$

### `augOut_addEntry`

Adding one unit at $(a,b)$ changes only the outgoing sum of $a$.

$$ \mathrm{augOut}(\mathrm{addEntry}(g,a,b),x) = \mathrm{augOut}(g,x)+\mathbf 1_{x=a} $$

### `augIn_addEntry`

Adding one unit at $(a,b)$ changes only the incoming sum of $b$.

$$ \mathrm{augIn}(\mathrm{addEntry}(g,a,b),x) = \mathrm{augIn}(g,x)+\mathbf 1_{x=b} $$

### `augBal_addEntry`

The balance change under a forward augmentation step is:

$$ \mathrm{augBal}(\mathrm{addEntry}(g,a,b),x) = \mathrm{augBal}(g,x)+\mathbf 1_{x=a}-\mathbf 1_{x=b} $$

### `sum_subEntry_row`

If $g(a,b)>0$, subtracting one unit from $(a,b)$ decreases the row sum of $a$ by exactly one.

$$ g(a,b)>0 \Rightarrow \sum_y (\mathrm{subEntry}(g,a,b))(a,y) = \sum_y g(a,y)-1 $$

### `sum_subEntry_col`

If $g(a,b)>0$, subtracting one unit from $(a,b)$ decreases the column sum of $b$ by exactly one.

$$ g(a,b)>0 \Rightarrow \sum_y (\mathrm{subEntry}(g,a,b))(y,b) = \sum_y g(y,b)-1 $$

### `augOut_subEntry`

$$ \mathrm{augOut}(\mathrm{subEntry}(g,a,b),x) = \mathrm{augOut}(g,x)-\mathbf 1_{x=a} $$

### `augIn_subEntry`

$$ \mathrm{augIn}(\mathrm{subEntry}(g,a,b),x) = \mathrm{augIn}(g,x)-\mathbf 1_{x=b} $$

### `augBal_subEntry_of_ne`

For $a\neq b$, a backward augmentation step changes balance by

$$ \mathrm{augBal}(\mathrm{subEntry}(g,a,b),x) = \mathrm{augBal}(g,x)-\mathbf 1_{x=a}+\mathbf 1_{x=b} $$

### `augmentVal`

Given a residual path $p:u\leadsto v$, define the new value function recursively:

- on a forward residual edge, add $1$ to the corresponding flow entry
- on a backward residual edge, subtract $1$ from the reversed flow entry

This is the formal implementation of “send one unit along the residual path”.

### `augmentVal_eq_of_or_not_mem_vertices`

If one endpoint of an edge is not on the path, augmentation leaves that edge unchanged.

$$ x\notin p.vertices \ \text{or}\ y\notin p.vertices \Rightarrow \mathrm{augmentVal}(p)(x,y)=f(x,y) $$

### `augmentVal_le_cap_of_nodup`

If the path is simple, the augmented value function still respects capacities.

$$ \mathrm{Nodup}(p.vertices) \Rightarrow \forall a,b,\ \mathrm{augmentVal}(p)(a,b)\le c(a,b) $$

This is where simplicity matters: repeated vertices would make local accounting harder.

### `augBal_augmentVal_of_nodup`

If $p:u\leadsto v$ is a simple residual path, then augmentation changes balances only at the endpoints.

$$ \mathrm{augBal}(\mathrm{augmentVal}(p),x) = \mathrm{augBal}(f,x)+\mathbf 1_{x=u}-\mathbf 1_{x=v} $$

So interior vertices stay balanced.

### `exists_simple_residualPath`

Any residual path can be replaced by a simple one.

$$ p:u\leadsto v \Rightarrow \exists q:u\leadsto v,\ \mathrm{Nodup}(q.vertices) $$

This imports the generic path-shortening lemmas into the residual-graph context.

### `augBal_eq_zero_of_conserve`

Every interior vertex of a genuine flow has zero balance.

$$ x\neq s,t \Rightarrow \mathrm{augBal}(f,x)=0 $$

### `augBal_source_eq_value`

The source balance equals the flow value.

$$ \mathrm{augBal}(f,s)=\mathrm{value}(f) $$

This uses the fact that source inflow is zero.

### `exists_augmentedFlow_of_simple_residualPath`

If there is a simple residual path from $s$ to $t$, then there exists a new legal flow $g$ whose value is larger by exactly $1$.

$$ p:s\leadsto t,\ \mathrm{Nodup}(p.vertices) \Rightarrow \exists g,\ \mathrm{value}(g)=\mathrm{value}(f)+1 $$

This is the main augmentation theorem.

The proof is:

1. define $g.val=\mathrm{augmentVal}(p)$
2. use `augmentVal_le_cap_of_nodup` for the capacity bound
3. use `augBal_augmentVal_of_nodup` and `augBal_eq_zero_of_conserve` to prove conservation at interior vertices
4. use `augBal_source_eq_value` to compute the new source value

### `exists_better_flow_of_residualPath`

If there is any residual path from $s$ to $t$, then there is a strictly better flow.

$$ p:s\leadsto t \Rightarrow \exists g,\ \mathrm{value}(f)<\mathrm{value}(g) $$

Proof:

1. simplify $p$ to a simple path $q$
2. augment along $q$
3. get value $+1$

---

## 6. Terminal flows and the main theorem

These statements are in
[`MainTheorem.lean`](./MaxFlowMinCut/MainTheorem.lean).

This file combines the augmentation theorem with the residual optimality theorem.

### `source_singleton_isCut`

The singleton $\{s\}$ is a valid cut.

$$ s\in \{s\},\quad t\notin \{s\} $$

This is used to get an initial cut-capacity bound.

### `zeroFlow`

The zero flow is a legal flow:

$$ f(u,v)=0 $$

It obviously satisfies capacity and conservation.

### `exists_terminalFlow_from`

Starting from any flow $f$, there exists a flow $g$ with value at least as large as $f$ and with no residual path from $s$ to $t$.

$$ \exists g,\ \mathrm{value}(f)\le \mathrm{value}(g) \ \land\ \neg(\exists \text{ residual path } s\leadsto t \text{ for } g) $$

This is the algorithmic termination theorem.

The proof uses strong induction on the gap

$$ C-\mathrm{value}(f) $$

where

$$ C=\mathrm{cutCapacity}(\{s\}) $$

is a fixed upper bound on every flow value, by weak duality.

If a residual path exists, `exists_better_flow_of_residualPath` gives a strictly better flow $g$, so

$$ C-\mathrm{value}(g) < C-\mathrm{value}(f). $$

Then the induction hypothesis applies.

If no residual path exists, we are already terminal.

### `exists_terminalFlow`

Starting from the zero flow, there exists a terminal flow.

$$ \exists f,\ \neg(\exists \text{ residual path } s\leadsto t \text{ for } f) $$

This is just `exists_terminalFlow_from zeroFlow`.

### `exists_isMaxFlow_and_isMinCut`

There exists a maximum flow and a minimum cut.

$$ \exists f,\exists S,\ f\text{ is max flow}\ \land\ S\text{ is min cut} $$

Proof:

1. take a terminal flow $f$
2. let $S=\mathrm{reachable}(f)$
3. apply `isMaxFlow_and_isMinCut_of_noResidualPath`

### `exists_isMaxFlow_and_isMinCut_and_value_eq_cutCapacity`

There exists a maximum flow $f$ and a minimum cut $S$ with equal value and capacity.

$$ \exists f,\exists S,\ f\text{ max flow} \land S\text{ min cut} \land \mathrm{value}(f)=\mathrm{cutCapacity}(S) $$

This is the cleanest existential statement of max-flow/min-cut.

### `exists_maxFlow_value_eq_minCut_capacity`

There exists a number $n$ which is simultaneously:

- the value of some maximum flow
- the capacity of some minimum cut

$$ \exists n,\ (\exists f,\ f\text{ max flow} \land \mathrm{value}(f)=n) \land (\exists S,\ S\text{ min cut} \land \mathrm{cutCapacity}(S)=n) $$

This is the final numeric equality form.

---

## 7. The whole proof in one chain

The whole formal proof can be summarized as follows.

### Step 1. Every flow is bounded by every cut

Using:

- `netOn_eq_value_of_isCut`
- `netOn_eq_cutFlow`
- `outAcross_le_cutCapacity`

we get

$$ \mathrm{value}(f)\le \mathrm{cutCapacity}(S) $$

for every flow $f$ and every cut $S$.

This is weak duality.

### Step 2. If a residual path exists, then the flow is not optimal

Using:

- `exists_simple_residualPath`
- `exists_augmentedFlow_of_simple_residualPath`
- `exists_better_flow_of_residualPath`

we get:

$$ \exists \text{ residual path } s\leadsto t \Rightarrow \exists g,\ \mathrm{value}(g)>\mathrm{value}(f) $$

So a flow with a residual $s\to t$ path cannot be maximum.

### Step 3. If no residual path exists, then the reachable set is an optimal cut certificate

Let

$$ R=\mathrm{reachable}(f). $$

Using:

- `reachable_isCut`
- `val_eq_cap_of_mem_reachable_of_not_mem_reachable`
- `val_rev_eq_zero_of_mem_reachable_of_not_mem_reachable`
- `outAcross_reachable_eq_cutCapacity`
- `inAcross_reachable_eq_zero`
- `value_eq_cutCapacity_reachable`

we get

$$ \neg(s\leadsto t \text{ residual}) \Rightarrow \mathrm{value}(f)=\mathrm{cutCapacity}(R). $$

Then weak duality forces:

$$ \mathrm{value}(g)\le \mathrm{cutCapacity}(R)=\mathrm{value}(f) $$

for every flow $g$, so $f$ is maximum; and

$$ \mathrm{cutCapacity}(R)=\mathrm{value}(f)\le \mathrm{cutCapacity}(T) $$

for every cut $T$, so $R$ is minimum.

### Step 4. Repeated augmentation reaches a terminal flow

Using:

- `source_singleton_isCut`
- `value_le_cutCapacity`
- `exists_better_flow_of_residualPath`
- `exists_terminalFlow_from`

we prove by strong induction that repeated augmentation must eventually stop.

The measure is

$$ \mathrm{cutCapacity}(\{s\})-\mathrm{value}(f), $$

which decreases whenever a residual path exists.

### Step 5. A terminal flow is simultaneously max flow and min cut

Using:

- `exists_terminalFlow`
- `isMaxFlow_and_isMinCut_of_noResidualPath`

we conclude:

$$ \exists f,\exists S,\ f\text{ max flow},\ S\text{ min cut},\ \mathrm{value}(f)=\mathrm{cutCapacity}(S). $$

That is exactly the max-flow / min-cut theorem.

---

## 8. What the algorithm really proves

The proof process is not just:

> augment until stuck, then take reachable vertices.

In Lean it becomes the following theorem chain:

1. simplify paths to simple paths
2. define augmentation edge-by-edge
3. prove augmentation preserves legality of flow
4. prove augmentation increases value by $1$
5. prove the weak-duality inequality
6. define the residual reachable set
7. prove terminal reachable-set edges are saturated in one direction and zero in the other
8. conclude value equals reachable cut capacity
9. derive max-flow and min-cut optimality
10. use induction on a bounded gap to prove termination

So the final theorem sits on top of four different kinds of ingredients:

- path shortening
- local augmentation bookkeeping
- cut algebra
- residual reachability

That is the full proving process formalized in the repo.
