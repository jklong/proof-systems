# Kimchi

* This document specifies *kimchi*, a zero-knowledge proof system that's a variant of PLONK.
* This document does not specify how circuits are created or executed, but only how to convert a circuit and its execution into a proof.

## Overview

There are three main algorithms to kimchi:

* [Setup](#constraint-system-creation): takes a circuit and produces a prover index, and a verifier index.
* [Proof creation](#proof-creation): takes the prover index, and the execution trace of the circuit to produce a proof.
* [Proof verification](#proof-verification): takes the verifier index and a proof to verify.

As part of these algorithms, a number of tables are created (and then converted into polynomials) to create a proof.

**Gates**. A circuit is described by a series of gates, that we list in a table. 
The columns of the tables list the gates, while the rows are the length of the circuit. 
For each row, only a single gate can take a value $1$ while all other gates take the value $0$.

|  row  | Generic | Poseidon | CompleteAdd | VarBaseMul | EndoMul | EndoMulScalar | ChaCha0 | ChaCha1 | ChaCha2 | ChaChaFinal |
| :---: | :-----: | :------: | :---------: | :--------: | :-----: | :-----------: | :-----: | :-----: | :-----: | :---------: |
|   0   |    1    |    0     |      0      |     0      |    0    |       0       |    0    |    0    |    0    |      0      |
|   1   |    0    |    1     |      0      |     0      |    0    |       0       |    0    |    0    |    0    |      0      |

**Coefficients**. The coefficient table has 15 columns, and is used to tweak the gates. 
Currently, only the [Generic](#double-generic-gate) and the [Poseidon](#poseidon) gates use it (refer to their own sections to see how). 
All other gates set their values to $0$.

|  row  |   0   |   1   |   2   |   3   |   4   |   5   |   6   |   7   |   8   |   9   |  10   |  11   |  12   |  13   |  14   |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
|   0   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |

**Registers (or Witness)**. Registers are also defined at every row, and are split into two types: the *IO registers* from $0$ to $6$ usually contain input or output of the gates (note that a gate can output a value on the next row as well). 
I/O registers can be wired to each other (they'll be forced to have the same value), no matter what row they're on (for example, the register at `row:0, col:4` can be wired to the register at `row:80, col:6`). 
The rest of the registers, $7$ through $14$, are called *advice registers* as they can store values that useful only for the row's active gate. 
Think of them as intermediary or temporary values needed in the computation when the prover executes a circuit.

|  row  |   0   |   1   |   2   |   3   |   4   |   5   |   6   |   7   |   8   |   9   |  10   |  11   |  12   |  13   |  14   |
| :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: | :---: |
|   0   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |   /   |


**Wiring (or Permutation)**. For gates to take the outputs of other gates as inputs, we use a wiring table to wire registers together. 
It is defined at every row, but only for the first $7$ registers. 
Each cell specifies a `(row, column)` tuple that it should be wired to.  Cells that are not connected to another cell are wired to themselves.
Note that if three or more registered are wired together, they must form a cycle. 
For example, if register `(0, 4)` is wired to both registers `(80, 6)` and `(90, 0)` then you would have the following table:

|  row  |    0    |   1   |   2   |   3   |    4     |   5   |    6     |
| :---: | :-----: | :---: | :---: | :---: | :------: | :---: | :------: |
|   0   |   0,0   |  0,1  |  0,2  |  0,3  | **80,6** |  0,5  |   0,6    |
|  ...  |         |       |       |       |          |       |          |
|  80   |  80,0   | 80,1  | 80,2  | 80,3  |   80,4   | 80,5  | **90,0** |
|  ...  |         |       |       |       |          |       |          |
|  90   | **0,4** | 90,1  | 90,2  | 90,3  |   90,4   | 90,5  |   90,6   |

**Wiring (Permutation) trace**. You can think of the permutation trace as an extra register that is used to enforce the wiring specified in the wiring table. 
It is a single column that applies on all the rows as well, which the prover computes as part of a proof.

|  row  |  pt   |
| :---: | :---: |
|   0   |   /   |

**Lookup**: TODO

This specification does not document how to create a circuit, we assume that the following gates are created prior to calling the [setup]() function:

* gates
* coefficients
* wiring (permutation)
* TODO: lookup

To create a proof, the prover will execute the circuit and record an execution trace using the following tables:

* registers
* wiring (permutation) trace
* TODO: lookup

## Dependencies

### Polynomial Commitments

Refer to the [specification on polynomial commitments](./poly-commitment.md). 
We make use of the following functions from that specification:

- `PolyCom.non_hiding_commit(poly) -> PolyCom::NonHidingCommitment`
- `PolyCom.commit(poly) -> PolyCom::HidingCommitment`
- `PolyCom.evaluation_proof(poly, commitment, point) -> EvaluationProof`
- `PolyCom.verify(commitment, point, evaluation, evaluation_proof) -> bool`

### Poseidon hash function

Refer to the [specification on Poseidon](./poseidon.md). 
We make use of the following functions from that specification:

- `Poseidon.init(params) -> FqSponge`
- `Poseidon.update(field_elem)`
- `Poseidon.finalize() -> FieldElem`

specify the following functions on top:

- `Poseidon.produce_challenge()` (TODO: uses the endomorphism)
- `Poseidon.to_fr_sponge() -> state_of_fq_sponge_before_eval, FrSponge`

With the current parameters:

* S-Box alpha: `7`
* Width: `3`
* Rate: `2`
* Full rounds: `55`
* Round constants: [`fp_kimchi`](https://github.com/o1-labs/proof-systems/blob/0b01f7575cdfa45541fcfcd88d59f73b015af56b/oracle/src/pasta/fp_kimchi.rs#L55), [`fq_kimchi`](https://github.com/o1-labs/proof-systems/blob/0b01f7575cdfa45541fcfcd88d59f73b015af56b/oracle/src/pasta/fq_kimchi.rs#L54)
* MDS matrix: [`fp_kimchi`](https://github.com/o1-labs/proof-systems/blob/0b01f7575cdfa45541fcfcd88d59f73b015af56b/oracle/src/pasta/fp_kimchi.rs#L10), [`fq_kimchi`](https://github.com/o1-labs/proof-systems/blob/0b01f7575cdfa45541fcfcd88d59f73b015af56b/oracle/src/pasta/fq_kimchi.rs#L10)

### Pasta

Kimchi is made to work on cycles of curves, so the protocol switch between two fields Fq and Fr, where Fq represents the base field and Fr represents the scalar field.

See the [Pasta curves specification](./pasta.md).

## Constraints

TODO: use expr to define the index columns?

### Permutation



### Lookup



### Gates

#### Double Generic Gate

The double generic gate contains two generic gates.

A generic gate is simply the 2-fan in gate specified in the
vanilla PLONK protocol that allows us to do operations like:

* addition of two registers (into an output register)
* or multiplication of two registers
* equality of a register with a constant

More generally, the generic gate controls the coefficients $c_i$ in the equation:

$$c_0 \cdot l + c_1 \cdot r + c_2 \cdot o + c_3 \cdot (l \times r) + c_4$$

The layout of the gate is the following:

|  0 |  1 |  2 |  3 |  4 |  5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 |
|:--:|:--:|:--:|:--:|:--:|:--:|:-:|:-:|:-:|:-:|:--:|:--:|:--:|:--:|:--:|
| l1 | r1 | o1 | l2 | r2 | o2 |   |   |   |   |    |    |    |    |    |

where l1, r1, and o1 (resp. l2, r2, o2)
are the left, right, and output registers
of the first (resp. second) generic gate.

The selectors are stored in the coefficient table as:

|  0 |  1 |  2 |  3 |  4 |  5 | 6  |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| l1 | r1 | o1 | m1 | c1 | l2 | r2 | o2 | m2 | c2 |    |    |    |    |    |

with m1 (resp. m2) the mul selector for the first (resp. second) gate,
and c1 (resp. c2) the constant selector for the first (resp. second) gate.

The constraints:

* $w_0 \cdot c_0 + w_1 \cdot c_1 + w_2 \cdot c_2 + w_0 \cdot w_1 \cdot c_3 + c_4$
* $w_3 \cdot c_5 + w_4 \cdot c_6 + w_5 \cdot c_7 + w_3 w_4 c_8 + c_9$

where the $c_i$ are the [coefficients]().


#### Poseidon

The poseidon gate encodes 5 rounds of the poseidon permutation.
A state is represents by 3 field elements. For example,
the first state is represented by `(s0, s0, s0)`,
and the next state, after permutation, is represented by `(s1, s1, s1)`.

Below is how we store each state in the register table:

|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| s0 | s0 | s0 | s4 | s4 | s4 | s1 | s1 | s1 | s2 | s2 | s2 | s3 | s3 | s3 |
| s5 | s5 | s5 |    |    |    |    |    |    |    |    |    |    |    |    |

The last state is stored on the next row. This last state is either used:

* with another Poseidon gate on that next row, representing the next 5 rounds.
* or with a Zero gate, and a permutation to use the output elsewhere in the circuit.
* or with another gate expecting an input of 3 field elements in its first registers.

```admonish
As some of the poseidon hash variants might not use $5k$ rounds (for some $k$),
the result of the 4-th round is stored directly after the initial state.
This makes that state accessible to the permutation.
```

We define $M_{r, c}$ as the MDS matrix at row $r$ and column $c$.

We define the S-box operation as $w^S$ for $S$ the `SPONGE_BOX` constant.

We store the 15 round constants $r_i$ required for the 5 rounds (3 per round) in the coefficient table:

|  0 |  1 |  2 |  3 |  4 |  5 |  6 |  7 |  8 |  9 | 10 | 11 | 12 | 13 | 14 |
|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|:--:|
| r0 | r1 | r2 | r3 | r4 | r5 | r6 | r7 | r8 | r9 | r10 | r11 | r12 | r13 | r14 |

The initial state, stored in the first three registers, are not constrained.
The following 4 states (of 3 field elements), including 1 in the next row,
are constrained to represent the 5 rounds of permutation.
Each of the associated 15 registers is associated to a constraint, calculated as:

first round:
* $w_6 - [r_0 + (M_{0, 0} w_0^S + M_{0, 1} w_1^S + M_{0, 2} w_2^S)]$
* $w_7 - [r_1 + (M_{1, 0} w_0^S + M_{1, 1} w_1^S + M_{1, 2} w_2^S)]$
* $w_8 - [r_2 + (M_{2, 0} w_0^S + M_{2, 1} w_1^S + M_{2, 2} w_2^S)]$

second round:
* $w_9 - [r_3 + (M_{0, 0} w_6^S + M_{0, 1} w_7^S + M_{0, 2} w_8^S)]$
* $w_{10} - [r_4 + (M_{1, 0} w_6^S + M_{1, 1} w_7^S + M_{1, 2} w_8^S)]$
* $w_{11} - [r_5 + (M_{2, 0} w_6^S + M_{2, 1} w_7^S + M_{2, 2} w_8^S)]$

third round:
* $w_{12} - [r_6 + (M_{0, 0} w_9^S + M_{0, 1} w_{10}^S + M_{0, 2} w_{11}^S)]$
* $w_{13} - [r_7 + (M_{1, 0} w_9^S + M_{1, 1} w_{10}^S + M_{1, 2} w_{11}^S)]$
* $w_{14} - [r_8 + (M_{2, 0} w_9^S + M_{2, 1} w_{10}^S + M_{2, 2} w_{11}^S)]$

fourth round:
* $w_3 - [r_9 + (M_{0, 0} w_{12}^S + M_{0, 1} w_{13}^S + M_{0, 2} w_{14}^S)]$
* $w_4 - [r_{10} + (M_{1, 0} w_{12}^S + M_{1, 1} w_{13}^S + M_{1, 2} w_{14}^S)]$
* $w_5 - [r_{11} + (M_{2, 0} w_{12}^S + M_{2, 1} w_{13}^S + M_{2, 2} w_{14}^S)]$

fifth round:
* $w_{0, next} - [r_{12} + (M_{0, 0} w_3^S + M_{0, 1} w_4^S + M_{0, 2} w_5^S)]$
* $w_{1, next} - [r_{13} + (M_{1, 0} w_3^S + M_{1, 1} w_4^S + M_{1, 2} w_5^S)]$
* $w_{2, next} - [r_{14} + (M_{2, 0} w_3^S + M_{2, 1} w_4^S + M_{2, 2} w_5^S)]$

where $w_{i, next}$ is the polynomial $w_i(\omega x)$ which points to the next row.


#### Chacha 



#### Elliptic Curve Addition



#### Endo Scalar



#### Endo Scalar Multiplication



#### Scalar Multiplication 



## Constraint System Creation

1. +3 on gates.len() here to ensure that we have room for the zero-knowledge entries of the permutation polynomial
   see https://minaprotocol.com/blog/a-more-efficient-approach-to-zero-knowledge-for-plonk
2. pad the rows: add zero gates to reach the domain size


## Prover Index


### The prover Index

1. compute the linearization
2. set `max_quot_size` to the degree of the quotient polynomial,
   which is obtained by looking at the highest monomial in the sum
    $$\sum_{i=0}^{PERMUTS} (w_i(x) + \beta k_i x + \gamma)$$
   where the $w_i(x)$ are of degree the size of the domain.


## Verifier Index

The verifier index is essentially a number of pre-computations containing:

* the (non-hidding) commitments of all the required polynomials



## Proof Data Structure

Originally, kimchi is based on an interactive protocol that was transformed into a non-interactive one using the [Fiat-Shamir](https://o1-labs.github.io/mina-book/crypto/plonk/fiat_shamir.html) transform.
For this reason, it can be useful to visualize the high-level interactive protocol before the transformation:


```mermaid
sequenceDiagram
    participant Prover
    participant Verifier
    Prover->>Verifier: public & witness commitment
    Verifier->>Prover: beta & gamma
    Prover->>Verifier: permutation commitment
    Verifier->>Prover: alpha
    Prover->>Verifier: quotient commitment
    Verifier->>Prover: zeta
    Note over Verifier: change of verifier (change of sponge)
    Prover->>Verifier: negated public poly p(zeta) & p(zeta * omega)
    Prover->>Verifier: permutation poly z(zeta) & z(zeta * omega)
    Prover->>Verifier: the generic selector gen(zeta) & gen(zeta * omega)
    Prover->>Verifier: the poseidon selector pos(zeta) & pos(zeta * omega)
    Prover->>Verifier: the 15 registers w_i(zeta) & w_i(zeta * omega)
    Prover->>Verifier: the 6 sigmas s_i(zeta) & s_i(zeta * omega)
    Prover->>Verifier: ft(zeta * omega)
    Verifier->>Prover: u, v
    Note over Verifier: change of verifier (change of sponge)
    Prover->>Verifier: evaluation proof (involves more interaction)
```

The Fiat-Shamir transform simulates the verifier messages via a hash function that hashes the transcript of the protocol so far before outputing verifier messages.
You can find these operations under the [proof creation](#proof-creation) and [proof verification](#proof-verification) algorithms as absorption and squeezing of values with the sponge.

A proof consists of:

* a number of (hidden) polynomial commitments:
  * the 15 registers/witness columns
  * the permutation
  * the quotient
  * TODO: lookup
  * TODO: public commitment is not here, but is in the sequence diagram
* evaluations of these polynomials at two random points $\zeta$ and $\zeta \omega$
* evaluations at the two random points of these addotional polynomials:
  * the 6 s (sigma)
  * TODO: lookup
  * generic selector
  * poseidon selector
* evaluation at $\zeta \omega$ of ft
* optionally, the public input used (the public input could be implied by the surrounding context and not part of the proof itself)
* optionally, the previous challenges (in case we are in a recursive prover)

The following sections specify how a prover creates a proof, and how a verifier validates a number of proofs.

### Proof Creation

To create a proof, the prover expects:

* A prover index, containing a representation of the circuit (and optionaly pre-computed values to be used in the proof creation).
* The (filled) registers table, representing parts of the execution trace of the circuit.

The prover then follows the following steps to create the proof:

1. Ensure we have room in the witness for the zero-knowledge rows.
   We currently expect the witness not to be of the same length as the domain,
   but instead be of the length of the (smaller) circuit.
   If we cannot add `ZK_ROWS` rows to the columns of the witness before reaching
   the size of the domain, abort.
2. Pad the witness columns with Zero gates to make them the same length as the domain.
   Then, randomize the last `ZK_ROWS` of each columns.
3. Setup the Fq-Sponge.
4. Compute the negated public input polynomial as
   the polynomial that evaluates to $-p_i$ for the first `public_input_size` values of the domain,
   and $0$ for the rest.
5. Commit (non-hidding) to the negated public input polynomial. **TODO: seems unecessary**
6. Absorb the public polynomial with the Fq-Sponge. **TODO: seems unecessary**
7. Commit to the witness columns by creating `COLUMNS` hidding commitments.
   Note: since the witness is in evaluation form,
   we can use the `commit_evaluation` optimization.
8. Absorb the witness commitments with the Fq-Sponge.
9. Compute the witness polynomials by interpolating each `COLUMNS` of the witness.
   TODO: why not do this first, and the commit? Why commit from evaluation directly?
10. TODO: lookup
11. Sample $\beta$ with the Fq-Sponge.
12. Sample $\gamma$ with the Fq-Sponge.
13. TODO: lookup
14. Compute the permutation aggregation polynomial $z$.
15. Commit (hidding) to the permutation aggregation polynomial $z$.
16. Absorb the permutation aggregation polynomial $z$ with the Fq-Sponge.
17. Sample $\alpha'$ with the Fq-Sponge.
18. Derive $\alpha$ from $\alpha'$ using the endomorphism (TODO: details)
19. TODO: instantiate alpha?
20. TODO: this is just an optimization, ignore?
21. TODO: lookup
22. TODO: setup the env
23. Compute the quotient polynomial (the $t$ in $f = Z_H \cdot t$).
    The quotient polynomial is computed by adding all these polynomials together:
    - the combined constraints for all the gates
    - the combined constraints for the permutation
    - TODO: lookup
    - the negated public polynomial
    and by then dividing the resulting polynomial with the vanishing polynomial $Z_H$.
    TODO: specify the split of the permutation polynomial into perm and bnd?
24. commit (hiding) to the quotient polynomial $t$
    TODO: specify the dummies
25. Absorb the the commitment of the quotient polynomial with the Fq-Sponge.
26. Sample $\zeta'$ with the Fq-Sponge.
27. Derive $\zeta$ from $\zeta'$ using the endomorphism (TODO: specify)
28. TODO: lookup
29. Chunk evaluate the following polynomials at both $\zeta$ and $\zeta \omega$:
    * $s_i$
    * $w_i$
    * $z$
    * lookup (TODO)
    * generic selector
    * poseidon selector

    By "chunk evaluate" we mean that the evaluation of each polynomial can potentially be a vector of values.
    This is because the index's `max_poly_size` parameter dictates the maximum size of a polynomial in the protocol.
    If a polynomial $f$ exceeds this size, it must be split into several polynomials like so:
    $$f(x) = f_0(x) + x^n f_1(x) + x^{2n} f_2(x) + \cdots$$

    And the evaluation of such a polynomial is the following list for $x \in {\zeta, \zeta\omega}$:

    $$(f_0(x), f_1(x), f_2(x), \ldots)$$

     TODO: do we want to specify more on that? It seems unecessary except for the t polynomial (or if for some reason someone sets that to a low value)
30. Evaluate the same polynomials without chunking them
    (so that each polynomial should correspond to a single value this time).
31. Compute the ft polynomial.
    This is to implement [Maller's optimization](https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html).
    (See in particular the [section on evaluating L](https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html#the-evaluation-of-l).)
32. construct the blinding part of the ft polynomial commitment
    see https://o1-labs.github.io/mina-book/crypto/plonk/maller_15.html#evaluation-proof-and-blinding-factors
33. Evaluate the ft polynomial at $\zeta\omega$ only.
34. Setup the Fr-Sponge
35. Squeeze the Fq-sponge and absorb the result with the Fr-Sponge.
36. Evaluate the negated public polynomial (if present) at $\zeta$ and $\zeta\omega$.
37. Absorb all the polynomial evaluations in $\zeta$ and $\zeta\omega$:
    - the public polynomial
    - z
    - generic selector
    - poseidon selector
    - the 15 register/witness
    - the 6 sigmas evaluations
38. Absorb the unique evaluation of ft: $ft(\zeta\omega)$.
39. Sample $v'$ with the Fr-Sponge
40. Derive $v$ from $v'$ using the endomorphism (TODO: specify)
41. Sample $u'$ with the Fr-Sponge
42. Derive $u$ from $u'$ using the endomorphism (TODO: specify)
43. Create a list of all polynomials that will require evaluations
    (and evaluation proofs) in the protocol.
    First, include the previous challenges, in case we are in a recursive prover.
44. Then, include:
    - the negated public polynomial (TODO: why?)
    - the ft polynomial
    - the permutation aggregation polynomial z polynomial
    - the generic selector
    - the poseidon selector
    - the 15 registers/witness columns
    - the 6 s
44. Create an aggregated evaluation proof for all of these polynomials at $\zeta$ and $\zeta\omega$ using $u$ and $v$.


### Proof Verification



## Optimizations

* `commit_evaluation`: TODO

## Security Considerations

TODO
