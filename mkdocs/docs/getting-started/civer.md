---
description: >-
  This tutorial guide you through the use of the different options of CIVER. 
---

# The CIVER tool

`CIVER` is a verification tool that allows to verify some properties implemented in circom using the Z3 SMT-solver. 


CIVER is activated when compiling a circuit using the flag `--civer`.
We have implemented three use modes `--check_tags`, `--check_postconditions`, and `--check_safety`, to verify tag-specfication, pre-/post-specifications, and weak safety respectively.  Let us see how to use each of these modes in the next modes. 


## Tag Verification
As explained in [Tag Section](), the circom compiler does not check if any tag is satisfied, since it only makes some syntactic checks. The tag semantics must be given by the programmer according to the logic of tags used in the circuits. Now, we can give the semantics of a tag as follows:


```text  
...
```

Using these tag specifications, we can try to verify the next circuit called `circuit_tags.circom`:

```text
...
```

If we  execute the command `circom unsafe.circom --check_tags`, we obtain the next output:

## Pre-/Post-conditions Verification
We can add preconditions and postconditions to a template, claiming some properties using quantifier-free formulas over the signals of the circuit. 
The current instructions are `spec_precondition Exp` and `spec_postcondition Exp`, respectively. 
Then, CIVER tries to prove that if the preconditions are satisfied, then the postconditions are also satisfied. 

For instance, let us consider the next example:

Let us consider the next circuit, called `conditions.circom`:
```text
a
```
If we execute the command `circom conditions.circom --check_postconditions`, we obtain the next output:



When dealing with cryptographic structures, some properties are often assumed by the programmers. CIVER usually needs these properties to reason about the different properties of the circuit. In this case, we can use the instruction `spec_fact` to claim a fact that CIVER interprets as true. For instance, 
let us consider the next example:

```text
b
```

## Weak-Safety Verification
Using the `--check_safety` option, CIVER tries to prove that the circuit satisfy the weak-safety property. Intuitively, a circuit is called weak-safety when for any input of the circuit, the constraint system describing the circuit ensures that there is a unique possible assignment for the output signals for the given inputs. 

Let us consider the next circuit, called `safe_iszero.circom`:
```text  
template IsZero() {
    signal input in;
    signal output {binary} out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    in*out === 0;
}

```

If we execute the command `circom safe_iszero.circom --check_safety`, we obtain the next output:

```text
-> All components satisfy weak safety :)
  * Number of verified components (weak-safety): 1
  * Number of failed components (weak-safety): 0
  * Number of timeout components (weak-safety): 0
```

Let us imagine we forget adding the last constraint in the previous circuit (called `unsafe_iszero.circom`):
```text  
template IsZero() {
    signal input in;
    signal output {binary} out;

    signal inv;

    inv <-- in!=0 ? 1/in : 0;

    out <== -in*inv +1;
    //in*out === 0;
}
```

If we execute the command `circom unsafe_iszero.circom --check_safety`, we obtain the next output:

```text
-> CIVER could not verify weak safety of all components
Components that do not satisfy weak safety: 
    - IsZero(), 
  * Number of verified components (weak-safety): 0
  * Number of failed components (weak-safety): 1
  * Number of timeout components (weak-safety): 0
```

