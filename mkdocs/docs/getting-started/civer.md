---
description: >-
  This tutorial guide you through the use of the different options of CIVER. 
---

# The CIVER tool

`CIVER` is a verification tool that allows to verify some properties implemented in circom using the Z3 SMT-solver. 


CIVER is activated when compiling a circuit using the flag `--civer`.
We have implemented three use modes `--check_tags`, `--check_postconditions`, and `--check_safety`, to verify tag-specfication, pre-/post-specifications, and weak safety respectively.  Let us see how to use each of these modes in the next sections. 


## Tag Verification
As explained in [Tag Section](), the circom compiler does not check if any tag is satisfied, since it only makes some syntactic checks. The tag semantics must be given by the programmer according to the logic of tags used in their circuit. In circom, we can give the semantics of a tag as follows:

```text  
spec_tags {tag_name} signal_name{
        Exp(signal_name, signal_name.tag_name)
}
```

We can specify a boolean formula depending on the signal name and the tag value, in case the tag has a value.

For instance, we can specify that a signal is a binary with the next specification:

```text  
spec_tags {binary} in{
        0 <= in && in <= 1
}
```

This specification uses not only the signal but also the value of the tag maxbit:
```text
spec_tags {maxbit} in{
        0 <= in && in <= 2**in.maxbit-1
}
```

The specification of a tag can be more general than some bounds. For instance:

```text
spec_tags {is_zero} in{
        in == 0
}
```

All the tag specifications are collected in a circom file, usually named as `tags_specification.circom`,and this file must be included always after the parameter `--civer` when using the command `circom`.

Using these tag specifications, we can try to verify the next circuit called `circuit_tags.circom`:

```text
template AddMaxbitTag(n) {
    signal input in;
    signal output {maxbit} out;

    _ <== Num2Bits(n)(in);

    out.maxbit = n;
    out <== in;
}
```

If we execute the command `circom unsafe.circom --civer tags_specification.circom --check_tags`, we obtain the next output:

```text
-> All tags were verified :)
  * Number of verified components (tags): 2
  * Number of failed components (tags): 0
  * Number of timeout components (tags): 0
```

## Pre-/Post-conditions Verification
We can add preconditions and postconditions to a template, claiming some properties using quantifier-free formulas over the signals of the circuit. 
The current instructions are `spec_precondition Exp` and `spec_postcondition Exp`, respectively. 
Then, CIVER tries to prove that if the preconditions are satisfied, then the postconditions are also satisfied. 

For instance, let us consider the next example:

Let us consider the next circuit, called `conditions.circom`:

```text
template LessThan(n) {
    assert(n <= 252);
    signal input {maxbit} in[2];
    signal output {binary} out;

    assert(in.maxbit <= n);

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];

    spec_postcondition out == (in[0] < in[1]);
}
```
If we execute the command `circom conditions.circom --civer --check_postconditions`, we obtain the next output:

```text
-> All postconditions were verified :)
  * Number of verified components (postconditions): 1
  * Number of failed components (postconditions): 0
  * Number of timeout components (postconditions): 0
```

After the parameter `--civer`, we can optionally include the file `tags_specification` to use the tag semantics to help the SMT solver to prove the postconditions.

When dealing with cryptographic structures, some properties are often assumed by the programmers. CIVER usually needs these properties to reason about the different properties of the circuit. In this case, we can use the instruction `spec_fact` to claim a fact that CIVER interprets as true. 

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

If we execute the command `circom safe_iszero.circom --civer --check_safety`, we obtain the next output:

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

If we execute the command `circom unsafe_iszero.circom --civer --check_safety`, we obtain the next output:

```text
-> CIVER could not verify weak safety of all components
Components that do not satisfy weak safety: 
    - IsZero(), 
  * Number of verified components (weak-safety): 0
  * Number of failed components (weak-safety): 1
  * Number of timeout components (weak-safety): 0
```

CIVER lists all the components that has not been able to verify.

## Modularity
CIVER takes advantage of the hierarchical structure of circom circuits and attack the problem in a bottom-up modular way, reducing the number of constraints that need to be considered to verify the properties at each component of the circuit.
An advantage of the approach is that it gives extra information about the potential bugs of the circuit when the verification fails. For example, in case there is a bug in a subcomponent `C` but the rest of the circuit is safe, our approach is able to distinguish that the only erroneous behavior appears in `C`, instead of just flagging the complete circuit as buggy.

