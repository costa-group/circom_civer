---
description: >-
  This tutorial guide you through the use of the different options of CIVER. 
---

# The CIVER tool

`CIVER` is a verification tool that allows us to verify properties of circuits implemented using the circom programming language. The verification problem is first transformed to make it suitable for the state-of-the-art SMT solvers and then proved in a modular way. CIVER uses the Z3 SMT-solver as back-end. 


CIVER is activated when compiling a circuit using the flag `--civer`.
We have implemented three use modes `--check_tags`, `--check_postconditions`, and `--check_safety`, to verify tag-specfication, pre-/post-specifications, and weak safety respectively.  Let us see how to use each of these modes in the next sections. 


## Tag Verification
As explained in [Tag Section](), the circom compiler does not check whether the semantics associated to the tag is satisfied by the tagged signals, since it only makes syntactic checks. In order to formally verify that the signals meet such semantics, the programmer should provide a formal definition of the tag semantics. In the CIVER extension of circom, the semantics of a tag is defined as follows:

```text  
spec_tags {tag_name} signal_name{
        Exp(signal_name, signal_name.tag_name)
}
```

We can specify a quantifier-free boolean formula depending on the signal name and the tag value (in case the tag has a value).

For instance, we can specify that a signal has a tag ```binary``` (which has no value) as follows:

```text  
spec_tags {binary} in{
        0 <= in && in <= 1
}
```

Similarly, we can sècify the semantics of the tag ```maxbit``` (which has a value), as follows:
```text
spec_tags {maxbit} in{
        0 <= in && in <= 2**in.maxbit-1
}
```

Another example (not using bounds) is when defining the ```non_zero``` tag: 

```text
spec_tags {non_zero} in{
        in != 0
}
```

In order to avoid conflicts when using the official cicom compiler, all tag specifications can be collected in a single file, usually named `tags_specification.circom`. If so, this file is given after the parameter `--civer` when using the command `circom`. 


Let us see how to use it with an example. Suppose we have included the specification of the tag ```maxbit``` in the file `tags_specification.circom` and we want to verify the next circuit called `circuit_tags.circom`:

```text
template AddMaxbitTag(n) {
    signal input in;
    signal output {maxbit} out;

    _ <== Num2Bits(n)(in);

    out.maxbit = n;
    out <== in;
}
```
To do so, we run the following command:

```circom unsafe.circom --civer tags_specification.circom --check_tags``` 

and we obtain the next output:

```text
-> All tags were verified :)
  * Number of verified components (tags): 2
  * Number of failed components (tags): 0
  * Number of timeout components (tags): 0
```

## Pre-/Post-conditions Verification
We can add preconditions and postconditions to a template as a (partial) specification of its behavior using quantifier-free formulas over the signals of the circuit. The current instructions to provide preconditions and postconditions are `spec_precondition Exp` and `spec_postcondition Exp`, respectively. 
Then, CIVER tries to prove that the postconditions are satisfied by the circuit assuming the preconditions are satisfied. 

For instance, let us consider the next circuit, called `conditions.circom` (where we have provided a postcondition):

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
If we execute the command 

```circom conditions.circom --civer --check_postconditions```

we obtain the next output:

```text
-> All postconditions were verified :)
  * Number of verified components (postconditions): 1
  * Number of failed components (postconditions): 0
  * Number of timeout components (postconditions): 0
```

After the parameter `--civer`, we can optionally include the file `tags_specification` to use the tag semantics to help the SMT solver to prove the postconditions.

When dealing with cryptographic structures, some properties are often assumed by the programmers. CIVER usually needs these properties to reason about the different properties of the circuit. In this case, we can use the instruction `spec_fact Exp` to claim a fact that CIVER interprets as true. 

## Weak-Safety Verification
Using the `--check_safety` option, CIVER tries to prove that the circuit satisfy the weak-safety property. Intuitively, a circuit is called weak-safety if for all possible inputs there is at most one possible assignment for the output signals that satisfy the constraint system describing the circuit (note that this ensures that the constraints define a deterministic circuit). 

Let us consider the next circuit, called `iszero.circom`:
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

If we execute the command 

```circom iszero.circom --civer --check_safety``` 

we obtain the next output:

```text
-> All components satisfy weak safety :)
  * Number of verified components (weak-safety): 1
  * Number of failed components (weak-safety): 0
  * Number of timeout components (weak-safety): 0
```

Let us imagine we forget adding the last constraint in the previous circuit (and we call the file `unsafe_iszero.circom`):
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

Now, if we execute the command 

```circom unsafe_iszero.circom --civer --check_safety```

we obtain the next output:

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

