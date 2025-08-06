# The CIVER tool
CIVER is a tool that can verify **weak safety**, also known as determinism, which means there is a single valid output for any given inputs. When this property is not satisfied it means that the circuit is underconstrained, as all non expected values that are valid for the outpus should be restricted. CIVER can verify weak safety of circuits defined using the DSL circom, but will soon also be able to verify circuits provided as constraint systems (R1CS, PLONK, ACIR). 

CIVER modularly analyses the circuit to increase scalability and to find the problematic part of the circuit.
+ When the circuit is provided in the circom language, it uses the structure of the circuit definition to modularly check all the components. CIVER can also check Pre/Postconditions defined on circom programs, as well as verify circom's tag specifications. CIVER has been integrated in the circom compiler and can handle full circom programs.
+ When CIVER is applied to non-circom circuits powerful clustering techniques are applied in order to break the circuit in smaller components that are then handled modularly.

CIVER currently uses the Z3 SMT solver as its back-end, but support for selecting other solvers such as cvc5 and additional SMT engines will be available soon.

Besides verifying weak safety, CIVER can also formally check tag specifications and pre/postconditions of circom circuits. If the programmer provides the semantics of the tags, CIVER can automatically prove that all tagged signals satisfy their intended meaning. Similarly, it can verify that the postconditions of a component hold whenever its preconditions are met. These additional verification modes allow developers to formally validate semantic annotations of their circuits.

We have implemented three use modes `--check_safety`, `--check_tags`, and `--check_postconditions`, to verify weak-safety, tag-specfication, and pre-/post-specifications, respectively.  Let us see how to use each of these modes in the next sections. 

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

component main = IsZero();
```

If we execute the command 

```civer_circom iszero.circom --check_safety``` 

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

```civer_circom unsafe_iszero.circom --check_safety```

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

## Tag Verification
As explained in the [Tags section](https://docs.circom.io/circom-language/tags/) of the official documentation, the circom compiler does not check whether the semantics associated to the tag is satisfied by the tagged signals, since it only makes syntactic checks. In order to formally verify that the signals meet such semantics, the programmer should provide a formal definition of the tag semantics. In the CIVER extension of circom, the semantics of a tag is defined as follows:

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

In order to avoid conflicts when using the official circom compiler, all tag specifications can be collected in a single file, usually named `tags_specification.circom`. If so, this file is given after the parameter `--civer` when using the command `civer_circom`. 


Let us see how to use it with an example. Suppose we have included the specification of the tag ```maxbit``` in the file `tags_specification.circom` and we want to verify the next circuit called `circuit_tags.circom`:

```text
include "bitify.circom";

template AddMaxbitTag(n) {
    signal input in;
    signal output {maxbit} out;

    _ <== Num2Bits(n)(in);

    out.maxbit = n;
    out <== in;
}

component main = AddMaxbitTag(4);
```
To do so, we run the following command:

```civer_circom circuit_tags.circom --civer tags_specification.circom --check_tags``` 

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

Optionally,  we can include the parameter `--civer` with the file `tags_specification.circom` to use the tag semantics to help the SMT solver to prove the postconditions and the weak-safety property.

For instance, let us consider the next circuit, called `conditions.circom` (where we have provided a postcondition):

```text
include "bitify.circom";

template MyLessThan(n) {
    assert(n <= 252);
    signal input {maxbit} in[2];
    signal output {binary} out;

    assert(in.maxbit <= n);

    component n2b = Num2Bits(n+1);

    n2b.in <== in[0]+ (1<<n) - in[1];

    out <== 1-n2b.out[n];

    spec_postcondition out == (in[0] < in[1]);
}

template Main(n){
   signal input in1, in2;
   signal {maxbit} in[2];
   in.maxbit = n;
   in <== [in1, in2];
   signal output {binary} out <== MyLessThan(n)(in);
}

component main = Main(16);


```
If we execute the command 

```civer_circom conditions.circom --check_postconditions --civer tags_specification.circom```

we obtain the next output:

```text
-> All postconditions were verified :)
  * Number of verified components (postconditions): 3
  * Number of failed components (postconditions): 0
  * Number of timeout components (postconditions): 0
```

When dealing with cryptographic structures, some properties are often assumed by the programmers. CIVER usually needs these properties to reason about the different properties of the circuit. In this case, we can use the instruction `spec_fact Exp` to claim a fact that CIVER interprets as true. 

## Modularity
CIVER takes advantage of the hierarchical structure of circom circuits and attack the problem in a bottom-up modular way, reducing the number of constraints that need to be considered to verify the properties at each component of the circuit.
An advantage of the approach is that it gives extra information about the potential bugs of the circuit when the verification fails. For example, in case there is a bug in a subcomponent `C` but the rest of the circuit is safe, our approach is able to distinguish that the only erroneous behavior appears in `C`, instead of just flagging the complete circuit as buggy.

## Upcoming Features

CIVER is actively evolving, and several powerful features are planned for an upcoming release:

- **Multiple SMT Solver Support**  
  Currently, CIVER relies on the **Z3** SMT solver. Future versions will allow the user to select alternative solvers, such as **cvc5**, as well as integrate additional SMT back-ends to improve performance and scalability.

- **Support for Additional Constraint Systems**  
  In addition to circom circuits, CIVER will soon be able to verify circuits provided directly as constraint systems, including:  
  - **R1CS (Rank-1 Constraint Systems)**  
  - **PLONK**  
  - **ACIR (Aztec Circuit Intermediate Representation)**  

- **Enhanced Bus Support and Relational Specifications**  
  The current version of **circom supported is 2.1.6**. Upcoming versions of CIVER will:  
  - Enable the use of **buses** in circuit specifications.    
  - Future versions will allow users to **formally specify the semantics of tags for buses**.
  - Preconditions and postconditions will be able to **involve multiple signals within a component**, allowing the specification of more expressive functional behaviors.

These features will expand CIVER’s ability to handle larger circuits, heterogeneous constraints, and richer correctness specifications.


