---
title: Project 5 - STLC with Type Reconstruction
layout: default
start: 16 Nov 2015, 00:00 (Europe/Zurich)
index: 8
---

# Project 5: STLC with Type Reconstruction

**Hand in:** 01 Dec 2015, 23:59 (Europe/Zurich)<br/>
**Project template:** [5-inference.zip](projects/5-inference.zip)

In this exercise, you will write a Hindley-Milner type inferencer for a modification of the simply typed λ-calculus
with booleans, numbers and `let`:

    t ::= "true"                            true value
        | "false"                           false value
        | numericLit                        integer
        | "pred" t                          predecessor
        | "succ" t                          successor
        | "iszero" t                        iszero
        | "if" t "then" t "else" t          if
        | x                                 variable
        | "\" x [ ":" T ] "." t             abstraction
        | t t                               application (left associative)
        | "let" x [ ":" T ] "=" t "in" t    let
        | "(" t ")"

    T ::= "Bool"                            boolean type
        | "Nat"                             numeric type
        | T "->" T                          function types  (right associative)
        | "(" T ")"

The main difference with the usual STLC is that the type annotations for lambdas and for `let` are optional
(which is expressed by the square brackets around them in the syntax spec).
This means that the programmer can either explicitly specify types for introduced variables
or leave them empty to be inferred by the typechecker.

### Type Inference 101

Unlike the typecheckers in projects #3 and #4 that went top-down on input abstract syntax trees
and assigned types in one pass, this one is going to be more involved, featuring two phases:

  1. During the first phase, our Hindley-Milner typechecker will recursively collect constraints on the types of expressions present in the input tree.
  2. Afterwards in the second phase, it is going to solve these constraints, either producing the resulting type or failing with an error.

Below we will explain how this works in details, essentially recapping what's written in TAPL.
The methodology that has been presented during the lecture on type reconstruction and polymorphism
is somewhat different, but in fact it talks about exactly the same thing. While implementing the type inferencer,
take time to understand how both approaches relate to the code that you're writing,
because you'll need to know both on the upcoming exam.

*You may wonder how what we're doing is related to the real world. The general notion of type inference
is very powerful and a lot of languages (C\#, Java, C++, F\#, Scala, Haskell, Swift, Rust and many others) employ it.
However, different languages do inference differently, and the most popular approach, called local type inference,
doesn't involve anything like Hindley-Milner. Nevertheless, some languages (F\# and Haskell among the aforementioned ones)
employ algorithms that resemble Hindley-Milner, so our project will let you develop useful intuitions.*

### Phase 1: Collecting constraints

`def collect(env: Env, t: Term): (Type, List[Constraint]) = ???`

The basic idea of the first phase is to recursively apply typing rules on the input tree, just as in projects #3/4.
However, this time the rules are not just `Γ ⊢ t : T`, but look like `Γ ⊢ t : T | C`, where `C` stands for a constraint set.
Without further ado, here are the typing rules for STLC augmented with constraints (you may want to look into p322 of TAPL
for a better formatted version):

    Γ ⊢ true : Bool | {}

    Γ ⊢ false : Bool | {}

    Γ ⊢ 0 : Nat | {}

    Γ ⊢ t : T | C    C' = C ∪ {T=Nat}
    ---------------------------------
        Γ ⊢ pred t : Nat | C'

    Γ ⊢ t : T | C    C' = C ∪ {T=Nat}
    ---------------------------------
        Γ ⊢ succ t : Nat | C'

    Γ ⊢ t : T | C    C' = C ∪ {T=Nat}
    ---------------------------------
       Γ ⊢ iszero t : Bool | C'

     Γ ⊢ t1: T1 | C1    Γ ⊢ t2 : T2 | C2
              Γ ⊢ t3 : T3 | C3
      C = C1 ∪ C2 ∪ C3 ∪ {T1=Bool, T2=T3}
    -------------------------------------
      Γ ⊢ if t1 then t2 else t3 : T2 | C

       x : T ∈ Γ
    --------------
    Γ ⊢ x : T | {}

       Γ, x : T1 ⊢ t : T2 | C
    -----------------------------
    Γ ⊢ λx: T1. t : T1 -> T2 | C

     Γ, x : X ⊢ t : T2 | C
          X is fresh
    ------------------------
    Γ ⊢ λx. t : X -> T2 | C

     Γ ⊢ t1 : T1 | C1    Γ ⊢ t2 : T2 | C2
    X is fresh, C = C1 ∪ C2 ∪ {T1=T2 -> X}
    --------------------------------------
            Γ ⊢ t1 t2 : X | C

An interesting thing about the presented typing rules is that they involve type variables. If you take a look at the last rule,
you will notice that when typechecking applications, we don't check whether `t1` has a function type.
Instead, we just postulate that it has a function type `T2 -> X` for some `X` that we'll infer later.
Same about typechecking a lambda with an unspecified type of the bound variable.

This is the key insight behind the Hindley-Milner algorithm.
If you don't know the type of something immediately by looking at it, you defer typechecking until you know more.
Amazingly enough, this simple idea is theoretically sound and works really well in practice!

One little remark about theory vs practice. If you compare our rules with the ones given in TAPL, you will notice that we have ignored freshness conditions on type variables: it is necessary that type variables, whenever created, are different from all other type variables in the system. This is easy to achieve when programming the typechecker, and talking about freshness here would only obfuscate the typing rules. However, a formally correct type system needs to include them (and we may ask you to do everything in a formal way during the exam!).

Finally, the most attentive of you guys have probably noticed that the typing rules above don't mention `let`.
This is not an oversight. `let` is a very special case that will be covered later in the document.

### Intermezzo

A fun fact about the type returned by phase 1 is that it's overly optimistic.
Whenever the typechecker can't trivially assign a type to something, it makes up fictional type variables and moves on
(see the last two typing rules provided above, namely the ones that say "X is fresh").
For example, applying phase 1 to `(\b. if b then false else true)` will yield the type `X -> Bool`
along with the constraint set that has been generated by the typing rules: `[X = Bool]`.

Therefore, in order to complete typechecking, we will need to solve the constraints.
This is done by a procedure called *unification*,
which will tell us two things: A) whether the input is well-typed, B) how to make sense of the type returned by phase 1.

Phase 2 is going to process the constraint set and either produce an error
or return a *substitution*, i.e. a mapping from type variables to types
that can be used to replace type variables in the type returned by phase 1.
For example, unification of the constraint set `[X = Bool]` will yield the substitution `[X → Bool]`,
and applying that substitution to `X -> Bool` will produce the resulting type of the example expression:
`Bool -> Bool` (note the arrows that we're using!).

### Phase 2: Unification

`def unify(c: List[Constraint]): Substitution = ???`

The unification algorithm works by starting with an empty substitution `[]` and then going through
the constraints one by one, extending the initial substitution (i.e. adding substitution rules) as it goes.
Concretely, for every constraint `S = T` in the constraint set, the unification algorithm works as follows:

1. If `S` and `T` are the same type, e.g. as in `Nat = Nat` or `X1 = X1`, then do nothing and proceed to the next constraint.

1. If `S` is a type variable, and `S` doesn't appear in `T`, extend the resulting substitution with `[S → T]` and proceed to the next constraint. If `S` appears in `T`, then it's a unification error, because otherwise our algorithm is going to loop infinitely.

    A tricky detail here lies in the necessity to apply `S → T` to the remaining constraints in the constraint set.
    Otherwise, things like `[X = Nat, Y = X]` aren't going to unify in a useful way.

1. If `T` is a type variable, and `S` is not, proceed analogously to the previous case.

1. If `S` and `T` are both function types, as in `S1 -> S2 = T1 -> T2`, recursively unify `S1` and `T1` as well as `S2` and `T2`, and proceed to the next constraint.

1. Else fail. This means that it's impossible to find a substitution that satisfies the constraint set, which ultimately means a type error.

### The elephant in the room...

By now, you're probably wondering what's so special about `let` that we've been ignoring it all this time.
After all, `let` trivially desugars to an application of a lambda, right?

Well, in fact there's nothing special about `let` as a language construct -
we're just going to use it as a hack to encode special behavior into the typechecking algorithm.

### ...and the dirty secrets of language designers

Let's recap the current situation. We have a very neat algorithm that lets us completely drop type annotations
from lambdas and have these annotations inferred. Now instead of writing:

    double = \f: Bool -> Bool. \x: Bool. f(f(x))
    double (\x: Bool. if x then true else false) false

We can write `double = \f.\x.f(f(x)); double (\x.if x then true else false) false`
(please bear with my imaginary syntax) thanks to *type inference*, which is definitely a useful language feature.

However, our language is definitely not cool enough, because there's another cool feature
that's called *polymorphism*. If our language had polymorphism, we would be able to write
the following code, using the function `double` polymorphically, i.e. being able to run the same code
in different contexts:

    double = \f.\x. f(f(x))
    if (double (\x. if x then false else true) false)
    then double (\x. succ x) 0
    else 0

Unfortunately, our type inference algorithm can't handle such a program, because the first usage of `double`
will add `X = Nat` to the constraint set (where `X` is a type variable introduced for `x`),
whereas the second usage will add `X = Bool` to the constraint, and we'll get a contradiction during unification.

Now, as language designers, we can't resist a possibility to make our language more powerful.
We're going to take an existing language feature, `let`, and repurpose it to exhibit the semantics
that we're currently fond of. As a result, our calculus will become more complicated, our implementation
will become more complicated, and you will have to understand and implement all that.
But hey - it's gotta be fun!

### A boring tl;dr of the previous section

Our calculus is really neat, but it's not cool enough. Therefore, we're going to incorporate
a new feature into it, and we need a dedicated language construct to express that feature.
We don't want to introduce new language features, so we'll take `let` and make it mean something else.

### Let-polymorphism

The way to incorporate polymorphism into typechecking `let` is to generalize the type of `double` by making it a *type scheme*. A type scheme is a recipe for creating types, and it works by abstracting over its type variables. Each time `double` is used, we instantiate the type scheme to yield a new type, which means that type variables participating in the constraints aren't going to contradict each other.

A *type scheme* is: 1) a type, together with 2) a list of type variables that can be instantiated. Instantiation means inventing fresh type variables for each of the arguments of a type scheme, and substituting them with the fresh ones. For example, `TypeScheme(List(a), a -> a)` instantiates to `a1 -> a1`, and that's how we'll be able to avoid contradicting constraints.

To accommodate this intuition, we do the following four steps:

  1. Change `Г`. Previously, the environment contained mappings from names to types, but now it is going to contain mappings from names to type schemes. Each time we lookup a variable in the environment, we instantiate its type scheme and return the result of instantiation.

  2. Change the typing rules for lambdas. Instead of binding names to types, these rules are now going to bind names to boring type schemes with empty lists of type variables. Nothing essential changes here - we're just trivially generalizing the old rules.

  3. Do not change other existing typing rules. The remaining rules don't modify `Г`, so we don't need to do anything with them.

  4. Introduce a new typing rule that handles `let x = v in t` (a typing rule for `let x: T = v in T` doesn't change from project #3). Here's an implementation sketch (consult chapter 22.7 of TAPL for a detailed explanation):

      1. We type the right hand side `v` obtaining a type `S` and a set of constraints `C`.

      1. We use unification on `C` and apply the result to `S` to find its first approximation as type. At this point, the substitution we found should be applied to the current environment too, since we have committed to a set of bindings between type variables and types! Let's call this new type `T`

      1. We generalize some type variables inside `T` and obtain a type scheme.

          *Important:* We need to be careful about what type variables we generalize. We should not generalize any type variables appearing in the environment, because they appear in constraints that need to be satisfied. For example:


              (\f.\x. let g = f in g(0)) (\x.if x then false else true) true

          While typing `let`, the environment will contain bindings such as `[f -> X1, g -> X2]` and some constraints on them, like { `X1 = Bool -> Bool` }. Notice inside `let` we use `g` as a function on `Nat` and that should be a constraint on `f` too, which is an argument of the function. Applying this function to `Bool` should fail. If we wrongly generalize, we would get a `TypeScheme(X1, X1)` for `g` which would be instantiated at use to `X3`, which would be constrained to be a function on `Nat`. Notice how this constraint will not involve the `X1` anymore, and the typechecker would miss the type error! The bottom line is, generalizing type `T` to a type scheme should only abstract type variables that don't appear in the current environment.

      1. We extend the environment with a binding from `x` to its type scheme.

      1. We typecheck `t` with the new environment.

### What you have to do

  1. Implement `collect` aka phase 1 of the Hindley-Milner typechecking algorithm
     with support for the entire language explained above, including `let`.

  2. Implement `unify` aka phase 2 of the Hindley-Milner typechecking algorithm,
     again for the whole language. If you encounter an error during unification,
     throw a `TypeError` exception.

### Implementation hints

  * In this project template, you will be given a working parser, so don't worry about parsing at all.
We're also not interested in evaluation, just in typechecking, so you don't need to implement an evaluator either.

  * You can start small by implementing the initial typing rules that don't include `let` and
extending the environment with trivial type schemes where necessary.
Our tests will check your progress at this stage, allowing you to make sure your initial implementation is okay before moving on to `let`.

  * While coding the assignment, only change `Infer.scala` and
    do not change names or signatures of any public methods or classes.
    If you do otherwise, your submission may fail to compile.

### Development and debugging

We provide a simple runnner for your application that lets you quickly debug your current implementation. When you implement `collect` and `unify`, it should produce results like:

**Example 1**:

input:

    \b. if b then false else true

output:

    typed: (Bool -> Bool)

**Example 2**:

input:

    \b. if b then 1 else true

output:

    type error: Could not unify: Nat with Bool

As usual, we won't be grading you on the format of console output, your style of prettyprinting or the exact content of your error messages. All examples here are purely illustratory.