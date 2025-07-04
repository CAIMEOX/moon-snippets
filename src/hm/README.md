# Hindley-Milner Type Inference with Levels

This directory contains a complete implementation of the Hindley-Milner type inference algorithm with the "levels" optimization, also known as Rémy algorithms. This is a foundational algorithm in functional programming languages like Haskell, [Rust](https://rustc-dev-guide.rust-lang.org/type-inference.html) and OCaml.

## What is Hindley-Milner Type Inference?

The Hindley-Milner type system is a type system that can automatically infer the **most general type** for any expression without requiring type annotations. It supports:

- **Polymorphism**: Functions like the identity function can work on any type
- **Type Safety**: All type errors are caught at compile time
- **Principal Types**: Every expression has a unique most general type
- **Decidability**: Type inference always terminates

[Wikipedia](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system) provides a good overview of the algorithm, both the formal deductive system and the practical implementation.

## Key Concepts

Here's a brief overview of the key concepts in the Hindley-Milner type inference algorithm.
This will help you read the code for this project, but for a deeper understanding of the wonders
of HM it's still recommended to read the references in the [latter article](#futher-reading).

### 1. Unification

The process of finding constraints that make two types equal. For example:

- Unifying `X -> Y` with `Int -> Bool` results in `X = Int, Y = Bool`
- Unifying `X` with `X -> Int` fails (occurs check - would create infinite type)

### 2. Let-Generalization

Converting type variables to universal quantifiers. This happens at let-bindings:

```text
let id = λx.x in ...
```

The type of `id` gets generalized from `'a -> 'a` to `forall a. a -> a`

### 3. Instantiation

Creating fresh copies of polymorphic types when they're used:

```text
id 5        // id gets instantiated as Int -> Int
id true     // id gets instantiated as Bool -> Bool
```

### 4. Levels (The Key Optimization)

The levels system tracks the nesting depth of let-expressions to determine which type variables can be generalized. This prevents premature generalization and makes the algorithm efficient.

## Running the Examples

The test suite in `hm.mbt` demonstrates the system in action.

## Futher Reading

The inference algorithm for the HM type system has been well documented in a number of articles, so if you have trouble reading this code, please read the following references.

- [How OCaml type checker works -- or what polymorphism and garbage collection have in common](https://okmij.org/ftp/ML/generalization.html)
  - Oleg Kiselyov's excellent explanation of the HM algorithm and its optimizations. This could be the first document that explains the levels optimization in detail.
  - For Chinese readers there is a [translated version](https://zhuanlan.zhihu.com/p/707994957) by [閱卜錄](https://github.com/cireu).
- [Practical Type Inference with Levels](https://dl.acm.org/doi/10.1145/3729338) - Although the level based approach has been widely used, its formalization was not completed until 2025, when it won the PLDI Distinguished Paper Award.
- [Principal Type Inference under a Prefix](https://www.microsoft.com/en-us/research/publication/principal-type-inference-under-a-prefix/)
  - The beauty of the HM system is that there always exists a **most general type** that encompasses all possible derivations. But if you want to extend the type system with additional features which often require complex side conditions to the type rules to maintain principal types.
  - This paper shows a HMQ type system, always derives principal types that correspond to the types inferred by the HM algorithm, but with better extensibility, e.g. Koka's static overloading system.
