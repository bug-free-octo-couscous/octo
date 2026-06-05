# octo

A minimalist type checker implementation for a Cubical Type Theory variant (Cubical Lambda calculus) written in Haskell. It features an interval algebra ($\mathbb{I}$) with DNF representation, dependent function types ($\Pi$), dependent pair types ($\Sigma$), Path types, and advanced cubical primitives such as homogeneous composition (`hcomp`), univalence (`ua`), and Glue types.

For the exhaustive specification, formal rules, and granular syntax definitions of this language, please visit the official documentation page:
👉 **[bug-free-octo-couscous.github.io](https://bug-free-octo-couscous.github.io)**

---

## Features

- **Interval Algebra ($\mathbb{I}$):** Full support for the interval variables (`i0`, `i1`), connections (`and`, `or`), and reversal (`not_`), fully evaluated and normalized via Disjunctive Normal Form (DNF).
- **Core Type System:** Standard Dependent Pi ($\Pi$) and Sigma ($\Sigma$) types with bidirectional inference and checking.
- **Cubical Path Types:** High-dimensional path abstractions (`⟨i⟩ e`) and applications (`p @ r`) with endpoint restriction validations.
- **Higher-Dimensional Primitives:** Supports `hcomp` (homogeneous composition), `transport`, `Glue`, `glue`, and `unglue` for handling univalence and equivalence structures.
- **Global Environment & REPL File Processor:** Processes declarative source code statements (`def`, `check`) sequentially while maintaining global scope.

---

## Codebase Structure

The project is organized cleanly across modular Haskell components:

- **`Syntax.hs`**: Defines the `Term` algebraic data type containing all expressions, types, and cubical operations, alongside de Bruijn index management routines (`shift`, `subst`, `beta`).
- **`Interval.hs`**: Handles the interval algebra syntax and normalizes dimensions into a DNF logic system (`dnfMeet`, `dnfJoin`, `dnfNeg`).
- **`Parser.hs`**: A monadic combinator parser that decodes keywords, variables, interval expressions, and top-level definitions.
- **`TypeChecker.hs`**: Implements the core bidirectional type-checking algorithm (`infer` and `check`), face-restriction controls, and context management.
- **`Equality.hs`**: Evaluates definitional equivalence using structural identity and contextual $\eta$-expansion fueled algorithms.
- **`Eval.hs`**: The computational engine performing weak-head and deep reduction of terms, boundary handling, and substitution applications.
- **`Env.hs`**: Provisions global context translation, type checking in context, and de Bruijn mapping for global definitions.
- **`Main.hs`**: Provides the executive entry point, scanning bare terms or file-based script statements iteratively.

---

## Language Syntax at a Glance

Top-level declarations follow this structure:

```hs
-- Define a constant with explicit type annotation
def id : PI (A : U0). PI (x : A). A =
  lambda_ A. lambda_ x. x

-- Type inferred definition
def id_infer = lambda_ A. lambda_ x. x

-- Validate a term against a type without binding
check "idTest" : PI (A : U0). PI (x : A). A = id

```

> 💡 **Detailed Syntax Rules:** To learn how to write `hcomp`, paths, or `Glue` expressions correctly, check out the comprehensive grammar reference at **[bug-free-octo-couscous.github.io](https://www.google.com/url?sa=E&source=gmail&q=https://bug-free-octo-couscous.github.io)**.

---

## Getting Started

### Prerequisites

Ensure you have GHC (Glasgow Haskell Compiler) and Cabal (or Stack) installed.

### Compilation

Compile the project directly using GHC:

```bash
cabal run
```

### Running the Interpreter

Pass one or more source files containing statements separated by blank lines:

```bash
cabal run octo -- test/comprehensive_tests.ctt
cabal run octo -- test/funext_tests.ctt
```