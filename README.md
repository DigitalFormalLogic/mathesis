# Mathesis

[![CI](https://github.com/digitalformallogic/mathesis/actions/workflows/ci.yml/badge.svg)](https://github.com/digitalformallogic/mathesis/actions/workflows/ci.yml)
[![PyPI](https://img.shields.io/pypi/v/mathesis.svg)](https://pypi.org/project/mathesis/)
[![Documentation Status](https://img.shields.io/github/actions/workflow/status/digitalformallogic/mathesis/pages/pages-build-deployment?branch=gh-pages&label=docs)](https://digitalformallogic.github.io/mathesis/)
[![PyPI downloads](https://img.shields.io/pypi/dm/mathesis.svg)](https://pypistats.org/packages/mathesis)

[Mathesis](//github.com/digitalformallogic/mathesis) is a human-friendly Python library for computational formal logic (including mathematical, symbolic, philosophical logic), formal semantics, and theorem proving.
It is particularly well-suited for:

- Students learning logic and educators teaching it
- Researchers in fields like logic, philosophy, linguistics, computer science, and many others

**Documentation:** <https://digitalformallogic.github.io/mathesis/>

## Installation

```bash
pip install mathesis
```

## Key features

- Interactive theorem proving for humans (proof assistant)
- Automated reasoning (theorem prover)
- Define models and check validity of inferences in the models
- JupyterLab/Jupyter Notebook support
- Output formulas/proofs in LaTeX
- Customizable ASCII/Unicode syntax (like `A -> B`, `A → B`, `A ⊃ B` for the conditional)

## Supported logics

### Propositional logics

|   | Truth Table | Tableau | Natural Deduction | Sequent Calculus |
|---:|:---:|:---:|:---:|:---:|
| Classical logic | ✅ | ✅ | ✅ | ✅ |
| Many-valued logics | ✅ | - | - | - |
| Intuitionistic logic | n/a | - | - | ✅ |

#### In Progress

- Modal logics
- Fuzzy logics
- Substructural logics
- Epistemic, doxastic, deontic logics
- Temporal logics

### First-order logics (quantified, predicate logics)

|   | Model | Tableau | Natural Deduction | Sequent Calculus |
|---:|:---:|:---:|:---:|:---:|
| Classical logic | ✅ | ✅ | ✅ | - |

#### In Progress

- Many-valued logics
- Modal logics
- Intuitionistic logic
- Fuzzy logics
- Substructural logics
- Higher-order logics

## Development status

### Proof theories

- **Tableaux** (semantic tableaux, analytic tableaux)
    * [x] Unsigned tableaux
    * [x] Signed tableaux
- **Hilbert systems**
    * [ ] Hilbert systems
- **Natural deduction**
    * [x] Generic natural deduction
    * [x] Gentzen-style natural deduction (Output)
    * [ ] Fitch-style natural deduction
- **Sequent calculi** (Gentzen-style sequent calculi)
    - [x] Two-sided sequent calculi
    - [ ] Hilbert systems in sequent calculus
    - [ ] Natural deduction in sequent calculus

### Semantics

- [x] Truth tables
- [x] Set-theoretic models
- [ ] Possible world semantics (Kripke semantics)
- [ ] Algebraic semantics
- [ ] Game-theoretic semantics
- [ ] Category-theoretic semantics

## Internals

- Parsing with [lark](https://github.com/lark-parser/lark)
- Trees with [anytree](https://github.com/c0fec0de/anytree)

## Roadmap

- [ ] Add tests (WIP)
- [ ] Hilbert systems
- [x] Natural deduction
- [ ] Boolean algebra
- [ ] Type theory
- [ ] Metatheorems
- [ ] Output graphical representations of models
- [ ] Support tptp syntax
