# Proof in Natural Deduction

## Introduction

In Mathesis, a _state_ of a natural deduction proof (and its subproofs) consists of the premises and the conclusion that are available to the (sub)proof at a given step.
A state is displayed as `<premises> ⇒ <conclusion>`.

Intuitively, the formulas on the left side of `⇒` are what to come to the upper part of the final (sub)proof, and those on the right side of `⇒` are what to come to the lower part of the final (sub)proof.

Natural deduction is a proof system that consists of elimination rules and introduction rules. In Mathesis,

- you can apply an **elimination rule** *up-to-down* to the premises of a (sub)proof to obtain new premises.
- Similarly, you can apply an **introduction rule** *down-to-up* to the conclusion of a (sub)proof and convert it into new subproofs.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar
from mathesis.deduction.natural_deduction import NDTree, rules

grammar = BasicGrammar()

premises = grammar.parse(["A∨B", "B→C"])
conclusion = grammar.parse("A∨C")
deriv = NDTree(premises, conclusion)
print(deriv.tree())

deriv.apply(deriv[1], rules.Disjunction.Elim())
print(deriv.tree())

deriv.apply(deriv[8], rules.Disjunction.Intro("left"))
print(deriv.tree())

deriv.apply(deriv[10], rules.Conditional.Elim())
print(deriv.tree())

deriv.apply(deriv[25], rules.Disjunction.Intro("right"))
print(deriv.tree())
```

## First-order Quantifiers

First-order rules are available through dedicated `rules.Universal` and `rules.Particular` classes. Just as in standard textbooks, instantiations use a concrete term while generalizations require fresh terms that do not occur elsewhere in the branch.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar
from mathesis.deduction.natural_deduction import NDTree, rules

grammar = BasicGrammar()

premises = grammar.parse(["∀x(P(x)→Q(x))", "∃x P(x)"])
conclusion = grammar.parse("∃x Q(x)")

deriv = NDTree(premises, conclusion)
print(deriv.tree())

deriv.apply(deriv[2], rules.Particular.Elim("a"))
deriv.apply(deriv[5], rules.Universal.Elim("a"))
deriv.apply(deriv[8], rules.Conditional.Elim())
deriv.apply(deriv[24], rules.Particular.Intro("a"))

print(deriv.tree())
print(deriv.tree(style="gentzen"))
```

## Render as Gentzen-style Proof

(WIP) Mathesis has an experimental support for rendering a natural deduction proof as a Gentzen-style proof or its LaTeX code.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar
from mathesis.deduction.natural_deduction import NDTree, rules

grammar = BasicGrammar()

premises = grammar.parse(["A∨B", "B→C"])
conclusion = grammar.parse("A∨C")
deriv = NDTree(premises, conclusion)
print(deriv.tree(number=False))

deriv.apply(deriv[1], rules.Disjunction.Elim())
deriv.apply(deriv[8], rules.Disjunction.Intro("left"))
deriv.apply(deriv[10], rules.Conditional.Elim())
deriv.apply(deriv[25], rules.Disjunction.Intro("right"))

print(deriv.tree(style="gentzen"))

print(deriv.latex())
```

$$
\begin{prooftree}
\AxiomC{$A$}
\RightLabel{$\lor$I}
\UnaryInfC{$A \lor C$}
\AxiomC{$B$}
\RightLabel{$\to$E}
\AxiomC{$B \to C$}
\BinaryInfC{$C$}
\RightLabel{$\lor$I}
\UnaryInfC{$A \lor C$}
\RightLabel{$\lor$E}
\AxiomC{$A \lor B$}
\TrinaryInfC{$A \lor C$}
\end{prooftree}
$$

## Render as Fitch-style Proof

WIP

## Render as Suppes-Lemmon-style Proof

WIP

## Render as Sequent Calculus Proof

WIP
