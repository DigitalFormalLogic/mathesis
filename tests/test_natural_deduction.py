import pytest

from mathesis.grammars import BasicGrammar
from mathesis.deduction.natural_deduction import NDTree, rules


grammar = BasicGrammar()


def test_universal_intro_creates_instantiated_goal():
    conclusion = grammar.parse("∀x P(x)")
    derivation = NDTree([], conclusion)

    derivation.apply(derivation[1], rules.Universal.Intro("c"))

    child = derivation._sequent_tree.root.children[0]
    assert str(child.right[0].fml) == "P(c)"


def test_universal_intro_rejects_non_fresh_terms():
    premises = grammar.parse(["P(a)"])
    conclusion = grammar.parse("∀x P(x)")
    derivation = NDTree(premises, conclusion)

    with pytest.raises(AssertionError):
        derivation.apply(derivation[2], rules.Universal.Intro("a"))


def test_universal_elim_instantiates_premise():
    premises = grammar.parse(["∀x(P(x)→Q(x))"])
    conclusion = grammar.parse("Q(a)")
    derivation = NDTree(premises, conclusion)

    derivation.apply(derivation[1], rules.Universal.Elim("a"))

    child = derivation._sequent_tree.root.children[0]
    left_formulas = [str(item.fml) for item in child.left]
    assert "P(a) → Q(a)" in left_formulas


def test_particular_intro_creates_instantiated_goal():
    conclusion = grammar.parse("∃x Q(x)")
    derivation = NDTree([], conclusion)

    derivation.apply(derivation[1], rules.Particular.Intro("a"))

    child = derivation._sequent_tree.root.children[0]
    assert str(child.right[0].fml) == "Q(a)"


def test_particular_elim_enforces_fresh_term_and_adds_assumption():
    premises = grammar.parse(["∃x P(x)", "R(a)"])
    conclusion = grammar.parse("Q")
    derivation = NDTree(premises, conclusion)

    with pytest.raises(AssertionError):
        derivation.apply(derivation[1], rules.Particular.Elim("a"))

    derivation.apply(derivation[1], rules.Particular.Elim("c"))

    child = derivation._sequent_tree.root.children[0]
    left_formulas = [str(item.fml) for item in child.left]
    assert "P(c)" in left_formulas
