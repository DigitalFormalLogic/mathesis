from mathesis.grammars import (
    BasicPropositionalGrammar,
    BasicGrammar
)
from mathesis.forms import (
    Atom,
    Top,
    Bottom,
    Negation,
    Conjunction,
    Disjunction,
    Conditional,
    Universal,
    Particular
)


def test_propositional_grammar():
    grammar = BasicPropositionalGrammar()
    assert grammar.parse("⊥ ∨ (B → C)") == Disjunction(
        Bottom(),
        Conditional(
            Atom("B"),
            Atom("C")
        )
    )
    assert grammar.parse("⊤ ∧ (P_1 ∧ ¬P_2)") == Conjunction(
        Top(),
        Conjunction(
            Atom("P_1"),
            Negation(Atom("P_2"))
        )
    )

    # Test for the order of precedence of operators
    assert grammar.parse("P ∨ Q ∧ ¬R → T") == Conditional(
        Disjunction(
            Atom("P"),
            Conjunction(
                Atom("Q"),
                Negation(Atom("R"))
            )
        ),
        Atom("T")
    )

    # Test for symbol customization
    grammar = BasicPropositionalGrammar(
        symbols={"conditional": "->"}
    )
    assert grammar.parse("A -> B") == Conditional(Atom("A"), Atom("B"))


def test_first_order_grammar():
    grammar = BasicGrammar()
    assert grammar.parse("∀x((P(x) ∧ Q(x)) → R(x, x))") == Universal(
        "x",
        Conditional(
            Conjunction(
                Atom("P", terms=["x"]),
                Atom("Q", terms=["x"])
            ),
            Atom("R", terms=["x", "x"])
        )
    )

    assert grammar.parse("∃y∀x(P123(x, y) ∨ P123(y, x))") == Particular(
        "y",
        Universal(
            "x",
            Disjunction(
                Atom("P123", terms=["x", "y"]),
                Atom("P123", terms=["y", "x"])
            )
        )
    )

    # Test with nullary predicates (propositions)
    assert grammar.parse("⊤ ∨ (A → B)") == Disjunction(
        Top(),
        Conditional(
            Atom("A"),
            Atom("B")
        )
    )
