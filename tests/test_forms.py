from mathesis.forms import (
    Formula,
    Atom,
    Top,
    Bottom,
    Negation,
    Disjunction,
    Conjunction,
    Conditional,
    Universal,
    Particular
)


# ⊤ ∨ (¬Q ∨ R)
propositional_formula_1 = Disjunction(
    Top(),
    Disjunction(
        Negation(Atom("Q")),
        Atom("R")
    )
)

# (P ∧ ¬P) → ⊥
propositional_formula_2 = Conditional(
    Conjunction(
        Atom("P"),
        Negation(Atom("P"))
    ),
    Bottom()
)

# ∀x(P(x) → (Q(x) ∨ R(x)))
quantified_formula_1 = Universal(
    "x",
    Conditional(
        Atom("P", terms=["x"]),
        Disjunction(
            Atom("Q", terms=["x"]),
            Atom("R", terms=["x"])
        )
    )
)

# ∃y(¬Q(y) ∧ ¬R(a, b, y))
quantified_formula_2 = Particular(
    "y",
    Conjunction(
        Negation(Atom("Q", terms=["y"])),
        Negation(Atom("R", terms=["a", "b", "y"]))
    )
)


def test_repr():
    assert repr(propositional_formula_1) == "Disj[Top, Disj[Neg[Atom[Q]], Atom[R]]]"
    assert repr(propositional_formula_2) == "Cond[Conj[Atom[P], Neg[Atom[P]]], Bottom]"
    assert repr(quantified_formula_1) == "Forall<x>[Cond[Atom[P(x)], Disj[Atom[Q(x)], Atom[R(x)]]]]"
    assert repr(quantified_formula_2) == "Exists<y>[Conj[Neg[Atom[Q(y)]], Neg[Atom[R(a, b, y)]]]]"


def test_str():
    assert str(propositional_formula_1) == "⊤ ∨ (¬Q ∨ R)"
    assert str(propositional_formula_2) == "(P ∧ ¬P) → ⊥"
    assert str(quantified_formula_1) == "∀x(P(x) → (Q(x) ∨ R(x)))"
    assert str(quantified_formula_2) == "∃y(¬Q(y) ∧ ¬R(a, b, y))"


def test_latex():
    assert propositional_formula_1.latex() == r"\top \lor (\neg Q \lor R)"
    assert propositional_formula_2.latex() == r"(P \land \neg P) \to \bot"
    assert quantified_formula_1.latex() == r"\forall x (P(x) \to (Q(x) \lor R(x)))"
    assert quantified_formula_2.latex() == r"\exists y (\neg Q(y) \land \neg R(a, b, y))"


def test_atoms():
    assert propositional_formula_1.atoms == {
        "Q": [Atom("Q")],
        "R": [Atom("R")]
    }
    assert propositional_formula_2.atoms == {
        "P": [Atom("P"), Atom("P")]
    }
    assert quantified_formula_1.atoms == {
        "P(x)": [Atom("P", terms=["x"])],
        "Q(x)": [Atom("Q", terms=["x"])],
        "R(x)": [Atom("R", terms=["x"])]
    }
    assert quantified_formula_2.atoms == {
        "Q(y)": [Atom("Q", terms=["y"])],
        "R(a, b, y)": [Atom("R", terms=["a", "b", "y"])]
    }


def test_atom_symbols():
    assert propositional_formula_1.atom_symbols == ["Q", "R"]
    assert propositional_formula_2.atom_symbols == ["P"]
    assert quantified_formula_1.atom_symbols == ["P(x)", "Q(x)", "R(x)"]
    assert quantified_formula_2.atom_symbols == ["Q(y)", "R(a, b, y)"]


def test_equality():
    assert propositional_formula_1 == propositional_formula_1
    assert propositional_formula_2 != propositional_formula_1
    assert propositional_formula_2 != quantified_formula_1
    assert quantified_formula_1 == quantified_formula_1
    assert quantified_formula_2 == quantified_formula_2
    assert quantified_formula_1 != quantified_formula_2


def test_free_terms():
    assert propositional_formula_1.free_terms == []
    assert propositional_formula_2.free_terms == []
    assert quantified_formula_1.free_terms == []
    assert quantified_formula_2.free_terms == ["a", "b"]


def test_replace_term():
    assert propositional_formula_1.replace_term("Q", "R") == propositional_formula_1
    assert quantified_formula_1.replace_term("x", "y") == Conditional(
        Atom("P", terms=["y"]),
        Disjunction(
            Atom("Q", terms=["y"]),
            Atom("R", terms=["y"])
        )
    )
    assert quantified_formula_2.replace_term("a", "b") == Conjunction(
        Negation(Atom("Q", terms=["y"])),
        Negation(Atom("R", terms=["b", "b", "y"]))
    )
