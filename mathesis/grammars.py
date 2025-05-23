from __future__ import annotations

from abc import ABC

from lark import Lark, Transformer

from mathesis.forms import (
    Atom,
    Top,
    Bottom,
    Conditional,
    Conjunction,
    Disjunction,
    Negation,
    Particular,
    Universal,
)


class ToFml(Transformer):
    def atom(self, v):
        if len(v) == 1:  # only a predicate (proposition)
            return Atom(v[0])
        else:
            return Atom(v[0], terms=v[1:])

    def top(self, v):
        return Top()

    def bottom(self, v):
        return Bottom()

    def negation(self, v):
        return Negation(*v)

    def universal(self, v):
        return Universal(*v)

    def particular(self, v):
        return Particular(*v)

    def conjunction(self, v):
        return Conjunction(*v)

    def disjunction(self, v):
        return Disjunction(*v)

    def conditional(self, v):
        return Conditional(*v)


class Grammar(ABC):
    """Abstract class for grammars."""

    grammar_rules: str

    def __repr__(self):
        return self.grammar_rules

    # @abstractmethod
    # def parse(self, text_or_list: str | list):
    #     raise NotImplementedError()

    def __init__(self):
        self.grammar = Lark(self.grammar_rules, start="fml")

    def parse(self, text_or_list: str | list):
        """Parse a string or a list of strings into formula object(s).

        Args:
            text_or_list (str | list): A string or a list of strings representing formula(s).
        """

        # print(fml_strings)
        if isinstance(text_or_list, list):
            fml_strings = text_or_list
            fmls = []
            for fml_string in fml_strings:
                tree = self.grammar.parse(fml_string)
                fml = ToFml().transform(tree)
                fmls.append(fml)
            return fmls
        else:
            fml_string = text_or_list
            tree = self.grammar.parse(fml_string)
            fml = ToFml().transform(tree)
            return fml


class BasicPropositionalGrammar(Grammar):
    """Basic grammar for the propositional language."""

    grammar_rules = r"""
?fml: conditional
    | disjunction
    | conjunction
    | negation
    | top
    | bottom
    | atom
    | "(" fml ")"

ATOM : /\w+/

atom : ATOM
top : "⊤"
bottom : "⊥"
negation : "¬" fml
conjunction : (conjunction | fml) "∧" fml
disjunction : (disjunction | fml) "∨" fml
conditional : fml "{conditional_symbol}" fml
necc : "□" fml
poss : "◇" fml

%import common.WS
%ignore WS
""".lstrip()

    def __init__(self, symbols={"conditional": "→"}):
        self.grammar_rules = self.grammar_rules.format(
            conditional_symbol=symbols["conditional"]
        )
        super().__init__()


class BasicGrammar(BasicPropositionalGrammar):
    """Basic grammar for the first-order language."""

    grammar_rules = r"""
?fml: conditional
    | disjunction
    | conjunction
    | negation
    | universal
    | particular
    | top
    | bottom
    | atom
    | "(" fml ")"

PREDICATE: /\w+/
TERM: /\w+/

atom : PREDICATE ("(" TERM ("," TERM)* ")")?
top : "⊤"
bottom : "⊥"
negation : "¬" fml
conjunction : fml "∧" fml
disjunction : fml "∨" fml
conditional : fml "{conditional_symbol}" fml
necc : "□" fml
poss : "◇" fml
universal : "∀" TERM fml
particular : "∃" TERM fml

%import common.WS
%ignore WS
""".lstrip()
