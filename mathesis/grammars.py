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
    Possibility,
    Necessity,
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
    
    def possibility(self, v):
        return Possibility(*v)
    
    def necessity(self, v):
        return Necessity(*v)

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

    default_symbols = {
        "top": "⊤",
        "bottom": "⊥",
        "negation": "¬",
        "conjunction": "∧",
        "disjunction": "∨",
        "conditional": "→",
        "necessity": "□",
        "possibility": "◇",
    }

    grammar_rules = r"""
?fml: conditional
    | disjunction
    | conjunction
    | negation
    | necessity
    | possibility
    | top
    | bottom
    | atom
    | "(" fml ")"

ATOM : /\w+/

atom : ATOM
top : "{top}"
bottom : "{bottom}"
negation : "{negation}" fml
conjunction : (conjunction | fml) "{conjunction}" fml
disjunction : (disjunction | fml) "{disjunction}" fml
conditional : fml "{conditional}" fml
necessity : "{necessity}" fml
possibility : "{possibility}" fml

%import common.WS
%ignore WS
""".lstrip()

    def __init__(self, symbols=None):
        merged = self.default_symbols.copy()
        if symbols is not None:
            merged.update(symbols)
        self.symbols = merged
        self.grammar_rules = self.grammar_rules.format(**merged)
        super().__init__()


class BasicGrammar(BasicPropositionalGrammar):
    """Basic grammar for the first-order language."""

    default_symbols = {
        **BasicPropositionalGrammar.default_symbols,
        "universal": "∀",
        "particular": "∃",
    }

    grammar_rules = r"""
?fml: conditional
    | disjunction
    | conjunction
    | negation
    | necessity
    | possibility
    | universal
    | particular
    | top
    | bottom
    | atom
    | "(" fml ")"

PREDICATE: /\w+/
TERM: /\w+/

atom : PREDICATE ("(" TERM ("," TERM)* ")")?
top : "{top}"
bottom : "{bottom}"
negation : "{negation}" fml
conjunction : fml "{conjunction}" fml
disjunction : fml "{disjunction}" fml
conditional : fml "{conditional}" fml
necessity : "{necessity}" fml
possibility : "{possibility}" fml
universal : "{universal}" TERM fml
particular : "{particular}" TERM fml

%import common.WS
%ignore WS
""".lstrip()
