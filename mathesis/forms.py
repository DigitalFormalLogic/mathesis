from __future__ import annotations
from typing import Optional

from copy import copy, deepcopy


class Formula:
    @property
    def atom_symbols(self):
        return list(self.atoms.keys())

    def transform(self, transformer):
        return transformer(self)

    def __eq__(self, other) -> bool:
        if not isinstance(other, Formula):
            return NotImplemented

        elif not isinstance(other, type(self)):  # not the same (main) connective
            return False

        return str(self) == str(other)


class Atom(Formula):
    _latex: str | None

    def __init__(self, predicate: str, terms: list[str]=[], latex: Optional[str]=None):
        self.predicate = predicate
        self.terms = terms
        self._latex = latex

    @property
    def symbol(self) -> str:
        if len(self.terms) == 0:
            return f"{self.predicate}"
        else:
            return f"{self.predicate}({', '.join(self.terms)})"

    @property
    def atoms(self):
        return {self.symbol: [self]}

    @property
    def free_terms(self):
        return self.terms

    def replace_term(self, replaced_term, replacing_term):
        fml = self.clone()
        fml.terms = [
            replacing_term if term == replaced_term else term for term in self.terms
        ]
        return fml

    def clone(self):
        clone = deepcopy(self)
        clone.__dict__ = deepcopy(clone.__dict__)
        return clone

    def latex(self):
        return f"{self._latex or self.symbol}"

    def __str__(self) -> str:
        return f"{self.symbol}"

    def __repr__(self) -> str:
        return f"Atom[{self.symbol}]"


class Constant(Atom):
    """Base class for Top and Bottom"""

    signature: str
    connective: str
    connective_latex: str

    def __init__(self):
        pass

    @property
    def symbol(self) -> str:
        return self.connective

    @property
    def atoms(self):
        return {}

    @property
    def free_terms(self):
        return []

    def replace_term(self, replaced_term, replacing_term):
        return self

    def latex(self) -> str:
        return self.connective_latex

    def __str__(self) -> str:
        return self.symbol

    def __repr__(self) -> str:
        return self.signature


class Top(Constant):
    signature = "Top"
    connective = "⊤"
    connective_latex = r"\top"


class Bottom(Constant):
    signature = "Bottom"
    connective = "⊥"
    connective_latex = r"\bot"


class Unary(Formula):
    def __init__(self, sub: Formula):
        self.sub = sub

    def clone(self):
        clone = deepcopy(self.sub.clone())
        clone.__dict__ = deepcopy(clone.__dict__)
        return self.__class__(clone)

    @property
    def atoms(self):
        return self.sub.atoms

    @property
    def free_terms(self):
        return self.sub.free_terms

    def replace_term(self, replaced_term, replacing_term):
        fml = self.clone()
        fml.sub = self.sub.replace_term(replaced_term, replacing_term)
        return fml

    def latex(self):
        return f"{self.connective_latex} " + (
            f"({self.sub.latex()})"
            if isinstance(self.sub, Binary)
            else f"{self.sub.latex()}"
        )

    def __str__(self) -> str:
        return self.connective + (
            f"({self.sub})" if isinstance(self.sub, Binary) else f"{self.sub}"
        )

    def __repr__(self) -> str:
        return f"{self.signature}[{repr(self.sub)}]"


class Negation(Unary):
    signature = "Neg"
    connective = "¬"
    connective_latex = r"\neg"


class Binary(Formula):
    subs: tuple[Formula, Formula]

    def __init__(self, sub1: Formula, sub2: Formula):
        self.subs = (sub1, sub2)

    def clone(self):
        clones = [sub.clone() for sub in self.subs]
        for clone in clones:
            clone.__dict__ = deepcopy(clone.__dict__)
        return self.__class__(*clones)

    @property
    def atoms(self):
        atoms = dict()
        for subfml in self.subs:
            for k, v in subfml.atoms.items():
                atoms[k] = atoms.get(k, []) + v
        return atoms

    @property
    def free_terms(self):
        free_terms = []
        for subfml in self.subs:
            free_terms += subfml.free_terms
        return free_terms

    def replace_term(self, replaced_term, replacing_term):
        # fml = copy(self)
        fml = self.clone()
        subs = []
        for subfml in deepcopy(self.subs):
            subs.append(subfml.replace_term(replaced_term, replacing_term))
        fml.subs = subs
        return fml

    def latex(self):
        return f" {self.connective_latex} ".join(
            map(
                lambda x: f"({x.latex()})" if isinstance(x, Binary) else f"{x.latex()}",
                self.subs,
            )
        )

    def __str__(self) -> str:
        # print(self.subs)
        # return f"{self.connective}".join(map(lambda x: f"({x})", self.subs))
        return f" {self.connective} ".join(
            map(
                lambda x: f"({x})" if isinstance(x, Binary) else f"{x}",
                self.subs,
            )
        )

    def __repr__(self) -> str:
        return "{}[{}]".format(
            self.signature, ", ".join(map(lambda x: repr(x), self.subs))
        )


class Conjunction(Binary):
    signature = "Conj"
    connective = "∧"
    connective_latex = r"\land"


class Disjunction(Binary):
    signature = "Disj"
    connective = "∨"
    connective_latex = r"\lor"


class Conditional(Binary):
    signature = "Cond"
    connective = "→"
    connective_latex = r"\to"


class Quantifier(Formula):
    def __init__(self, term, sub: Formula):
        self.variable = term
        self.sub = sub

    @property
    def atoms(self):
        return self.sub.atoms
        # atoms = []
        # for atom in self.sub.atoms:
        #     bounded_variables = atom.get("bounded_variables", []) + [self.variable]
        #     atoms.append(dict(atom, bounded_variables=bounded_variables))
        # return atoms

    @property
    def free_terms(self):
        return [term for term in self.sub.free_terms if term not in self.variable]

    def replace_term(self, replaced_term, replacing_term):
        return self.sub.replace_term(replaced_term, replacing_term)

    def clone(self):
        return Quantifier(copy(self.variable), self.sub.clone())

    def latex(self):
        return f"{self.connective_latex} {self.variable} " + (
            f"({self.sub.latex()})"
            if isinstance(self.sub, Binary)
            else f"{self.sub.latex()}"
        )

    def __str__(self) -> str:
        return f"{self.connective}{self.variable}" + (
            f"({self.sub})" if isinstance(self.sub, Binary) else f"{self.sub}"
        )

    def __repr__(self) -> str:
        return f"{self.signature}<{self.variable}>[{repr(self.sub)}]"


class Universal(Quantifier):
    signature = "Forall"
    connective = "∀"
    connective_latex = r"\forall"


class Particular(Quantifier):
    signature = "Exists"
    connective = "∃"
    connective_latex = r"\exists"
