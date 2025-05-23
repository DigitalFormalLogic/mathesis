# Formulas and Grammars

## Parsing formulas

In Mathesis, formulas are represented as objects.
Formulas are parsed from strings using grammars (languages, syntax).
`mathesis.grammars.BasicGrammar` is a basic grammar with a standard set of symbols for propositional and quantified logic:

- `¬` for negation, `∧` for conjunction, `∨` for disjunction, `→` for conditional.
- `⊤` for top (True) and `⊥` for bottom (False).
- `∀` for universal quantifier and `∃` for existential quantifier.
- Arbitrary symbols are allowed for atomic formulas.

For example, `¬(A→C)` is parsed as a negation of a conditional of two atomic formulas `A` and `C`.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar

grammar = BasicGrammar()

fml = grammar.parse("¬(A→C)")

print(fml, repr(fml))
```

The `symbols` option allows you to customize some symbols used in the grammar.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar

grammar = BasicGrammar(symbols={"conditional": "⊃"})

fml = grammar.parse("¬(A⊃C)")

print(fml, repr(fml))
```

It accepts a list of formulas as well.

```python exec="1" result="text" source="material-block"
from mathesis.grammars import BasicGrammar

grammar = BasicGrammar()

fmls = grammar.parse(["¬(A→C)", "B∨¬B", "(((A∧B)))"])

print([str(fml) for fml in fmls], repr(fmls))
```

## Advanced

### Constructing formula objects directly

`mathesis.forms.Formula` is the base class for all formulas.

```python exec="1" result="text" source="material-block"
from mathesis.forms import Negation, Conjunction, Disjunction, Conditional, Atom

fml = Negation(Conditional(Atom("A"), Atom("C")))

print(fml, repr(fml))
```

New connectives can be defined by subclassing `Formula`.

### Custom grammars

While there is no restriction in the way that a formula string is translated into a formula object, by default Mathesis uses <a href="https://github.com/lark-parser/lark" target="_blank">`lark`</a> for parsing.
Using lark, you can define arbitrary grammars in EBNF (Extended Backus-Naur Form) notation.
For example, here is a simple grammar for first-order classical logic:

```python
from mathesis.grammars import Grammar

class MyGrammar(Grammar):
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
conditional : fml "→" fml
universal : "∀" TERM fml
particular : "∃" TERM fml

%import common.WS
%ignore WS
""".lstrip()
```
