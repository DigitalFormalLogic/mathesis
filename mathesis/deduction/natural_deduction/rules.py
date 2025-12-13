from copy import deepcopy
from itertools import count
from typing import Literal

from mathesis import forms
from mathesis.deduction.natural_deduction.natural_deduction import NDSubproof
from mathesis.deduction.sequent_calculus import Sequent, SequentItem
from mathesis.deduction.tableau import sign


def _apply(target, new_items, counter, preserve_target=True):
    """Add new items to a sequent, cloning existing items as needed."""

    branch_items = new_items

    for item in target.sequent.items:
        if item != target or preserve_target:
            if not hasattr(item, "subproof"):
                item.subproof = NDSubproof(item)
            node = item.clone()
            node.subproof = item.subproof
            node.n = next(counter)
            if item == target:
                pass
            branch_items.append(node)

    branch_sequent = Sequent([], [], parent=target.sequent)
    branch_sequent.items = branch_items

    # NOTE: Connect the subproofs
    branch_sequent.right[0].subproof = target.sequent.right[0].subproof

    target_new = deepcopy(target)
    target_new.sequent = branch_sequent

    if preserve_target:
        return branch_sequent, target_new
    else:
        return branch_sequent


def _instantiate_quantifier_body(quantifier, replacing_term: str):
    subfml = quantifier.sub.clone()
    subfml = subfml.replace_term(quantifier.variable, replacing_term)
    return subfml


def _collect_branch_terms(sequent):
    terms = set()
    current = sequent
    while current is not None:
        for item in current.items:
            terms.update(item.fml.free_terms)
        current = current.parent
    return terms


def _ensure_fresh_term(term: str, sequent):
    branch_terms = _collect_branch_terms(sequent)
    assert term not in branch_terms, "The chosen term already appears in this branch"


class Rule:
    label: str
    latex_label: str

    def __str__(self):
        return self.label

    def latex(self):
        return self.latex_label


class IntroductionRule(Rule):
    pass


class EliminationRule(Rule):
    pass


class EFQ(Rule):
    label = "EFQ"
    latex_label = "EFQ"

    def __init__(self, intro: SequentItem):
        self.intro = intro

    def apply(self, target: SequentItem, counter=count(1)):
        assert target.sign == sign.POSITIVE, "Invalid application"
        # TODO: Fix this
        assert str(target.fml) == "⊥", "Not an atom"

        target.sequent.derived_by = self
        target.subproof.derived_by = self

        item = SequentItem(
            self.intro.fml,
            sign=sign.POSITIVE,
            n=next(counter),
        )
        sq, _target = _apply(target, [item], counter)

        # Subproof
        item.subproof = NDSubproof(
            item,
            parent=target.sequent.right[0].subproof,
            children=[target.subproof],
        )
        # target.subproof = Node(target, children=[item.subproof])
        # _target.sequent.right[0].subproof = target.sequent.right[0].subproof
        sq.right[0].subproof = target.sequent.right[0].subproof

        if sq.tautology():
            target.sequent.right[0].subproof.children = item.subproof.children

        return {
            "queue_items": [sq],
            "counter": counter,
        }


class Negation:
    # Intro = signed_rules.NegativeNegationRule
    class Intro(IntroductionRule):
        label = "¬I"
        latex_label = r"$\neg$I"

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Cannot apply introduction rule"
            assert isinstance(target.fml, forms.Negation), "Not a negation"
            subfml = target.fml.sub

            if target.sequent:
                target.sequent.derived_by = self

            target.subproof.derived_by = self

            # TODO: Fix this
            falsum = forms.Atom("⊥", latex=r"\bot")

            antec = SequentItem(subfml, sign=sign.POSITIVE, n=next(counter))
            conseq = SequentItem(
                falsum,
                sign=sign.NEGATIVE,
                n=next(counter),
            )
            sq = _apply(target, [antec, conseq], counter, preserve_target=False)

            # Attach a subproof to the consequent (falsum)
            conseq.subproof = NDSubproof(
                conseq,
                children=[],
            )
            target.sequent.right[0].subproof.children = [conseq.subproof]
            antec.subproof = NDSubproof(
                antec,
                parent=conseq.subproof,
                children=[],
            )

            return {
                "queue_items": [sq],
                "counter": counter,
            }

    class Elim(EliminationRule):
        label = "¬E"
        latex_label = r"$\neg$E"

        def __init__(self):
            pass

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(target.fml, forms.Negation), "Not a negation"

            target.sequent.derived_by = self

            # # NOTE: Negation elimination requires a falsum in right
            # falsum = next(
            #     filter(lambda x: str(x.fml) == "⊥", target.sequent.right),
            #     None,
            # )
            # assert falsum, "`⊥` must be in conclusions"

            # NOTE: If you want to eliminate negation, you need to have its subformula
            subfml = target.fml.sub

            # Find on the left side
            nonneg_item = next(
                filter(
                    lambda x: str(x.fml) == str(subfml),
                    target.sequent.left,
                ),
                None,
            )
            assert nonneg_item, "Subformula must be in premises"
            nonneg_item = nonneg_item.clone()

            falsum = forms.Atom("⊥", latex=r"\bot")
            falsum_item = SequentItem(
                falsum,
                sign=sign.POSITIVE,
                n=next(counter),
            )

            # Look up falsum on the right side
            falsum_right = next(
                filter(lambda x: str(x.fml) == "⊥", target.sequent.right),
                None,
            )

            if falsum_right is not None:
                falsum_item.subproof = falsum_right.subproof
                falsum_item.subproof.children = [
                    deepcopy(nonneg_item.subproof),
                    deepcopy(target.subproof),
                ]
            else:
                falsum_item.subproof = NDSubproof(
                    falsum_item,
                    children=[
                        deepcopy(nonneg_item.subproof),
                        deepcopy(target.subproof),
                    ],
                    parent=target.sequent.right[0].subproof,
                )

            falsum_item.subproof.derived_by = self

            # subfml = SequentItem(subfml, sign=sign.NEGATIVE, n=next(counter))
            sequent, _target = _apply(target, [falsum_item], counter)

            return {
                "queue_items": [sequent],
                "counter": counter,
            }


class Conjunction:
    # Intro = signed_rules.NegativeConjunctionRule
    # class Intro(signed_rules.NegativeConjunctionRule, IntroductionRule):
    #     pass

    class Intro(IntroductionRule):
        label = "∧I"
        latex_label = r"$\land$I"

        def __init__(self):
            pass

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Cannot apply introduction rule"
            assert isinstance(target.fml, forms.Conjunction), "Not a conjunction"

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            branches = []

            for conj in target.fml.subs:
                conj = SequentItem(conj, sign=sign.NEGATIVE, n=next(counter))
                sequent = _apply(target, [conj], counter, preserve_target=False)
                branches.append(sequent)

            # Subproof
            for branch in branches:
                for item in branch.left:
                    if getattr(item, "subproof", None) is None:
                        item.subproof = NDSubproof(item)

                branch.right[0].subproof = NDSubproof(branch.right[0])
                branch.right[0].subproof.children = [
                    deepcopy(item.subproof) for item in branch.left
                ]

                if branch.tautology():
                    left_item = next(
                        filter(
                            lambda x: str(x.fml) == str(branch.right[0]), branch.left
                        ),
                        None,
                    )
                    branch.right[0].subproof.children = left_item.subproof.children

            target.sequent.right[0].subproof.children = [
                branch.right[0].subproof for branch in branches
            ]

            return {
                "queue_items": branches,
                "counter": counter,
            }

    # TODO: Choice of conjunct
    # Elim = signed_rules.PositiveConjunctionRule
    class Elim(EliminationRule):
        label = "∧E"
        latex_label = r"$\land$E"

        def __init__(self, conjunct: Literal["left", "right"]):
            self.conjunct = conjunct

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(target.fml, forms.Conjunction), "Not a conjunction"

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            conj1, conj2 = target.fml.subs
            if self.conjunct == "left":
                item = SequentItem(conj1, sign=sign.POSITIVE, n=next(counter))
            elif self.conjunct == "right":
                item = SequentItem(conj2, sign=sign.POSITIVE, n=next(counter))

            # Attach a new subproof node
            item.subproof = NDSubproof(
                item,
                children=[deepcopy(target.subproof)],
                parent=target.sequent.right[0].subproof,
            )

            sq1, target = _apply(target, [item], counter)
            # sq2 = Sequent([target], [item], parent=target.sequent)

            return {
                "queue_items": [sq1],
                "counter": counter,
            }


class Disjunction:
    # Intro = signed_rules.NegativeDisjunctionRule
    class Intro(IntroductionRule):
        label = "∨I"
        latex_label = r"$\lor$I"

        def __init__(self, disjunct: Literal["left", "right"]):
            self.disjunct = disjunct

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Sign is not negative"
            assert isinstance(target.fml, forms.Disjunction), "Not a disjunction"

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            disj1, disj2 = target.fml.subs

            if self.disjunct == "left":
                disjunct_item = SequentItem(disj1, sign=sign.NEGATIVE, n=next(counter))
            elif self.disjunct == "right":
                disjunct_item = SequentItem(disj2, sign=sign.NEGATIVE, n=next(counter))
            else:
                raise ValueError("Invalid disjunct")

            sq = _apply(target, [disjunct_item], counter, preserve_target=False)

            # Subproof
            disjunct_item.subproof = NDSubproof(
                disjunct_item,
                children=[deepcopy(left_item.subproof) for left_item in sq.left],
            )

            target.subproof.children = [deepcopy(disjunct_item.subproof)]

            if sq.tautology():
                left_item = next(
                    filter(lambda x: str(x.fml) == str(disjunct_item.fml), sq.left),
                    None,
                )
                target.subproof.children = [deepcopy(left_item.subproof)]

            return {
                "queue_items": [sq],
                "counter": counter,
            }

    # Elim = signed_rules.PositiveDisjunctionRule
    class Elim(EliminationRule):
        label = "∨E"
        latex_label = r"$\lor$E"

        def __init__(self):
            pass

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(target.fml, forms.Disjunction), "Not a disjunction"

            target.sequent.derived_by = self
            target.sequent.right[0].subproof.derived_by = self

            branches = []
            items = []

            for disj in target.fml.subs:
                disj = SequentItem(disj, sign=sign.POSITIVE, n=next(counter))
                disj.subproof = NDSubproof(
                    disj,
                    children=[],
                    parent=None,
                )
                disj.subproof.hyp = True
                items.append(disj)

            for item in items:
                sequent, _target = _apply(target, [item], counter)

                # for left_item in branch.left:
                #     if getattr(left_item, "subproof", None) is None:
                #         left_item.subproof = NDSubproof(left_item)

                sequent.right[0].subproof = NDSubproof(
                    sequent.right[0],
                    parent=target.sequent.right[0].subproof,
                    children=[],
                )

                branches.append(sequent)

            target.sequent.right[0].subproof.children = [
                branch.right[0].subproof for branch in branches
            ] + [target.subproof]

            return {
                "queue_items": branches,
                "counter": counter,
            }


class Conditional:
    # class Intro(signed_rules.NegativeConditionalRule, IntroductionRule):
    #     pass
    class Intro(IntroductionRule):
        label = "→I"
        latex_label = r"$\to$I"

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Cannot apply introduction rule"
            assert isinstance(target.fml, forms.Conditional), "Not a conditional"

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            antec, conseq = target.fml.subs

            antec = SequentItem(antec, sign=sign.POSITIVE, n=next(counter))
            conseq = SequentItem(
                conseq,
                sign=sign.NEGATIVE,
                n=next(counter),
            )

            sq = _apply(target, [antec, conseq], counter, preserve_target=False)

            conseq.subproof = NDSubproof(
                conseq,
                parent=target.subproof,
            )
            antec.subproof = NDSubproof(
                antec,
                # parent=conseq.subproof,
            )
            antec.subproof.hyp = True

            if sq.tautology():
                left_item = next(
                    filter(
                        lambda x: str(x.fml) == str(conseq.fml),
                        sq.left,
                    ),
                    None,
                )
                # target.sequent.right[0].subproof.children = left_item.subproof.children
                left_item.subproof.parent = target.sequent.right[0].subproof
                conseq.subproof.parent = None

            return {
                "queue_items": [sq],
                "counter": counter,
            }

    class Elim(EliminationRule):
        label = "→E"
        latex_label = r"$\to$E"

        def __init__(self):
            pass

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(target.fml, forms.Conditional), "Not a conditional"

            target.sequent.derived_by = self

            antec, conseq = target.fml.subs

            antec = SequentItem(antec, sign=sign.NEGATIVE, n=next(counter))

            # antec.subproof = NDSubproof(
            #     antec,
            #     children=[],
            #     parent=target.sequent.right[0].subproof,
            # )

            # sq1, target_new = _apply(target.sequent.right[0], [], counter)
            sq1, _target = _apply(target, [antec], counter)

            conseq = SequentItem(conseq, sign=sign.POSITIVE, n=next(counter))

            # Limit to single conclusion = antecedent
            sq1.items = [
                item
                for item in sq1.items
                if item.sign == sign.POSITIVE or item == antec
            ]

            # Attach a new subproof node
            target.subproof.parent = None
            conseq.subproof = NDSubproof(
                conseq,
                children=[deepcopy(target.subproof)],
                parent=target.sequent.right[0].subproof,
            )
            conseq.subproof.derived_by = self

            # Invalidate if conseq does not target.sequent.right[0]
            # if str(conseq.fml) != str(target.sequent.right[0].fml):
            #     raise AssertionError("Consequent does not match target sequent conclusion")

            # target.subproof.parent = conseq.subproof

            antec.subproof = NDSubproof(
                antec,
                children=[],
                parent=None,
            )

            for item in sq1.items:
                if item.sign == sign.POSITIVE and item.fml == antec.fml:
                    antec.subproof = item.subproof
                    break

            antec.subproof.parent = conseq.subproof

            sq2, _target_conseq = _apply(target, [conseq], counter)

            if sq2.tautology():
                target.sequent.right[0].subproof.children = conseq.subproof.children
                target.sequent.right[0].subproof.derived_by = self
                conseq.subproof.parent = None

            branches = [sq1, sq2]

            return {
                "queue_items": branches,
                "counter": counter,
            }


class Universal:
    class Intro(IntroductionRule):
        label = "∀I"
        latex_label = r"$\forall$I"

        def __init__(self, generalizing_term: str):
            self.generalizing_term = generalizing_term

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Cannot apply introduction rule"
            assert isinstance(target.fml, forms.Universal), "Not a universal formula"

            _ensure_fresh_term(self.generalizing_term, target.sequent)

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            instantiated = _instantiate_quantifier_body(
                target.fml, self.generalizing_term
            )
            instantiated_item = SequentItem(
                instantiated,
                sign=sign.NEGATIVE,
                n=next(counter),
            )

            sequent = _apply(
                target, [instantiated_item], counter, preserve_target=False
            )

            instantiated_item.subproof = NDSubproof(
                instantiated_item,
                children=[],
                parent=target.subproof,
            )

            return {
                "queue_items": [sequent],
                "counter": counter,
            }

    class Elim(EliminationRule):
        label = "∀E"
        latex_label = r"$\forall$E"

        def __init__(self, replacing_term: str):
            self.replacing_term = replacing_term

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(target.fml, forms.Universal), "Not a universal formula"

            target.sequent.derived_by = self
            # target.subproof.derived_by = self

            instantiated = _instantiate_quantifier_body(target.fml, self.replacing_term)
            instantiated_item = SequentItem(
                instantiated,
                sign=sign.POSITIVE,
                n=next(counter),
            )

            sequent, target = _apply(target, [instantiated_item], counter)

            instantiated_item.subproof = NDSubproof(
                instantiated_item,
                children=[target.subproof],
                parent=target.sequent.right[0].subproof,
            )
            instantiated_item.subproof.derived_by = self

            return {
                "queue_items": [sequent],
                "counter": counter,
            }


class Particular:
    class Intro(IntroductionRule):
        label = "∃I"
        latex_label = r"$\exists$I"

        def __init__(self, witness_term: str):
            self.witness_term = witness_term

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.NEGATIVE, "Cannot apply introduction rule"
            assert isinstance(
                target.fml, forms.Particular
            ), "Not an existential formula"

            target.sequent.derived_by = self
            target.subproof.derived_by = self

            instantiated = _instantiate_quantifier_body(target.fml, self.witness_term)
            instantiated_item = SequentItem(
                instantiated,
                sign=sign.NEGATIVE,
                n=next(counter),
            )
            instantiated_item.subproof = NDSubproof(
                instantiated_item,
                children=target.subproof.children,
                parent=target.subproof,
            )

            sequent = _apply(
                target, [instantiated_item], counter, preserve_target=False
            )

            if sequent.tautology():
                left_item = next(
                    filter(
                        lambda x: str(x.fml) == str(instantiated_item.fml),
                        sequent.left,
                    ),
                    None,
                )
                if left_item is not None:
                    # instantiated_item.subproof.parent = None
                    target.subproof.children = [left_item.subproof]

            return {
                "queue_items": [sequent],
                "counter": counter,
            }

    class Elim(EliminationRule):
        label = "∃E"
        latex_label = r"$\exists$E"

        def __init__(self, generalizing_term: str):
            self.generalizing_term = generalizing_term

        def apply(self, target: SequentItem, counter=count(1)):
            assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
            assert isinstance(
                target.fml, forms.Particular
            ), "Not an existential formula"

            _ensure_fresh_term(self.generalizing_term, target.sequent)

            target.sequent.derived_by = self
            target.sequent.right[0].subproof.derived_by = self

            instantiated = _instantiate_quantifier_body(
                target.fml, self.generalizing_term
            )
            instantiated_item = SequentItem(
                instantiated,
                sign=sign.POSITIVE,
                n=next(counter),
            )
            instantiated_item.subproof = NDSubproof(
                instantiated_item,
            )
            instantiated_item.subproof.hyp = True

            target.subproof.parent = target.sequent.right[0].subproof

            sq, target = _apply(target, [instantiated_item], counter)

            sq.right[0].subproof = NDSubproof(
                sq.right[0],
                parent=target.sequent.right[0].subproof,
                children=[],
            )

            return {
                "queue_items": [sq],
                "counter": counter,
            }
