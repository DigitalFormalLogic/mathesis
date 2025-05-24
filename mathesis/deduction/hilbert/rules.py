from copy import deepcopy
from itertools import count

from anytree import Node

from mathesis import forms
from mathesis.deduction.sequent_calculus.rules import Rule, SequentItem, _apply, sign

# from mathesis.deduction.natural_deduction.rules import _apply


class ModusPonens(Rule):
    def apply(self, target, counter=count(1)):
        assert target.sign == sign.POSITIVE, "Cannot apply elimination rule"
        assert isinstance(target.fml, forms.Conditional), "Not a conditional"
        antec, conseq = target.fml.subs

        antec = next(
            filter(lambda x: x.fml == antec, target.sequent.left),
            None,
        )
        assert antec, "Antecendent does not match"

        # conclusion = str(target.sequent.right[0].fml)
        # print(conclusion)
        # assert str(conseq) == conclusion, "Consequent does not match"

        conseq = SequentItem(conseq, sign=sign.POSITIVE, n=next(counter))
        sequent = _apply(target, [conseq], counter)

        # # Subproof
        # conseq.subproof = Node(
        #     conseq,
        #     children=[
        #         deepcopy(antec.subproof),
        #         deepcopy(target.subproof),
        #     ],
        #     parent=target.sequent.right[0].subproof,
        # )
        # # target.sequent.right[0].subproof = sequent.right[0].subproof
        # sequent.right[0].subproof = target.sequent.right[0].subproof

        # if sequent.tautology():
        #     target.sequent.right[0].subproof.children = conseq.subproof.children

        return {
            "queue_items": [sequent],
            "counter": counter,
        }
