Require Import Coq.Lists.List.

Require Import AttestationProtocolOrdering.attacktree.
Require Import AttestationProtocolOrdering.attacktree_adversary.
Require Import AttestationProtocolOrdering.attacktree_ordering.
Require Import AttestationProtocolOrdering.set_minimization.
Require Import AttestationProtocolOrdering.set_ordering.


Section ProtocolOrdering.
    Context {components : Type}.

    Inductive orderT : Type :=
    | equiv : orderT
    | leq : orderT
    | geq : orderT
    | incomparable : orderT.


    Definition order_fix (P Q : list (attacktree components)) : orderT :=
    if (equivDec P Q) then equiv else
    if (leqDec P Q)   then leq else
    if (leqDec Q P)   then geq else
                           incomparable.

End ProtocolOrdering.
