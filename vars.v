Require MSets.

Module Type FreshS
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var)).

Parameter fresh : forall s : VSet.t, {v | ~ VSet.In v s}.

End FreshS.

Module Var : Orders.UsualOrderedType := Coq.Arith.PeanoNat.Nat.
Declare Module VSet : MSetInterface.SetsOn(Var).
Declare Module Export Fresh : FreshS(Var)(VSet).

Module Export VSetFacts := MSetFacts.WFactsOn(Var)(VSet).
