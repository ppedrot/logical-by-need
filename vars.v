Require MSets.
Require Import Omega.

Module Type FreshListS (Var : Orders.UsualOrderedType).
Parameter fresh : forall s : list Var.t, {v | ~ List.In v s}.
End FreshListS.

Module Type FreshS (Var : Orders.UsualOrderedType)(VSet : MSetInterface.SetsOn(Var)).
Parameter fresh : forall s : VSet.t, {v | ~ VSet.In v s}.
End FreshS.

Module Type VarS := Orders.UsualOrderedType <+ FreshListS.

Module Var : VarS.
Include Coq.Arith.PeanoNat.Nat.

Definition fresh : forall s : list Var.t, {v | ~ List.In v s}.
Proof.
intros l; pose (e := (List.fold_right Nat.max 0 l)).
assert (H : List.Forall (fun x => x <= e) l).
{ induction l; cbn in *; constructor; [apply Nat.le_max_l|].
  eapply List.Forall_impl; [|eassumption].
  cbn; intros; etransitivity; [eassumption|apply Nat.le_max_r]. }
exists (S e); intros He.
eapply List.Forall_forall in He; [|eassumption].
cbn in He; omega.
Qed.

End Var.

Module VSet : MSetInterface.SetsOn(Var) := MSetAVL.Make(Var).
Declare Module Export Fresh : FreshS(Var)(VSet).

Module Export VSetFacts := MSetFacts.WFactsOn(Var)(VSet).
