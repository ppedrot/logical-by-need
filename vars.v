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
Module Export Fresh : FreshS(Var)(VSet).

Definition fresh : forall s : VSet.t, {v | ~ VSet.In v s}.
Proof.
intros s; destruct (Var.fresh (VSet.elements s)) as [x Hx].
exists x; intros Hi.
apply VSet.elements_spec1 in Hi.
apply SetoidList.InA_alt in Hi; destruct Hi as [y [Hrw Hi]]; subst; intuition.
Qed.

End Fresh.

Module Export VSetFacts := MSetFacts.WFactsOn(Var)(VSet).

Ltac check_not_in l x :=
match l with
| nil => idtac
| cons ?y ?l => try (constr_eq x y; fail 2 x y) ; check_not_in l x
end.

Ltac get T l f :=
match goal with
| [ x : ?T' |- _ ] => unify T T'; check_not_in l x; get T (cons x l) f
| _ => f l
end.

Ltac fold_not_hyp H :=
  let t := type of H in
  match t with context [?P -> False] => fold (not P) in H end.

Ltac fold_not_goal :=
  match goal with |- context [?P -> False] => fold (not P) end.

Ltac simplify_vset_one_hyp H :=
match type of H with
| context [VSet.In ?x (VSet.union ?p ?q)] =>
  rewrite VSet.union_spec in H
| context [VSet.In ?x (VSet.add ?p ?q)] =>
  rewrite VSet.add_spec in H
| context [VSet.In ?x VSet.empty] =>
  rewrite VSetFacts.empty_iff in H
end.

Ltac simplify_vset_one_goal :=
match goal with
| |- context [VSet.In ?x (VSet.union ?p ?q)] =>
  rewrite VSet.union_spec
| |- context [VSet.In ?x (VSet.add ?p ?q)] =>
  rewrite VSet.add_spec
| |- context [VSet.In ?x VSet.empty] =>
  rewrite VSetFacts.empty_iff
end.

Ltac simplify_vset_hyp H :=
  repeat simplify_vset_one_hyp H; 
  unfold not in H;
  repeat rewrite Decidable.not_or_iff in H;
  repeat (fold_not_hyp H).

Ltac simplify_vset_goal :=
  repeat simplify_vset_one_goal;
  unfold not;
  repeat rewrite Decidable.not_or_iff;
  repeat fold_not_goal.

Ltac simplify_vset_hyps :=
  repeat match goal with [ H : ?P |- _ ] => progress (simplify_vset_hyp H) end.

Ltac simplify_vset := simplify_vset_hyps; simplify_vset_goal.
