Require MSets.
Require Import Omega.
Require lambda.

Module Type Fresh
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var)).

Parameter fresh : forall s : VSet.t, {v | ~ VSet.In v s}.

End Fresh.


Module Spec
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var))
  (Import Fresh : Fresh(Var)(VSet))
.

Module Import VSetFacts := MSetFacts.WFactsOn(Var)(VSet).
Module Import Lambda := lambda.Spec(Var)(VSet)(Fresh).

Fixpoint comps (σ : list Var.t) : term :=
match σ with
| nil => refl
| cons x σ => comp (fvar x) (comps σ)
end.

Fixpoint forcing (σ : list Var.t) (ω : Var.t) t (Ht : STerm t) {struct Ht} : term.
Proof.
refine (
match Ht in STerm t return term with
| STerm_fvar x => fvar x @ fvar ω @ comps σ
| STerm_appl t u Ht Hu =>
  let (α, _) := fresh (VSet.union (fv u) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  (forcing σ ω t Ht) @ λ[ω] λ[α] (forcing (cons α σ) ω u Hu)
| STerm_abst t Ht =>
  let (x, Hx) := fresh (VSet.union (fv t) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))) in
  λ[x] (forcing σ ω _ (Ht x _))
| STerm_comp t u Ht Hu => comp (forcing σ ω t Ht) (forcing σ ω u Hu)
| STerm_refl => refl
end%term
).
clear - Hx; abstract (simplify_vset_hyps; intuition eauto).
Defined.

Lemma Term_forcing : forall σ ω t Ht, Term (forcing σ ω t Ht).
Proof.
intros σ ω t Ht; revert σ ω; induction Ht; intros σ ω; cbn in *; intuition eauto.
+ repeat constructor; induction σ; cbn; intuition eauto.
+ destruct fresh as [α Hα].
  repeat constructor; intuition eauto.
  eapply (Term_close (λ[α] (forcing (cons α σ) ω u _)) ω), Term_close; auto.
+ destruct fresh as [x Hx].
  apply Term_close; intuition.
Qed.

Local Ltac dTerm π :=
refine (match π with
| Term_fvar x => _
| Term_appl t u πt2 πu2 => _
| Term_abst L t πt2 => _
| Term_comp t u πt2 πu2 => _
| Term_refl => _
end); unfold IDProp; trivial.

Local Ltac pop := match goal with [ H : ?P |- _ ] => revert H end.

(*
Lemma forcing_irrelevant : forall σ ω t π1 π2,
  forcing σ ω t π1 = forcing σ ω t π2.
Proof.
intros σ ω t π1; revert σ ω.
induction π1; intros σ ω π2; cbn in *.
+ dTerm π2.
+ move π2 before u; do 6 pop; dTerm π2; cbn.
  intros; destruct fresh; cbn.
  erewrite IHπ1_1, IHπ1_2; reflexivity.
+ move π2 before t; do 4 pop; dTerm π2; cbn.
  intros; repeat destruct fresh; cbn; f_equal.
  erewrite close_subst.
  simplify_vset_hyps.
  erewrite H.
  

*)


(*
Lemma forcing_fv : forall σ ω t Ht x, VSet.In x (fv (forcing σ ω t Ht)) ->
  VSet.In x (VSet.union (fv t) (VSet.add ω (List.fold_right VSet.add VSet.empty σ))).
Proof.
intros σ ω t Ht; revert σ ω.
induction Ht; intros σ ω y Hy; cbn in *; simplify_vset_hyps; simplify_vset_goal; intuition eauto.
+ right; right; induction σ; cbn in *; simplify_vset_hyps; simplify_vset; intuition eauto.
+ destruct fresh as [α Hα]; cbn in *; simplify_vset; destruct Hy as [Hy|Hy].
  - refine ((fun IH => _) (IHHt1 _ _ _ Hy)); clear - IH.
    simplify_vset; tauto.
  -
    do 2 (apply close_fv in Hy; destruct Hy as [? Hy]).
    refine ((fun IH => _) (IHHt2 _ _ _ Hy)).
    cbn in IH; simplify_vset; tauto.
+ destruct fresh as [x Hx]; cbn in *; simplify_vset.
  apply close_fv in Hy; destruct Hy as [? Hy].
  

(* Definition lift1 x α t := subst t x (λ λ (fvar x @ bvar 1 @ (comp (bvar 0) α))). *)

(* Fixpoint lift σ α t {struct t} := VSet.fold (fun x t => lift1 x α t) σ t. *)

Fixpoint forcing (σ : list nat) (ω : Var.t) t {struct t} : term :=
match t with
| bvar n => bvar n @ fvar ω @ refl
| fvar x => fvar x
| appl t u => appl (forcing σ ω t) (λ[ω] λ (forcing (cons 0 σ) ω u))
| abst t => abst (forcing (List.map S σ) ω t)
| comp t u => comp (forcing σ ω t) (forcing σ ω u)
| refl => refl
end.

Definition is_pure t := match t with
| refl | comp _ _ => False
| _ => True
end.

Lemma forcing_fv
*)

End Spec.
