Require MSets NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations Omega.

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

Ltac check_not_in l x :=
match l with
| nil => idtac
| cons ?y ?l => try (constr_eq x y; fail 2 x y) ; check_not_in l x
end.

Ltac get T l f :=
match goal with
| [ x : T |- _ ] => check_not_in l x; get T (cons x l) f
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

Inductive term :=
| fvar : Var.t -> term
| bvar : nat -> term
| appl : term -> term -> term
| abst : term -> term
| comp : term -> term -> term
| refl : term.

Bind Scope trm_scope with term.
Delimit Scope trm_scope with term.

Notation "'λ' t" := (abst t) (at level 80, t at level 0, format "'λ'  t") : trm_scope.
Notation "t @ u" := (appl t u) (at level 20, left associativity) : trm_scope.

Fixpoint open (t : term) (n : nat) (r : term) :=
match t with
| fvar x => fvar x
| bvar m => if PeanoNat.Nat.eq_dec m n then r else bvar m
| appl t u => appl (open t n r) (open u n r)
| abst t => abst (open t (S n) r)
| comp t u => comp (open t n r) (open u n r)
| refl => refl
end.

Notation "t << u" := (open t 0 u) (at level 50, left associativity).

Inductive Term : term -> Type :=
| Term_fvar : forall x, Term (fvar x)
| Term_appl : forall t u, Term t -> Term u -> Term (appl t u)
| Term_abst : forall L t,
  (forall x, ~ VSet.In x L -> Term (t << fvar x)) ->
  Term (abst t)
| Term_comp : forall t u, Term t -> Term u -> Term (comp t u)
| Term_refl : Term refl
.

Hint Constructors Term.

Fixpoint subst (t : term) (x : Var.t) (r : term) :=
match t with
| fvar y => if Var.eq_dec x y then r else fvar y
| bvar m => bvar m
| appl t u => appl (subst t x r) (subst u x r)
| abst t => abst (subst t x r)
| comp t u => comp (subst t x r) (subst u x r)
| refl => refl
end.

Notation "[ t | x := r ]" := (subst t x r).

Fixpoint fv (t : term) : VSet.t :=
match t with
| fvar y => VSet.add y VSet.empty
| bvar m => VSet.empty
| appl t u => VSet.union (fv t) (fv u)
| abst t => fv t
| comp t u => VSet.union (fv t) (fv u)
| refl => VSet.empty
end.

Fixpoint close (t : term) (x : Var.t) (n : nat) :=
match t with
| fvar y => if Var.eq_dec x y then bvar n else fvar y
| bvar m => bvar m
| appl t u => appl (close t x n) (close u x n)
| abst t => abst (close t x (S n))
| comp t u => comp (close t x n) (close u x n)
| refl => refl
end.

Notation "λ[ x ] t" := (λ (close t x 0))%term (at level 80, t at level 0, format "λ[ x ] t") : trm_scope.

Ltac gather_ f :=
  get Var.t (@nil Var.t) ltac:(fun l =>
  get VSet.t (@nil VSet.t) ltac:(fun ls =>
  get term (@nil term) ltac:(fun lt =>
  let r0 := constr:(List.fold_left (fun accu s => VSet.union s accu) ls VSet.empty) in
  let r1 := constr:(List.fold_left (fun accu t => VSet.union (fv t) accu) lt r0) in
  let s := constr:(List.fold_left (fun accu x => VSet.add x accu) l r1) in
  f s))).

Ltac pick x :=
  gather_ ltac:(fun s =>
  pose (x := fresh s);
  cbn [List.fold_left] in x;
  let H := fresh in
  destruct x as [x H];
  simplify_vset_hyp H
  ).

Ltac gather L :=
  gather_ ltac:(fun s =>
  pose (L := s);
  cbn [fv List.fold_left] in L).

Inductive red : term -> term -> Prop :=
| red_beta : forall t u, red (appl (abst t) u) (t << u)
| red_appl_l : forall t u r, red t r -> red (appl t u) (appl r u)
| red_appl_r : forall t u r, red u r -> red (appl t u) (appl t r).

Lemma open_idem_core : forall t n1 n2 r1 r2, n1 <> n2 ->
  open t n1 r1 = open (open t n1 r1) n2 r2 -> t = open t n2 r2.
Proof.
induction t; intros n1 n2 r1 r2 Hn Hrw; cbn in *; try inversion Hrw; f_equal;
try solve [intuition eauto]; cbn in *.
repeat (destruct PeanoNat.Nat.eq_dec; cbn in *); first [omega|intuition].
Qed.

Lemma Term_open_idem : forall t n r,
  Term t -> open t n r = t.
Proof.
intros t n r Ht; revert n.
induction Ht; intros n; cbn in *; f_equal; intuition eauto.
pick x; erewrite <- (open_idem_core _ 0); [|omega|symmetry]; intuition eauto.
Qed.

Lemma open_subst_trans : forall t x r,
  ~ VSet.In x (fv t) -> [ t << fvar x | x := r ] = t << r.
Proof.
intros t; generalize 0.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
+ destruct Nat.eq_dec; cbn; [destruct eq_dec|]; intuition.
Qed.

Lemma Term_subst_distr : forall t u x r, Term r ->
  [ t << u | x := r ] = [t | x := r] << [u | x := r].
Proof.
intros t; generalize 0.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
  rewrite Term_open_idem; now intuition.
+ destruct Nat.eq_dec; cbn; intuition.
Qed.

Lemma Term_subst_idem : forall t x r, ~ VSet.In x (fv t) -> [ t | x := r ] = t.
Proof.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; intuition eauto.
Qed.

Lemma Term_subst_comm : forall t u x r, Term r -> ~ VSet.In x (fv u) ->
  [ t << u | x := r ] = [t | x := r] << u.
Proof.
intros.
rewrite <- (Term_subst_idem u x r) at 2; [|assumption].
apply Term_subst_distr; assumption.
Qed.

Lemma Term_subst_compat : forall t x r,
  Term t -> Term r -> Term [t | x := r].
Proof.
intros t x r Ht Hr; induction Ht; cbn; try solve [intuition eauto].
+ destruct eq_dec; subst; intuition.
+ gather L'; apply Term_abst with L'; intros; unfold L' in *.
  simplify_vset_hyps; rewrite <- Term_subst_comm; cbn in *; intuition eauto.
  simplify_vset_hyps; intuition eauto.
Qed.

Lemma close_open : forall t x, ~ VSet.In x (fv t) -> close (t << fvar x) x 0 = t.
Proof.
intros t; generalize 0.
induction t; intros; cbn in *; simplify_vset_hyps; f_equal; intuition eauto.
+ destruct eq_dec; cbn; intuition.
+ destruct Nat.eq_dec; cbn; intuition.
  destruct eq_dec; intuition eauto.
Qed.

Lemma close_fv : forall t x n, ~ VSet.In x (fv (close t x n)).
Proof.
induction t; intros; cbn in *; simplify_vset_hyps; simplify_vset_goal; intuition eauto.
destruct eq_dec; cbn in *; simplify_vset_hyps; intuition.
Qed.

(*
Lemma open_inj : forall L t u,
  (forall x, ~ VSet.In x L -> t << fvar x = u << fvar x) -> t = u.
Proof.
intros L t; revert L; generalize 0.
induction t; intros ? L u H; cbn in *;
pick x; (refine ((fun H => _) (H x _)); [|intuition]);
destruct u; cbn in H; repeat destruct Nat.eq_dec; cbn in *; simplify_vset_hyps; try intuition congruence.
f_equal; intuition eauto.*)

(*
Lemma open_close : forall t x, Term t -> (close t x 0) << (fvar x) = t.
Proof.
intros t x Ht; generalize 0.
induction Ht; intros; cbn in *; f_equal; intuition eauto.
+ destruct eq_dec; cbn; intuition.
  destruct Nat.eq_dec; intuition congruence.
+ pick y.

*)

Fixpoint forcing (σ : list Var.t) (ω : Var.t) t (Ht : Term t) {struct t} : term.
Proof.
refine (
match Ht in Term t return term with
| Term_fvar x => fvar x @ fvar ω @ (List.fold_left (fun accu x => comp (fvar x) accu) σ refl)
| Term_appl t u Ht Hu =>
  let (α, _) := fresh (List.fold_left (fun accu x => VSet.add x accu) (cons ω σ) (fv u)) in
  (forcing σ ω t Ht) @ λ[ω] λ[α] (forcing (cons α σ) ω u Hu)
| Term_abst L t Ht =>
  let (x, Hx) := fresh (List.fold_left (fun accu x => VSet.add x accu) (cons ω σ) L) in
  λ[x] (forcing σ ω (t << fvar x) (Ht x _))
| Term_comp t u Ht Hu => comp (forcing σ ω t Ht) (forcing σ ω u Hu)
| Term_refl => refl
end%term
).
Show Proof.
Defined.

match Ht with
| bvar n => bvar n @ fvar ω @ refl
| fvar x => fvar x
| appl t u => appl (forcing σ ω t) (λ[ω] λ (forcing (cons 0 σ) ω u))
| abst t => abst (forcing (List.map S σ) ω t)
| comp t u => comp (forcing σ ω t) (forcing σ ω u)
| refl => refl
end.

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
