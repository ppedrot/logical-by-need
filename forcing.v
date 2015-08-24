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

Inductive Term : term -> Prop :=
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

Fixpoint close (t : term) (x : Var.t) (n : nat) :=
match t with
| fvar y => if Var.eq_dec x y then bvar n else fvar y
| bvar m => bvar m
| appl t u => appl (close t x n) (close u x n)
| abst t => abst (close t x (S n))
| comp t u => comp (close t x n) (close u x n)
| refl => refl
end.

Inductive red : term -> term -> Prop :=
| red_beta : forall t u, red (appl (abst t) u) (t << u)
| red_appl_l : forall t u r, red t r -> red (appl t u) (appl r u)
| red_appl_r : forall t u r, red u r -> red (appl t u) (appl t r).

Ltac check_not_in l x :=
match l with
| nil => idtac
| cons ?y ?l => try (constr_eq x y; fail 2) ; check_not_in l x
end.

Ltac get T l f :=
match goal with
| [ x : T |- _ ] => check_not_in l x; get T (cons x l) f
| _ => f l
end.

Ltac fold_not H :=
  let t := type of H in
  match t with context [?P -> False] => fold (not P) in H end.

Ltac pick x :=
  get Var.t (@nil Var.t) ltac:(fun l =>
  get VSet.t (@nil VSet.t) ltac:(fun ls =>
  let r0 := constr:(List.fold_left (fun accu s => VSet.union s accu) ls VSet.empty) in
  let s := constr:(List.fold_left (fun accu x => VSet.add x accu) l r0) in
  pose (x := fresh s);
  cbn [List.fold_left] in x;
  let H := fresh in
  destruct x as [x H];
  repeat rewrite VSet.add_spec in H;
  repeat rewrite VSet.union_spec in H;
  repeat rewrite empty_iff in H;
  unfold not in H;
  repeat rewrite Decidable.not_or_iff in H;
  repeat (fold_not H)
  )).

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

Lemma Term_subst_compat : forall t x r,
  Term t -> Term r -> Term [t | x := r].
Proof.
intros t x r Ht Hr; induction Ht; cbn; try solve [intuition eauto].
+ destruct eq_dec; subst; intuition.
+ apply Term_abst with L; intros.
  


 econstructor. (VSet.add x L).


Definition lift1 x α t := subst t x (λ λ (fvar x @ bvar 1 @ (comp (bvar 0) α))).

Fixpoint lift σ α t {struct t} := VSet.fold (fun x t => lift1 x α t) σ t.

Fixpoint forcing (σ : VSet.t) ω t {struct t} : term :=
match t with
| bvar n => bvar n
| fvar x => fvar x @ fvar ω @ refl
| appl t u => appl (forcing σ ω t) (λ λ u)
| abst t => t
| _ => t
end.

