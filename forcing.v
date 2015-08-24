Require FSets FMaps NArith Wellfounded.
Require Import Program Setoid Morphisms BinNat Relations.

Module Type Fresh
  (Var : OrderedType.OrderedType)
  (VSet : FSetInterface.Sfun(Var)).

Parameter fresh : forall s : VSet.t, {v | ~ VSet.In v s}.

End Fresh.


Module Spec
  (Var : OrderedType.OrderedType)
  (VSet : FSetInterface.Sfun(Var))
  (Import Fresh : Fresh(Var)(VSet))
.

Module Import USetFacts := FSetFacts.WFacts_fun(Var)(VSet).

Inductive term :=
| fvar : Var.t -> term
| bvar : nat -> term
| appl : term -> term -> term
| abst : term -> term.

Fixpoint open (t : term) (n : nat) (r : term) :=
match t with
| fvar x => fvar x
| bvar m => if Nat.eqb m n then r else bvar m
| appl t u => appl (open t n r) (open u n r)
| abst t => abst (open t (S n) r)
end.

Inductive Term : term -> Prop :=
| Term_fvar : forall x, Term (fvar x)
| Term_appl : forall t u, Term t -> Term u -> Term (appl t u)
| Term_abst : forall L t,
  (forall x, ~ VSet.In x L -> Term (open t 0 (fvar x))) ->
  Term (abst t)
.







