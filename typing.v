Require lambda.

Module Spec
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var))
  (Import Fresh : lambda.Fresh(Var)(VSet))
.

Module Import Lambda := lambda.Spec(Var)(VSet)(Fresh).

Inductive type :=
| arrow : type -> type
| prod : type -> type
| le : Var.t -> Var.t -> type.

Definition env := list (Var.t * type).

Inductive typing : env -> term -> type -> Prop :=.

End Spec.
