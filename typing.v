Require lambda.

Module Spec
  (Var : Orders.UsualOrderedType)
  (VSet : MSetInterface.SetsOn(Var))
  (Import Fresh : lambda.Fresh(Var)(VSet))
.

Module Import Lambda := lambda.Spec(Var)(VSet)(Fresh).

Inductive type :=
| arrow : type -> type -> type
| prod : type -> type -> type
| quant : type -> type
| le : term -> term -> type.

Definition env := list (Var.t * type).

Inductive typing : env -> term -> type -> Prop :=.

End Spec.
