Require Export List. Export ListNotations.

(*
Fixpoint alternate (l1 l2 : list nat) : list nat :=
match l1, l2 with
[], _ => l2 | _, [] => l1 | h1 :: t1, h2 :: t2 =>
  h1 :: h2 :: alternate t1 t2
end.
*)


Fixpoint alternate (l1 l2 : list nat) : list nat :=
match l1, l2 with
[], _ => l2 | _, [] => l1 | h1 :: t1, h2 :: t2 =>
  h1 :: h2 :: alternate t1 t2
end.

Inductive alt : list nat -> list nat -> list nat -> Prop :=
| alt_nil : forall l, alt [] l l
| alt_step : forall a l t1 t2,
    alt l t1 t2 -> alt (a :: t1) l (a :: t2).

Lemma alt_alternate : 
  forall l1 l2 l3, alt l1 l2 l3 -> alternate l1 l2 = l3.
Proof.
induction l1; intros.
- inversion H. subst. simpl. reflexivity.
- destruct l2; simpl; inversion H; inversion H4; auto.
  apply IHl1 in H9. rewrite H9. reflexivity.
Qed.
