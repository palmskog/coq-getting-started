Require Export List. Export ListNotations.

Fixpoint alternate l1 l2 : list nat :=
match l1 with
| [] => l2
| h1 :: t1 =>
  match l2 with
  | [] => h1 :: t1
  | h2 :: t2 => h1 :: h2 :: alternate t1 t2
  end
end.

(*
Fixpoint alternate (l1 l2 : list nat) : list nat :=
match l1, l2 with
| [], _ => l2
| _, [] => l1
| h1 :: t1, h2 :: t2 => h1 :: h2 :: alternate t1 t2
end.
*)

(*
Fixpoint alternate l1 l2 : list nat :=
match l1 with
| [] => l2
| h :: t1 => h :: alternate l2 t1
end.
*)

Eval compute in alternate [] [1; 2].
Eval compute in alternate [1; 2] [].
Eval compute in alternate [1; 3] [2; 4].

Inductive alt : list nat -> list nat -> list nat -> Prop :=
| alt_nil : forall l, alt [] l l
| alt_step : forall a l t1 t2,
    alt l t1 t2 -> alt (a :: t1) l (a :: t2).

Lemma alt_nil_emp_l_12 :
  alt [] [1; 2] [1; 2].
Proof.
apply alt_nil.
Qed.

Lemma alt_nil_emp_r_12 :
  alt [1; 2] [] [1; 2].
Proof.
apply alt_step.
apply alt_nil.
Qed.

Lemma alt_nil_emp_r :
  forall l, alt l [] l.
Proof.
induction l.
- apply alt_nil.
- apply alt_step.
  apply alt_nil.
Qed.

Lemma alt_1234 :
  alt [1; 3] [2; 4] [1; 2; 3; 4].
Proof.
apply alt_step.
apply alt_step.
apply alt_step.
apply alt_nil_emp_r.
Qed.

Lemma alt_alternate : 
  forall l1 l2 l3, alt l1 l2 l3 -> alternate l1 l2 = l3.
Proof.
induction l1; intros.
- inversion H. subst. simpl. reflexivity.
- destruct l2; simpl; inversion H; inversion H4; auto.
  apply IHl1 in H9. rewrite H9. reflexivity.
Qed.

Extraction "alternate.ml" alternate.

Extraction Language Haskell.
Extraction "alternate.hs" alternate.

Extraction Language Ocaml.
Require Import ExtrOcamlBasic.
Require Import ExtrOcamlNatInt.
Extraction "alternate.ml" alternate.
