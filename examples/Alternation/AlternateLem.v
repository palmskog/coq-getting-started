Require Import Alternate.

Lemma alternate_alt :
  forall l1 l2 l3, alternate l1 l2 = l3 -> alt l1 l2 l3.
Proof.
induction l1; simpl; intros.
- rewrite H. apply alt_nil.
- destruct l2; subst; apply alt_step; try apply alt_nil.
  apply alt_step. apply IHl1. reflexivity.
Qed.

Lemma alternate_correct : 
  forall l1 l2 l3, alternate l1 l2 = l3 <-> alt l1 l2 l3.
Proof. 
intros; split; [apply alternate_alt | apply alt_alternate].
Qed.
