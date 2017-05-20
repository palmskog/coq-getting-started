Require Import Alternate.

Lemma alt_exists : forall l1 l2, exists l3, alt l1 l2 l3.
Proof.
induction l1; intros; destruct l2.
- exists []. apply alt_nil.
- exists (n :: l2). apply alt_nil.
- exists (a :: l1). apply alt_step. apply alt_nil.
- specialize(IHl1 l2). destruct IHl1. exists (a :: n :: x).
  repeat apply alt_step. auto.
Qed.
