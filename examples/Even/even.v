Require Import Arith.
Require Import Omega.
Require Import Arith.Wf_nat.

(* standard definition *)

Inductive even : nat -> Prop :=
 | zero_even : even 0
 | other_even : forall n : nat, even n -> even (S (S n)).

Inductive odd : nat -> Prop :=
 | one_odd : odd 1
 | other_odd : forall n : nat, odd n -> odd (S (S n)).

(* alternative definition *)

Fixpoint even' (n : nat) :=
  match n with
    | O => True
    | 1 => False
    | S (S m) => even' m
  end.

Fixpoint odd' (n : nat) :=
  match n with
    | O => False
    | 1 => True
    | S (S m) => odd' m
  end.

Eval compute in even' 3.

Lemma not_even_3 : ~ even 3.
Proof.
intro.
inversion H.
subst.
inversion H1.
Qed.

Lemma odd'_3 : odd' 3.
Proof.
compute.
trivial.
Qed.

Lemma odd_3 : odd 3.
Proof.
apply other_odd.
apply one_odd.
Qed.

Lemma even_implies_odd : forall n : nat, even n -> odd (S n).
Proof.
intros.
induction H.
- apply one_odd.
- apply other_odd.
  assumption.
Qed.

Lemma odd_implies_even : forall n : nat, odd n -> even (S n).
Proof.
intros.
induction H.
- apply other_even.
  apply zero_even.
- apply other_even.
  assumption.
Qed.

Theorem all_even_or_odd : forall n : nat, even n \/ odd n.
Proof.
induction n.
- left.
  apply zero_even.
- destruct IHn.
  * right.
    apply even_implies_odd.
    assumption.
  * left.
    apply odd_implies_even.
    assumption.
Qed.

Theorem all_even_or_odd_alt : forall n, even n \/ odd n.
Proof.
 apply well_founded_ind with (R := lt).
 apply lt_wf.
 intros.
 destruct x.
 left; apply zero_even.
 destruct x.
 right; apply one_odd.
 assert (forall a b c d: Prop, (c -> d) -> (a -> b) -> (c \/ a) -> (d \/ b)).
 intros.
 elim H2; intros.
 apply H0 in H3; left;  assumption.
 apply H1 in H3; right; assumption. 
 apply (H0 (odd x) (odd (S (S x))) (even x) (even (S (S x)))).
 apply other_even.
 apply other_odd.
 apply H.
 auto.
Qed.

Theorem all_even_or_odd_fix : forall n : nat, even' n \/ odd' n.
Proof.
 intros.
 apply (lt_wf_ind _ (fun (n:nat) => (even' n \/ odd' n))).
 intros n0 H.
 induction n0.
 left; constructor.
 induction n0.
 right; constructor.
 simpl.
 apply H.
 auto.
Qed.

Theorem all_even_or_odd_fix_alt : forall n : nat, even' n \/ odd' n.
Proof.
 intros n0.
 elim n0 using (well_founded_ind (lt_wf)).
 intros.
 induction x.
 left.
 constructor.
 induction x.
 right.
 constructor.
 simpl.
 apply H.
 auto.
Qed.

Lemma next_not_even : forall n, odd n -> ~(odd (S n)).
Proof.
 induction n.
 intros.
 intro.
 inversion H.
 intros.
 intro.
 elim IHn.
 inversion H0.
 assumption.
 assumption.
Qed.

Theorem even_odd_exclusively : forall n, ~(even n /\ odd n).
Proof.
 induction n.
 intro.
 elim H.
 intros.
 inversion H1.
 intro.
 elim H.
 intros.
 apply next_not_even in H1.
 elim H1.
 apply even_implies_odd.
 apply H0.
Qed.

Lemma even_times_two : forall n : nat, even n -> exists m : nat, n = 2 * m.
Proof.
 intros.
 induction n.
 exists 0.
 reflexivity.
 elim H.
 exists 0.
 reflexivity.
 intros.
 elim H1.
 intros.
 exists (x+1).
 omega.
Qed.

Lemma two_times_even : forall n : nat, (exists m : nat, n = 2 * m) -> even n.
Proof.
 intros.
 elim H.
 intros.
 rewrite H0; clear H0.
 elim x.
 simpl.
 apply zero_even.
 intro.
 intros.
 simpl.
 rewrite plus_comm.
 simpl.
 rewrite <- plus_comm.
 apply other_even.
 assert (n0 + (n0 + 0) = 2 * n0).
 omega.
 rewrite H1.
 assumption.
Qed.

Theorem even_plus_even : forall m n : nat, even m -> even n -> even (m + n).
Proof.
 intros m n.
 intros.
 apply even_times_two in H.
 apply even_times_two in H0.
 apply two_times_even.
 elim H.
 intros.
 elim H0.
 intros.
 rewrite H1.
 rewrite H2.
 exists (x + x0).
 omega.
Qed.

Lemma odd_next : forall n : nat, odd (S n) -> even n.
Proof.
 intros.
 destruct n.
 apply zero_even.
 apply odd_implies_even.
 inversion H.
 assumption.
Qed.

Lemma odd_times_two : forall n : nat, odd n -> exists m : nat, n = 2 * m + 1.
Proof.
 intros n.
 induction n.
 intros.
 inversion H.
 intros.
 apply odd_next in H.
 apply even_times_two in H.
 elim H.
 intros.
 rewrite H0; clear H0.
 exists x.
 omega.
Qed.

Lemma two_times_odd : forall n : nat, (exists m : nat, n = 2 * m + 1) -> odd n. 
Proof.
 intros.
 elim H; clear H.
 intros x H0.
 rewrite H0; clear H0.
 elim x.
 simpl.
 apply one_odd.
 intros.
 rewrite plus_comm.
 simpl.
 apply other_odd.
 assert (2 * n0 + 1 = (n0 + S (n0 + 0))).
 omega.
 rewrite <- H0.
 assumption.
Qed.

Theorem odd_plus_odd : forall m n : nat, odd m -> odd n -> even (m + n).
Proof.
 intros.
 apply odd_times_two in H.
 apply odd_times_two in H0.
 apply two_times_even.
 elim H.
 elim H0.
 intros.
 rewrite H1.
 rewrite H2.
 exists (x + x0 + 1).
 omega.
Qed.

Theorem odd_plus_even : forall m n : nat, odd m -> even n -> odd (m + n).
Proof.
 intros.
 apply odd_times_two in H.
 apply even_times_two in H0.
 apply two_times_odd.
 elim H; clear H.
 elim H0; clear H0.
 intros.
 rewrite H; clear H.
 rewrite H0; clear H0.
 exists (x + x0).
 omega.
Qed.

Theorem three_average_integer : forall m n p : nat, (exists q, 2 * q = m + n \/ 2 * q = m + p \/ 2 * q = n + p).
Proof.
 intros.
 assert (even m \/ odd m).
 apply all_even_or_odd.
 assert (even n \/ odd n).
 apply all_even_or_odd.
 assert (even p \/ odd p).
 apply all_even_or_odd.
 elim H.
 elim H0.
 elim H1.
 intros.
 assert (even (m + n)).
 apply even_plus_even.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 left.
 rewrite H6.
 reflexivity.
 intros.
 assert (even (m + n)).
 apply even_plus_even.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 left.
 rewrite H6.
 reflexivity.
 elim H1.
 intros.
 assert (even (m + p)).
 apply even_plus_even.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 right.
 left.
 rewrite H6.
 reflexivity.
 intros.
 assert (even (p + n)).
 apply odd_plus_odd.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 right.
 right.
 rewrite <- H6.
 rewrite plus_comm.
 reflexivity.
 elim H0.
 elim H1.
 intros.
 assert (even (n + p)).
 apply even_plus_even.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 right.
 right.
 rewrite H6.
 reflexivity.
 intros.
 assert (even (m + p)).
 apply odd_plus_odd.
 assumption.
 assumption.
 apply even_times_two in H5.
 elim H5.
 intros.
 exists x.
 right.
 left.
 rewrite <- H6.
 reflexivity.
 intros.
 assert (even (m + n)).
 apply odd_plus_odd.
 assumption.
 assumption.
 apply even_times_two in H4.
 elim H4.
 intros.
 exists x.
 left.
 rewrite <- H5.
 reflexivity.
Qed.

Lemma next_not_odd : forall n, even n -> ~(even (S n)).
Proof.
 induction n.
 intros.
 intro.
 inversion H0.
 intros.
 intro.
 elim IHn.
 inversion H0.
 assumption.
 assumption.
Qed.

Lemma even_not_odd : forall n, ~(even n) -> odd n.
Proof.
 intros.
 assert (H1: even n \/ odd n).
 apply all_even_or_odd.
 elim H1.
 intros.
 elim H.
 apply H0.
 trivial.
Qed.

Lemma odd_not_even : forall n, ~(odd n) -> even n.
Proof.
 intros.
 assert (H1: even n \/ odd n).
 apply all_even_or_odd.
 elim H1.
 intros.
 apply H0.
 intros.
 elim H.
 assumption.
Qed.

Lemma even_not_odd_again : forall n, even n -> ~(odd n).
Proof.
 intros.
 assert (H1: even n \/ odd n).
 apply all_even_or_odd.
 intro.
 elim H1.
 intro.
 inversion H0.
 rewrite <- H3 in H2.
 inversion H2.
 rewrite <- H4 in H.
 rewrite <- H4 in H0.
 apply next_not_even in H0.
 elim H0.
 apply even_implies_odd.
 rewrite H4.
 apply H2.
 intro.
 apply next_not_even in H2.
 elim H2.
 apply even_implies_odd.
 assumption.
Qed.
