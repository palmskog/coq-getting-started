Section Ex12_1a.

Variable p q r s t : Prop.

Hypothesis H0 : (p /\ q) /\ r.
Hypothesis H1 : s /\ t.

Lemma Ex12_1a : q /\ s.
proof.
  have H2: (p /\ q) by H0.
  have H3: q by H2.
  have H4: s by H1.
  hence thesis by H3, H4.
end proof.
Qed.

Lemma Ex12_1a' : q /\ s.
Proof.
tauto.
Qed.

End Ex12_1a.

(* Exercise 1.2) 1g *)
Section Ex12_1g.

Variable p q : Prop.

Hypothesis H0 : p.

Lemma Ex12_1g : q -> (p /\ q).
proof.
  assume H1: q.
  hence thesis by H0, H1.
end proof.
Qed.

End Ex12_1g.

(* Exercise 1.2) 2e *)
Section Ex12_2e.

Variable p q r : Prop.

Hypothesis H0: p -> (q \/ r).
Hypothesis H1: ~ q.
Hypothesis H2: ~ r.

Lemma Ex12_2e : ~ p.
proof.
  assume H4: p.
  have H5: (q \/ r) by H0, H4.
  per cases of (q \/ r) by H5.
    suppose H6: q.
      hence thesis by H1, H6.
    suppose H6: r.
      hence thesis by H2, H6.
  end cases.
end proof.
Qed.

End Ex12_2e.

(* Exercise 1.2) 3g *)
Section Ex12_3g.

Variable p q : Prop.

Lemma Ex12_3g : ~ p \/ q -> (p -> q).
proof.
  assume H0: (~ p \/ q).
  per cases of (~ p \/ q) by H0.
    suppose H1: (~ p).
      assume H2: p.
      hence thesis by H1, H2.
    suppose H1: q.
      assume H2: p.
      hence thesis by H1.
  end cases.
end proof.
Qed.

End Ex12_3g.

(* Exercise 1.2) 3i *)  
Section Ex12_3i.

Variable c n t h s p : Prop.

Hypothesis H0: (c /\ n) -> t.
Hypothesis H1: h /\ ~ s.
Hypothesis H2: h /\ ~ (s \/ c) -> p.

Lemma Ex12_3i : (n /\ ~ t) -> p.
proof.
  assume H3: (n /\ ~ t).
  have H4: h by H1.
  claim H5: (~ (s \/ c)).
    assume H5: (s \/ c).
    per cases of (s \/ c) by H5.
      suppose H6: s.
        have H7: (~ s) by H1.
        hence thesis by H6, H7.
      suppose H6: c.
        have H7: n by H3.
        have H8: (c /\ n) by H6, H7.
        have H9: t by H8, H0.
        have H10: (~ t) by H3.
        hence thesis by H9, H10.
    end cases.
  end claim.
  have H6: (h /\ ~ (s \/ c)) by H4, H5.
  hence thesis by H6, H2.
end proof.
Qed.

End Ex12_3i.

(* Exercise 2.3 9 *)
Section Ex23_9.

Variable A : Set.
Variable P : A -> Prop.
Variable q : Prop.

Hypothesis H0 : exists x, (P x -> q).

Lemma Ex23_9 : (forall x, P x) -> q.
proof.
  assume H1: (forall x, P x).
  consider x0 such that H2: (P x0 -> q) from H0.
  have H3: (P x0) by H1.
  hence thesis by H3, H2.
end proof.
Qed.

Lemma Ex23_9' : (forall x, P x) -> q.
Proof.
firstorder.
Qed.

End Ex23_9.

Section Ex23_9k.

Variable A : Set.
Variable P Q : A -> Prop.

Hypothesis H0 : forall x, (P x /\ Q x).

Lemma Ex23_9k : (forall x, P x) /\ (forall x, Q x).
proof.
  claim H1: (forall x, P x).
    let x0 : A.
    have H1: (P x0 /\ Q x0) by H0.
    have H2: (P x0) by H1.
    hence thesis by H2.
  end claim.
  claim H2: (forall x, Q x).
    let x0 : A.
    have H2: (P x0 /\ Q x0) by H0.
    have H3: (Q x0) by H2.
    hence thesis by H3.
  end claim.
  hence thesis by H1, H2.
end proof.
Qed.

Lemma Ex23_9k' : (forall x, P x) /\ (forall x, Q x).
Proof.
firstorder.
Qed.

End Ex23_9k.

Section Ex23_9s.

Variable A : Set.
Variable P : A -> Prop.

Hypothesis H0 : exists x, ~ P x.

Lemma Ex23_9s : ~ (forall x, P x).
proof.
  assume H1: (forall x, P x).
  consider x0 such that H2: (~ P x0) from H0.
  have H3: (P x0) by H1.
  hence thesis by H2, H3.
end proof.
Qed.

End Ex23_9s.

Section Ex23_9r.

Variable A : Set.
Variable P : A -> Prop.

Hypothesis H0 : ~ (exists x, P x).

Lemma Ex23_9r : forall x, ~ P x.
proof.
  let x0 : A.
  assume H1: (P x0).
  have H2: (exists x, P x) by H1.
  hence thesis by H2, H0.
end proof.
Qed.

End Ex23_9r.

Section KS1_4.

Variable A : Set.
Variable P : A -> A -> Prop.

Hypothesis H0: forall x y, P x y -> ~ P y x.

Lemma KS1_4 : forall x, ~ P x x.
proof.
  let x : A.
  assume H1: (P x x).
  have H2: (~ (P x x)) by H0.
  hence thesis by H1, H2.
end proof.
Qed.

End KS1_4.

Section KS_10_E.

Variable A : Set.
Variable R : A -> Prop.
Variable q : Prop.

Hypothesis H : forall y, q -> R y.

Lemma KS_10_E : q -> forall x, R x.
proof.
  assume H0: q.
  let x : A.
  have H1: (q -> R x) by H.
  hence thesis by H0, H1.
end proof.
Qed.

Lemma KS_10_E' : q -> forall x, R x.
Proof.
firstorder.
Qed.

End KS_10_E.

Section KS_10_C.

Variable A : Set.
Variable Q : A -> Prop.

Hypothesis H : forall x, ~ Q x.

Lemma KS_10_C : ~ exists x, Q x.
proof.
  assume H0: (exists x, Q x).
  consider x such that H1: (Q x) from H0.
  have H2: (~ Q x) by H.
  hence thesis by H1, H2.
end proof.
Qed.

End KS_10_C.
