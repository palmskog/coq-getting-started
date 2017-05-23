Require Import ZArith.
Require Import Coq.ZArith.Zmax.

Section BinaryTree.

Open Scope Z_scope.

Inductive BTree : Set :=
| leaf : BTree
| btree : BTree -> BTree -> BTree.

Definition max := Zmax.

Fixpoint height (t : BTree) : Z := 
match t with 
| leaf => 0
| btree t1 t2 => 1 + (max (height t1) (height t2))
end.

Lemma height_nonnegative : forall t, height t >= 0.
proof.
  let t : BTree.
  per induction on t.
    suppose it is leaf.
      have (height leaf = 0).  
      hence thesis.
    suppose it is (btree t1 t2) and H_ind1 : thesis for t1 and H_ind2 : thesis for t2.
      have H0: (height (btree t1 t2) = 1 + max (height t1) (height t2)).
      have H1: (height t1 <= max (height t1) (height t2)) by Zle_max_l.
      have H2: (1 + max (height t1) (height t2) >= 0) by H_ind1, H_ind2, H1.
      hence thesis by H0, H1, H2.
  end induction.
end proof.
Qed.

Eval compute in (height (btree leaf (btree leaf leaf))).

Lemma height_is_2 : height (btree leaf (btree leaf leaf)) = 2.
proof.
  have (height (btree leaf (btree leaf leaf))
       = 1 + max (height leaf) (height (btree leaf leaf))).
       ~= (1 + max 0 (1 + max (height leaf) (height leaf))).
       ~= (1 + max 0 (1 + max 0 0)).
       ~= (1 + max 0 (1 + 0)).
       ~= (1 + 1).
  thus ~= 2.
end proof.
Qed.

Fixpoint numleaves (t : BTree) : Z :=
match t with 
| leaf => 1
| btree t1 t2 => numleaves t1 + numleaves t2
end.

Eval compute in (numleaves (btree leaf (btree leaf leaf))).

Lemma numleaves_is_3 : numleaves (btree leaf (btree leaf leaf)) = 3.
proof.
  have (numleaves (btree leaf (btree leaf leaf))
       = numleaves leaf + numleaves (btree leaf leaf)).
       ~= (1 + numleaves leaf + numleaves leaf).
       ~= (1 + 1 + 1).
  thus ~= 3.
end proof.
Qed.

Inductive complete : BTree -> Prop :=
| complete_leaf : complete leaf
| complete_btree : 
    forall t1 t2, 
      complete t1 -> 
      complete t2 -> 
      height t1 = height t2 ->
      complete (btree t1 t2).

Lemma complete_definition : forall t1 t2, 
  complete (btree t1 t2) <-> (complete t1 /\ complete t2 /\ height t1 = height t2).
proof.
  let t1 : BTree.
  let t2 : BTree.
  claim H0: (complete (btree t1 t2) -> (complete t1 /\ complete t2 /\ height t1 = height t2)).
    assume H1: (complete (btree t1 t2)).
    have H2: (complete t1) by H1 using inversion H1.
    have H3: (complete t2) by H1 using inversion H1.
    have H4: (height t1 = height t2) by H1 using inversion H1.
    hence thesis by H2, H3, H4.
  end claim.
  claim H1: ((complete t1 /\ complete t2 /\ height t1 = height t2) -> complete (btree t1 t2)).
    assume H1: (complete t1 /\ complete t2 /\ height t1 = height t2).
    have H2: (complete t1) by H1.
    have H3: (complete t2) by H1.
    have H4: (height t1 = height t2) by H1.
    hence thesis by H2, H3, H4, complete_btree.
  end claim.
  hence thesis by H0, H1.
end proof.
Qed.

Theorem complete_numleaves_height : forall t, complete t -> numleaves t = 2^(height t).
proof.
  let t : BTree.
  per induction on t.
    suppose it is leaf.
      assume H0: (complete leaf).
      have (numleaves leaf = 1).
           ~= (2^0).
      thus ~= (2^(height leaf)).
    suppose it is (btree t1 t2) and H_ind1: thesis for t1 and H_ind2: thesis for t2.
      assume H0: (complete (btree t1 t2)).
      have H1: (complete t1) by H0 using inversion H0.
      have H2: (complete t2) by H0 using inversion H0.
      have H3: (height t1 = height t2) by H0 using inversion H0.
      have H4: (numleaves t1 = 2^(height t1)) by H1, H_ind1.
      have H5: (numleaves t2 = 2^(height t2)) by H2, H_ind2.
      have H6: (1 >= 0).
      have H7: (height t1 >= 0) by height_nonnegative.
      have H8: (height t1 = max (height t1) (height t1)) by Zmax_idempotent.
      have (numleaves (btree t1 t2) 
           = numleaves t1 + numleaves t2).
           ~= (2^(height t1) + 2^(height t2)) by H4, H5.
           ~= (2^(height t1) + 2^(height t1)) by H3.
           ~= (2 * 2^(height t1)).
           ~= (2^1 * 2^(height t1)).
           ~= (2^(1 + height t1)) by (Zpower_exp 2 1 (height t1) H6 H7).
           ~= (2^(1 + (max (height t1) (height t1)))) by H8.
           ~= (2^(1 + max (height t1) (height t2))) by H3.
      thus ~= (2^(height (btree t1 t2))).
  end induction.
end proof.
Qed.

Theorem complete_numleaves_height' : forall t, complete t -> numleaves t = 2^(height t).
Proof.
induction t; intros.
- reflexivity.
- apply complete_definition in H.
  destruct H.
  destruct H0.
  apply IHt1 in H.
  apply IHt2 in H0.  
  simpl numleaves.
  rewrite H.
  rewrite H0.
  assert (height t1 = max (height t1) (height t1)).
    rewrite Zmax_idempotent; reflexivity.
  assert (height (btree t1 t2) = (1 + (max (height t1) (height t2)))) by reflexivity.
  rewrite H3.
  rewrite <- H1.  
  rewrite <- H2.
  rewrite Zpower_exp; auto with zarith.
  * assert (2 ^ height t1 + 2 ^ height t1 = 2 * 2 ^ height t1) by auto with zarith.
    rewrite H4.
    reflexivity.
  * apply height_nonnegative.
Qed.

End BinaryTree.
