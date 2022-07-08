Require Import List.
Require Import Arith.
Require Import Recdef.
Require Import Lia.

Definition len (p: list nat * list nat) := length (fst p) + length (snd p).

Function merge (p: list nat * list nat) {measure len p} :=
match p with
| (nil, l2) => l2
| (l1, nil) => l1
| ((hd1 :: tl1) as l1, (hd2 :: tl2) as l2) =>
if hd1 <=? hd2 then hd1 :: merge (tl1, l2)
else hd2 :: merge (l1, tl2)
end.
Proof.
  - intros.
    unfold len.
    simpl.
    lia.
  - intros.
    unfold len.
    simpl.
    lia.
Defined.

Inductive sorted : list nat -> Prop :=
| sorted_nil: sorted nil
| sorted_one: forall x, sorted (x :: nil)
| sorted_all: forall x y l, x <= y -> sorted (y :: l) -> sorted (x :: y :: l).                        

Theorem merge_sorted: forall l1 l2, sorted l1 -> sorted l2 -> sorted (merge(l1,l2)).
Proof.
  Admitted.
