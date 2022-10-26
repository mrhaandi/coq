(************************************************************************)
(*         *   The Coq Proof Assistant / The Coq Development Team       *)
(*  v      *         Copyright INRIA, CNRS and contributors             *)
(* <O___,, * (see version control and CREDITS file for authors & dates) *)
(*   \VV/  **************************************************************)
(*    //   *    This file is distributed under the terms of the         *)
(*         *     GNU Lesser General Public License Version 2.1          *)
(*         *     (see LICENSE file for the text of the license)         *)
(************************************************************************)

Require Import NAxioms NSub.

(** Properties of Iteration *)

Module NIterProp
(Import N : NAxiomsSig')
(Import N' : NSubProp N)
  (Import NI : NAxiomsIter N N).


  Lemma mymy {A : Type} (f : A -> A) (a : A) :
    Proper (eq ==> iff)
      (fun x => forall y, x == y -> iter x f a = iter y f a).
  Proof.
    intros x y Hxy. split.
    - intros H' z Hyz.
      assert (Hxz : x == z) by now transitivity y.
      now rewrite <- (H' _ Hxy), <- (H' _ Hxz).
    - intros H' z Hxz.
      assert (Hyx : y == x) by now symmetry.
      assert (Hyz : y == z) by now rewrite Hyx.
      now rewrite <- (H' _ Hyx), <- (H' _ Hyz).
  Qed.

  (*

  #[local] Instance iter_wd {A : Type} :
  Proper (eq ==> (Logic.eq ==> Logic.eq) ==> Logic.eq ==> Logic.eq) (fun n => @iter n A).
Proof.
intros ?????????. subst.
revert y H. pattern x.
apply (induction).
- admit.
- intros y Hy. admit.
- intros x' IH y Hy.
Admitted. (* doable ? *)
*)
  Lemma aux0  {A : Type} {f : A -> A} {a : A} {x : t} :
    x == 0 -> iter x f a = a.
  Proof.
    pattern x. apply (induction).
    - intros ???. split.
      + intros IH .
    clear x. intros x IH Hx.
    destruct ()
    zero_or_succ
  Admitted.

*)

(*
maybe this is not provable as is?
*)
  Lemma aux  {A : Type} {f : A -> A} {a : A} {x y : t} :
    x == y -> iter x f a = iter y f a.
  Proof.
    revert y. pattern x.
    apply (induction).
    - apply mymy.
    - intros y Hy.
      assert (HH := mymy f a 0 y Hy).
      cbn in HH.
    clear x. intros x IH y Hxy.
    destruct ()
    zero_or_succ
  Admitted.
  (*
  #[local] Instance iter_wd {A : Type} :
    Proper (eq ==> (Logic.eq ==> Logic.eq) ==> Logic.eq ==> Logic.eq) (fun n => @iter n A).
  Proof.
  intros ?????????. subst.
  revert y H. pattern x.
  apply (induction).
  - admit.
  - intros y Hy. admit.
  - intros x' IH y Hy.
  Admitted. (* doable ? *)
*)

Lemma iter_swap :
  forall n (A:Type) (f:A -> A) (x:A),
    iter n f (f x) = f (iter n f x).
Proof.
  intros n A f x. revert n.
  apply (induction).
  - intros ???. now rewrite !(aux H).
  - now rewrite !iter_0.
  - intros ? H. now rewrite !iter_succ, H.
Qed.

Lemma div_0_l : forall a, 0/a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Ha].
  - apply div_0_r.
  - now apply div_0_l.
Qed.

Lemma mod_0_l : forall a, 0 mod a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Hb].
  - apply mod_0_r.
  - now apply mod_0_l.
Qed.

#[local] Hint Rewrite div_0_l mod_0_l div_0_r mod_0_r : nz.

Lemma div_mod : forall a b, a == b*(a/b) + (a mod b).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mod.
Qed.

Lemma mod_eq : forall a b, a mod b == a - b*(a/b).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_eq.
Qed.

Lemma mod_same : forall a, a mod a == 0.
Proof.
  intros a. destruct (eq_decidable a 0) as [->|Ha].
  - now nzsimpl.
  - now apply mod_same.
Qed.

Lemma mod_mul : forall a b, (a*b) mod b == 0.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_mul.
Qed.

Lemma mod_le : forall a b, a mod b <= a.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply mod_le.
Qed.

Lemma div_le_mono : forall a b c, a<=b -> a/c <= b/c.
Proof.
  intros a b c. destruct (eq_decidable c 0) as [->|Hc].
  - now nzsimpl.
  - now apply div_le_mono.
Qed.

Lemma mul_div_le : forall a b, b*(a/b) <= a.
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. apply le_0_l.
  - now apply mul_div_le.
Qed.

Lemma div_exact : forall a b, (a == b*(a/b) <-> a mod b == 0).
Proof.
  intros a b. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_exact.
Qed.

Lemma div_lt_upper_bound : forall a b q, a < b*q -> a/b < q.
Proof.
  intros a b q. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. now intros ?%nlt_0_r.
  - now apply div_lt_upper_bound.
Qed.

Lemma div_le_upper_bound : forall a b q, a <= b*q -> a/b <= q.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - nzsimpl. intros. apply le_0_l.
  - now apply div_le_upper_bound.
Qed.

Lemma mod_add : forall a b c, (a + b * c) mod c == a mod c.
Proof.
  intros a b c. destruct (eq_decidable c 0) as [->|Hc].
  - now nzsimpl.
  - now apply mod_add.
Qed.

Lemma div_mul_cancel_r : forall a b c, c~=0 -> (a*c)/(b*c) == a/b.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mul_cancel_r.
Qed.

Lemma div_mul_cancel_l : forall a b c, c~=0 -> (c*a)/(c*b) == a/b.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - now apply div_mul_cancel_l.
Qed.

Lemma mul_mod_distr_r : forall a b c, (a*c) mod (b*c) == (a mod b) * c.
Proof.
  intros a b c. destruct (eq_decidable b 0) as [->|Hb].
  - now nzsimpl.
  - destruct (eq_decidable c 0) as [->|Hc].
    + now nzsimpl.
    + now apply mul_mod_distr_r.
Qed.

*)