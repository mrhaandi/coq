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

Lemma iter_swap :
  forall n (A:Type) (f:A -> A) (x:A),
    iter n f (f x) = f (iter n f x).
Proof.
  intros n A f x. revert n.
  apply (induction).
  - intros ???.
  assert (HH := @iter_wd A x0 y H).
  rewrite H.
  intros n. pattern n. revert n.
  apply case_analysis.
  - intros ???. split.
    + intros ??. admit.
  - intros IH. rewrite !iter_0. reflexivity.
  - intros n IH. rewrite !iter_succ, IH; [reflexivity|].
    apply lt_succ_diag_r.

    Search (_ < S _).
  intros n IH. revert n.

  - intros ???. rewrite H. cbn.
  Print NAxiomsSig'.
  induction n.

 intros. symmetry. now apply iter_swap_gen.
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