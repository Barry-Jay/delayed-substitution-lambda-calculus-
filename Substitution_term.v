(* This program is free software; you can redistribute it and/or      *)
(* modify it under the terms of the GNU Lesser General Public License *)
(* as published by the Free Software Foundation; either version 2.1   *)
(* of the License, or (at your option) any later version.             *)
(*                                                                    *)
(* This program is distributed in the hope that it will be useful,    *)
(* but WITHOUT ANY WARRANTY; without even the implied warranty of     *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the      *)
(* GNU General Public License for more details.                       *)
(*                                                                    *)
(* You should have received a copy of the GNU Lesser General Public   *)
(* License along with this program; if not, write to the Free         *)
(* Software Foundation, Inc., 51 Franklin St, Fifth Floor, Boston, MA *)
(* 02110-1301 USA                                                     *)


(**********************************************************************)
(*              Intensional Lambda Calculus                           *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *) 
(* Lambda Calculus from Project Coq                                   *) 
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                   Substitution_term.v                              *)
(*                                                                    *)
(*                     Barry Jay                                      *)
(*                                                                    *)
(* adapted from Substitution.v of Project Coq  to act on boa-terms    *)
(**********************************************************************)

Require Import Arith.
Require Import Delayed_Terms.
Require Import Test.
Require Import General.
Require Import Delayed_Tactics.


Lemma relocate_null :
forall (n n0 : nat), relocate n n0 0 = n.
Proof. split_all. unfold relocate. case (test n0 n); intro; auto with arith. Qed.

Lemma relocate_lessthan : forall m n k, m<=k -> relocate k m n = (n+k). 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 
Lemma relocate_greaterthan : forall m n k, m>k -> relocate k m n = k. 
Proof. split_all. unfold relocate. elim(test m k); split_all; try noway. Qed. 

Ltac relocate_lt := 
try (rewrite relocate_lessthan; [| omega]; relocate_lt); 
try (rewrite relocate_greaterthan; [| omega]; relocate_lt);
try(rewrite relocate_null). 


Lemma relocate_zero_succ :
forall n k, relocate 0 (S n) k = 0.
Proof.  split_all. Qed.

Lemma relocate_succ :
forall n n0 k, relocate (S n) (S n0) k = S(relocate n n0 k).
Proof. 
intros; unfold relocate. elim(test(S n0) (S n)); elim(test n0 n); split_all. 
noway. 
noway. 
Qed. 

Lemma relocate_mono : forall M N n k, relocate M n k = relocate N n k -> M=N. 
Proof. 
intros M N n k. 
unfold relocate.
elim(test n M); elim(test n N); split_all; omega. 
Qed. 

(* Lifting lemmas *)

Lemma lift_rec_null_term : 
forall (U : lambda)(n: nat), lift_rec U n 0 = U.
Proof. 
simple induction U; split_all.  
relocate_lt; auto. rewrite H; auto. 
Qed.

Lemma lift1 :
 forall (U : lambda) (j i k : nat),
 lift_rec (lift_rec U i j) (j + i) k = lift_rec U i (j + k).
Proof.
simple induction U; simpl in |- *;  split_all. 
unfold relocate. 
elim (test i n); elim (test (j+i) (j+ n)); split_all; try noway. 
assert(k + (j + n) = j + k + n) by omega. congruence. 
elim (test (j + i) n); split_all; try noway.
replace (S(j+i)) with (j + S i) by omega. 
rewrite H.  auto. 
Qed. 

Lemma lift_lift_rec :
 forall (U : lambda) (k p n i : nat),
 i <= n ->
 lift_rec (lift_rec U i p) (p + n) k = lift_rec (lift_rec U n k) i p.
Proof.
simple induction U; simpl in |- *;  split_all.
(* 4 *) 
rewrite H; split_all. rewrite H0; split_all. 
(* 3 *) 
unfold relocate.
elim(test i n); split_all; try noway. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i (k+n)); split_all; try noway. 
assert(k+(p+n) = p+ (k+n)) by omega. 
rewrite H1; auto. 
rewrite H; auto. 
elim(test (p+n0) (p+n)); split_all; try noway. 
elim(test i n); split_all; try noway. 
rewrite H; auto. 
elim(test n0 n); split_all; try noway. 
elim(test (p+n0) n); split_all; try noway. 
elim(test i n); split_all; try noway. 
rewrite H; auto. 
(* 2 *) 
replace(S(p+n)) with (p + S n) by auto. rewrite H; auto. omega. 
(* 1 *) 
rewrite H; split_all.  rewrite H0; split_all. 
Qed. 


Lemma lift_lift_term :
 forall (U : lambda) (k p n : nat),
 lift_rec (lift p U) (p+ n) k = lift p (lift_rec U n k).
Proof.
unfold lift in |- *; intros; apply lift_lift_rec; trivial with arith.
Qed.

Lemma liftrecO : forall (U : lambda) (n : nat), lift_rec U n 0 = U.
Proof.
simple induction U; simpl in |- *; intros; split_all; relocate_lt; congruence. 
Qed.

Lemma liftO : forall (U : lambda) , lift 0 U = U.
Proof.
unfold lift in |- *; split_all; apply liftrecO.
Qed.

Lemma lift_rec_lift_rec :
 forall (U : lambda) (n p k i : nat),
 k <= i + n ->
 i <= k -> lift_rec (lift_rec U i n) k p = lift_rec U i (p + n).

Proof.
simple induction U; split_all.
(* 4 *) 
rewrite H; split_all; rewrite H0; split_all; split_all.
(* 3 *) 
unfold relocate. 
elim(test i n); split_all; try noway. 
elim(test k (n0 + n)); split_all; try noway. 
replace (p+(n0+n)) with (p + n0 + n) by omega. rewrite H; auto. 
elim(test k n); split_all; try noway. rewrite H; auto. 
(* 2 *) 
rewrite H; split_all; omega. 
(* 1 *) 
rewrite H; split_all; rewrite H0; split_all; split_all.
Qed. 

Lemma lift_rec_lift :
 forall (U : lambda)  (n p k i : nat),
 k <= n -> lift_rec (lift  n U)  k p = lift (p + n) U.
Proof.
unfold lift in |- *; intros; rewrite lift_rec_lift_rec; trivial with arith.
Qed.



Lemma gt_plus : forall i m n : nat, i>m+n -> i> n.
Proof.
induction m.
simpl; tauto.
intros; apply (IHm); auto with arith.
Qed.

Lemma le_plus : forall i m n : nat, i +m <= n -> i<= n.
Proof.
induction m; intros. 
elim H;  auto with arith.
apply (IHm). 
apply le_trans with (i+S m).
auto with arith. trivial.

Qed.


Ltac lrlr_absurd p k n := 
absurd (p+S k> S n); [
apply le_not_gt;
replace (p+ S k) with (S (p+k)); auto with arith | trivial].

