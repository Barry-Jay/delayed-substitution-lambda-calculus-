(**********************************************************************)
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

(**********************************************************************)
(*                  Delayed Substitution Lambda Calculus              *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Delayed_reduction.v                           *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Omega Test Delayed_Terms Delayed_Tactics.


Fixpoint swap j t := 
(* swap j and S j *) 
match t with 
| Unit  => Unit 
| Pair s t1 => Pair (swap j s) (swap j t1)
| Ref i s => 
match compare i j with 
        (* i<j *) | inleft (left _) => Ref i (swap j s)
        (* i=j *) | inleft _ =>  Ref (S i) (swap j s) 
        (* i>j *) | _ => 
                    match compare (S j) i with 
                      (* S j < i  *) | inleft (left _) =>  Ref i (swap j s)
                      (* S j = i  *) | _ => Ref j (swap j s)
                                                end
end
| Abs t1 => Abs (swap (S j) t1)
| App t1 t2 => App (swap j t1) (swap j t2)
end. 


Lemma aux1: swap 0 (Ref 0 Unit) = Ref 1 Unit. 
Proof. split_all. Qed. 

Lemma aux2: swap 1 (Ref 0 Unit) = Ref 0 Unit. 
Proof. split_all. Qed. 

Lemma aux3: swap 0 (Ref 1 Unit) = Ref 0 Unit. 
Proof. split_all. Qed. 

Lemma aux4: swap 1 (Ref 1 Unit) = Ref 2 Unit. 
Proof. split_all. Qed. 

Lemma aux5: swap 0 (Ref 2 Unit) = Ref 2 Unit. 
Proof. split_all. Qed. 

Lemma aux6: swap 1 (Ref 2 Unit) = Ref 1 Unit. 
Proof. split_all. Qed. 


Lemma lift_rec_preserves_swap: 
forall M j k, S j < k -> lift_rec (swap j M) k = swap j (lift_rec M k).
Proof.
induction M; split_all. 
(* 4 *) 
rewrite IHM1; split_all. rewrite IHM2; split_all. 
(* 3 *) 
unfold relocate; split_all. 
elim(test k n); split_all. 
elim(compare n j); split_all. elim a0; split_all; try noway. 
elim(compare (S j) n); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (S n) j); split_all; try noway. 
elim a2; split_all; try noway. 
unfold relocate; split_all. 
elim(test k n); split_all. 
elim(compare (S j) (S n)); split_all. elim a3; split_all; try noway. 
rewrite IHM; auto.
noway. 
elim(compare (S j) (S n)); split_all. elim a2; split_all; try noway. 
rewrite IHM; auto.
noway. 
elim(compare n j); split_all; try noway. 
elim a; split_all; try noway. 
unfold relocate; split_all. 
elim(test k n); split_all. 
noway. 
rewrite IHM; auto.
subst. 
unfold relocate; split_all. 
elim(test k (S j)); split_all. 
noway. 
rewrite IHM; auto.
elim(compare (S j) n); split_all. elim a; split_all; try noway. 
unfold relocate; split_all. 
elim(test k n); split_all. 
noway. 
rewrite IHM; auto.
subst. 
unfold relocate; split_all. 
elim(test k j); split_all. 
noway. 
rewrite IHM; auto.
noway. 
(* 2 *) 
rewrite IHM; auto. omega. 
(* 1 *) 
rewrite IHM1; split_all. rewrite IHM2; split_all. 
Qed. 


Lemma lift_rec_preserves_swap2: 
forall M j k, k<= j -> lift_rec (swap j M) k = swap (S j) (lift_rec M k).
Proof.
induction M; split_all.
(* 4 *) 
rewrite IHM1; split_all; try omega. rewrite IHM2; split_all; try omega. 
(* 3 *) 
unfold relocate. 
elim(test k n); split_all; try noway. 
elim(compare n j); split_all; try noway. elim a0; split_all; try noway. 
unfold relocate.
elim(test k n); split_all; try noway. 
elim(compare (S n) (S j)); split_all; try noway. 
elim a3; split_all; try noway. 
rewrite IHM; auto. 
elim(compare (S n) (S j)); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate. elim(test k (S n)); split_all; try noway. 
rewrite IHM; auto. 
elim(compare (S j) n); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (S n) (S j)); split_all; try noway. 
elim a2; split_all; try noway. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim a2; split_all; try noway. 
unfold relocate. elim(test k n); split_all; try noway. 
rewrite IHM; auto. 
subst. elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate. elim(test k j); split_all; try noway. 
rewrite IHM; split_all. 
elim(compare n j); split_all; try noway. elim a; split_all; try noway. 
unfold relocate.
elim(test k n); split_all; try noway. 
elim(compare n (S j)); split_all; try noway. 
elim a1; split_all; try noway. 
rewrite IHM; auto. 
(* 2 *) 
rewrite IHM; auto. omega. 
(* 1 *) 
rewrite IHM1; split_all; try omega. rewrite IHM2; split_all; try omega. 
Qed. 


Lemma swap_swap : 
forall M j k, S k < j -> swap j (swap k M) = swap k (swap j M). 
Proof. 
induction M; split_all. 
(* 4 *) 
rewrite IHM1; split_all. rewrite IHM2; split_all. 
(* 3 *) 
elim(compare n k); split_all. elim a; split_all; try noway. 
elim(compare n j); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare n k); split_all; try noway. 
elim a3; split_all; try noway. 
rewrite IHM; auto.
subst. elim(compare (S k) j); split_all. elim a0; split_all; try noway. 
elim(compare k j); split_all; try noway. 
elim a2; split_all; try noway. 
elim(compare k k); split_all; try noway. 
elim a4; split_all; try noway. 
rewrite IHM; auto.
elim(compare (S j) (S k)); split_all. elim a0; split_all; try noway. 
elim(compare k j); split_all; try noway. 
elim(compare (S k) n); split_all; try noway. elim a; split_all; try noway. 
elim(compare n j); split_all; try noway. 
elim a1; split_all; try noway. 
elim(compare n k); split_all; try noway. 
elim a3; split_all; try noway. 
elim(compare (S k) n); split_all. elim a3; split_all; try noway. 
rewrite IHM; auto.
noway. 
subst. elim(compare (S j) k); split_all; try noway. 
elim a2; split_all; try noway. 
elim(compare (S k) (S j)); split_all; try noway. 
elim a2; split_all; try noway. 
rewrite IHM; auto.
elim(compare (S j) n); split_all. elim a1; split_all; try noway. 
elim(compare n k); split_all; try noway. elim a3; split_all; try noway. 
elim(compare (S k) n); split_all; try noway. elim a3; split_all; try noway. 
rewrite IHM; auto.
elim(compare j k); split_all. elim a2; split_all; try noway. 
subst. elim(compare (S k) j); split_all; try noway. elim a2; split_all; try noway. 
rewrite IHM; auto.
elim(compare j k); split_all; try noway. 
subst. elim(compare k j); split_all; try noway. elim a0; split_all; try noway. 
elim(compare (S k) j); split_all; try noway. elim a2; split_all; try noway. 
elim(compare (S k) k); split_all; try noway. elim a4; split_all; try noway. 
elim(compare (S k) (S k)); split_all; try noway. elim a4; split_all; try noway. 
rewrite IHM; auto.
(* 2 *) 
rewrite IHM; auto. omega. 
(* 1 *) 
rewrite IHM1; split_all. rewrite IHM2; split_all. 
Qed. 


(* Parallel lift reduction *)

Definition termred := lambda -> lambda -> Prop. 

Inductive tuple_red1: termred := 
  | un_tuple_red : tuple_red1 Unit Unit
  | pair_tuple_red : forall M M' ,
      tuple_red1 M M' ->
      forall N N', tuple_red1 N N' -> tuple_red1 (Pair M N) (Pair M' N')
  | ref_tuple_red : forall i M M', tuple_red1 M M' -> tuple_red1 (Ref i M) (Ref i M')
  | abs_tuple_red :
      forall M M', tuple_red1 M M' -> tuple_red1 (Abs M) (Abs M') 
  | app_tuple_red :
      forall M M' ,
      tuple_red1 M M' ->
      forall N N', tuple_red1 N N' -> tuple_red1 (App M N) (App M' N')
  | ref_app_red : forall i M M' N N', tuple_red1 M M' -> tuple_red1 N N' ->
                                  tuple_red1 (App (Ref i M) N) (Ref i (Pair M' N'))
  | beta_id_red : forall N N',  tuple_red1 N N' -> tuple_red1 (App (Abs (Ref 0 Unit)) N) N'
  | beta_const_red : forall i N, tuple_red1 (App (Abs (Ref (S i) Unit)) N) (Ref i Unit)
  | beta_pair_red : forall i M M' N N' P P', 
                      tuple_red1 M M' -> tuple_red1 N N' -> tuple_red1 P P' ->
                      tuple_red1 (App (Abs (Ref i (Pair P M))) N) 
                                 (App (App (Abs (Ref i P')) N') (App (Abs M') N'))
  | beta_abs_red : forall M M' N N',
                     tuple_red1 M M' -> tuple_red1 N N' -> 
                     tuple_red1 (App (Abs (Abs M)) N) 
                               (Abs (App (Abs  (swap 0 M')) (lift N')))
.

Hint Constructors tuple_red1. 

Definition tuple_red := multi_step tuple_red1. 


Lemma refl_tuple_red1: reflective tuple_red1. 
Proof. red. induction M; split_all. Qed. 

Hint Resolve refl_tuple_red1. 

Lemma preserves_unit_tuple_red: 
forall red M N, multi_step red M N -> red = tuple_red1 -> M = Unit -> N = Unit. 
Proof. intros red M N r; induction r; split_all; subst. inversion H; subst. auto. Qed. 

Lemma preserves_pair_tuple_red: 
forall M M' N N', tuple_red M M' -> tuple_red N N' -> tuple_red (Pair M N) (Pair M' N').
Proof. 
intros. apply transitive_red with (Pair M' N). 
eapply2 preserves_pairl_multi_step. red; split_all. 
eapply2 preserves_pairr_multi_step. red; split_all. 
Qed. 

Lemma preserves_ref_tuple_red: 
forall red M M', multi_step red M M' -> red = tuple_red1 -> 
forall i, tuple_red (Ref i M) (Ref i M').
Proof.
intros red M M' r; induction r; split_all; subst. eapply2 zero_red. 
eapply succ_red. eapply ref_tuple_red.  eexact H. eapply2 IHr. 
Qed. 

Lemma preserves_appl_tuple_red: 
forall red M M' N, multi_step red M M' -> red = tuple_red1 -> tuple_red (App M N) (App M' N).
Proof. 
intros red M M' N r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (App N0 N).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_appr_tuple_red: 
forall red M N N', multi_step red N N' -> red = tuple_red1 -> tuple_red (App M N) (App M N').
Proof. 
intros red M N N' r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (App M N).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_app_tuple_red: 
forall M M' N N', tuple_red M M' -> tuple_red N N' -> tuple_red (App M N) (App M' N').
Proof. 
intros. apply transitive_red with (App M' N). 
eapply2 preserves_appl_tuple_red. 
eapply2 preserves_appr_tuple_red. 
Qed. 

Lemma preserves_abs_tuple_red: 
forall red M M', multi_step red M M' -> red = tuple_red1 -> tuple_red (Abs M) (Abs M').
Proof. 
intros red M M' r; induction r; split_all; subst. eapply2 zero_red. 
apply succ_red with (Abs N).  auto. eapply2 IHr. 
Qed. 

Lemma preserves_unit2_tuple_red: 
forall red P1 P2, multi_step red P1 P2 -> red = tuple_red1 -> 
P1 = Unit -> P2 = Unit. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
inversion H; subst. eapply2 IHr. 
Qed. 

Lemma preserves_pair2_tuple_red: 
forall red P1 P2, multi_step red P1 P2 -> red = tuple_red1 -> 
forall M1 N1, P1 = Pair M1 N1 -> 
exists M2 N2, P2 = Pair M2 N2 /\ tuple_red M1 M2 /\ tuple_red N1 N2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist M1; exist N1; eapply2 zero_red. 
inversion H; subst. 
assert(exists M2 N2 : lambda,
          P = Pair M2 N2 /\ tuple_red M' M2 /\ tuple_red N' N2). eapply2 IHr. 
split_all; subst. exist x; exist x0; eapply2 succ_red. 
Qed. 

Lemma preserves_ref2_tuple_red: 
forall red P1 P2, multi_step red P1 P2 -> red = tuple_red1 -> 
forall i s1, P1 = Ref i s1 -> 
exists s2, P2 = Ref i s2 /\ tuple_red s1 s2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist s1; eapply2 zero_red. 
inversion H; subst. 
assert( exists s2 : lambda, P = Ref i s2 /\ tuple_red M' s2).  eapply2 IHr. 
split_all; subst. exist x; eapply2 succ_red. 
Qed. 

Lemma preserves_abs2_tuple_red: 
forall red P1 P2, multi_step red P1 P2 -> red = tuple_red1 -> 
forall t1, P1 = Abs t1 -> 
exists t2, P2 = Abs t2 /\ tuple_red t1 t2. 
Proof. 
intros red P1 P2 r; induction r; split_all; subst. 
exist t1; eapply2 zero_red. 
inversion H; subst. 
assert( exists t2 : lambda, P = Abs t2 /\ tuple_red M' t2).  eapply2 IHr. 
split_all; subst. exist x; eapply2 succ_red. 
Qed. 

Lemma lift_rec_preserves_tuple_red1: 
forall M N, tuple_red1 M N -> forall k, tuple_red1 (lift_rec M k) (lift_rec N k).
Proof.
intros M N r; induction r; split_all. 
(* 2 *) 
rewrite relocate_succ. auto. 
unfold lift. rewrite lift_lift_rec.
rewrite lift_rec_preserves_swap. 
eapply2 beta_abs_red. 
omega. omega. 
Qed. 

Lemma swap_preserves_tuple_red1: 
forall M N, tuple_red1 M N -> forall j, tuple_red1 (swap j M) (swap j N). 
Proof.
intros M N r; induction r; split_all. 
(* 5 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S j) i); split_all; try noway. elim a; split_all; try noway. 
(* 4 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S j) i); split_all; try noway. elim a; split_all; try noway. 
(* 3 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S i) (S j)); split_all; try noway. elim a1; split_all; try noway. 
subst; elim(compare (S j) (S j)); split_all; try noway. elim a0; split_all; try noway. 
elim(compare (S i) (S j)); split_all; try noway. elim a; split_all; try noway. 
elim(compare (S (S j)) (S i)); split_all; try noway. elim a; split_all; try noway. 
elim(compare (S j) i); split_all; try noway. elim a1; split_all; try noway. 
elim(compare (S j) i); split_all; try noway. elim a0; split_all; try noway. 
(* 2 *) 
elim(compare i (S j)); split_all. elim a; split_all. 
elim(compare (S (S j)) i); split_all; try noway. elim a; split_all; try noway. 
(* 1 *) 
rewrite swap_swap; try omega. 
cut(swap (S j) (lift N') = lift (swap j N')).  
intro c; rewrite c; auto. 
unfold lift. 
cut(forall j k, k<= j -> swap (S j) (lift_rec N' k) = lift_rec (swap j N') k). 
split_all. eapply2 H. omega. 
(* 1 *) 
clear. induction N'; split_all. 
(* 4 *) 
rewrite IHN'1; split_all; rewrite IHN'2; split_all. 
(* 3 *) 
unfold relocate. elim(test k n); split_all. 
elim(compare (S n) (S j)); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare n j); split_all; try noway. 
elim a2; split_all; try noway. 
unfold relocate; try noway. 
elim(test k n); split_all; try noway. 
rewrite IHN'; split_all. 
elim(compare n j); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate; try noway. 
elim(test k (S n)); split_all; try noway.
rewrite IHN'; split_all. 
elim(compare n j); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (S j) n); split_all; try noway. 
elim a0; split_all; try noway. 
unfold relocate. elim(test k n); split_all. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim a3; split_all; try noway. 
rewrite IHN'; split_all. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate. elim(test k j); split_all; try noway. 
rewrite IHN'; split_all. 
elim(compare n j); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare n (S j)); split_all; try noway. 
elim a1; split_all; try noway. 
rewrite IHN'; split_all. 
unfold relocate. elim(test k n); split_all; try noway. 
(* 2 *) 
rewrite IHN'; split_all. omega. 
(* 1 *) 
rewrite IHN'1; split_all. rewrite IHN'2; split_all. 
Qed. 


Lemma diamond_tuple_red1 : diamond tuple_red1 tuple_red1. 
Proof. 
red. induction M; split_all. 
(* 5 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
(* 4 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
elim(IHM1 M' M'0); split_all. 
elim(IHM2 N' N'0); split_all.  exist (Pair x x0). 
(* 3 *) 
inversion H0; inversion H; subst; eauto; try discriminate. 
elim(IHM M' M'0); split_all. eauto. 
(* 2 *) 
inversion H; subst.    inversion H0; subst; eauto; try discriminate. 
elim(IHM M'0 M'); split_all; eauto. 
(* 1 *) 
inversion H; subst;   inversion H0; subst; eauto; try discriminate. 
(* 14 *) 
elim(IHM1 M' M'0); split_all; eauto. 
elim(IHM2 N' N'0); split_all; eauto. 
(* 13 *) 
inversion H3; subst; eauto. 
elim(IHM1 (Ref i M'0) (Ref i M'1)); split_all. 
elim(IHM2 N' N'0); split_all. 
inversion H2; inversion H6; subst. 
inversion H15; subst.
exist(Ref i (Pair M' x0)). 
(* 12 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. inversion H8; subst; eauto. 
elim(IHM2 N' P); split_all. eauto. 
(* 11 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. inversion H7; subst; eauto. 
(* 10 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. inversion H10; subst; eauto. 
elim(IHM1 (Abs (Ref i (Pair P' M'0)))(Abs (Ref i (Pair M'1 N'1)))); split_all. 
elim(IHM2 N' N'0); split_all. 
inversion H7; inversion H11; subst. 
inversion H15; inversion H18; subst. 
inversion H20; inversion H24; subst. 
invsub. 
exist(App (App (Abs (Ref i M')) x0) (App (Abs N'2) x0)).
(* 9 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. 
elim(IHM1 (Abs (Abs M')) (Abs (Abs M'0))); split_all. 
inversion H8; inversion H9; subst. 
inversion H10; inversion H13; subst; invsub. 
elim(IHM2 N' N'0); split_all. 
exist(Abs (App (Abs (swap 0 M'3)) (lift x))). 
eapply2 abs_tuple_red. eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1. 
unfold lift. eapply2 lift_rec_preserves_tuple_red1. 
(* 8 *) 
inversion H4; subst. 
elim(IHM1 (Ref i M') (Ref i M'1)); split_all. 
inversion H2; inversion H6; subst. invsub. 
elim(IHM2 N' N'0); split_all. 
exist(Ref i (Pair M'0 x)). 
(* 7 *) 
elim(IHM1 (Ref i M') (Ref i M'0)); split_all. 
inversion H2; inversion H4; subst. invsub. 
elim(IHM2 N' N'0); split_all. 
exist(Ref i (Pair M'1 x)). 
(* 6 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. inversion H8; subst; eauto. 
elim(IHM2 N N'); split_all. 
exist x. 
(* 5 *) 
inversion H3; subst; eauto. inversion H2; subst; eauto. inversion H7; subst; eauto.
(* 4 *) 
inversion H5; subst; eauto. inversion H2; subst; eauto. inversion H10; subst; eauto. 
elim(IHM1  (Abs (Ref i (Pair P' M'))) (Abs (Ref i (Pair M'1 N'1)))); split_all. 
inversion H7; inversion H11; subst. 
inversion H13; inversion H16; subst. 
inversion H18; inversion H22; subst. 
invsub. 
elim(IHM2 N' N'0); split_all.
exist( (App (App (Abs (Ref i M'0)) x) (App (Abs N'2) x))). 
(* 3 *) 
elim(IHM1  (Abs (Ref i (Pair P' M'))) (Abs (Ref i (Pair P'0 M'0)))); split_all. 
inversion H2; inversion H5; subst. 
inversion H7; inversion H13; subst. 
inversion H15; inversion H19; subst. 
invsub. 
elim(IHM2 N' N'0); split_all.
exist( (App (App (Abs (Ref i M'1)) x) (App (Abs N'1) x))). 
(* 2 *) 
inversion H4; subst; eauto. inversion H2; subst; eauto. 
elim(IHM1 (Abs (Abs M')) (Abs (Abs M'0))); split_all. 
inversion H8; inversion H9; subst. 
inversion H10; inversion H13; subst. 
invsub. 
elim(IHM2 N' N'0); split_all.
exist( (Abs (App (Abs (swap 0 M'3)) (lift x))) ). 
eapply2 abs_tuple_red. eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1.  
unfold lift.  eapply2 lift_rec_preserves_tuple_red1. 
(* 1 *) 
elim(IHM1 (Abs (Abs M')) (Abs (Abs M'0))); split_all. 
inversion H2; inversion H6; subst. 
inversion H8; inversion H11; subst. 
invsub. 
elim(IHM2 N' N'0); split_all.
exist( (Abs (App (Abs (swap 0 M'3)) (lift x))) ). 
eapply2 abs_tuple_red. eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1. 
unfold lift; eapply2 lift_rec_preserves_tuple_red1.  
eapply2 abs_tuple_red. eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1. 
unfold lift; eapply2 lift_rec_preserves_tuple_red1.  
Qed. 

(* Confluence *)

Definition confluence (A : Set) (R : A -> A -> Prop) :=
  forall x y : A,
  R x y -> forall z : A, R x z -> exists u : A, R y u /\ R z u.

Theorem tuple_parallel_confluence: confluence lambda tuple_red. 
Proof. red. eapply2 diamond0_tiling. eapply2 diamond_iff_diamond0. eapply2 diamond_tuple_red1. Qed.

(* sequential reduction *)



Inductive seq_red1 : lambda -> lambda -> Prop := 
  | pairl_seq_red :  forall M M' N, seq_red1 M M' -> seq_red1 (Pair M N) (Pair M' N)
  | pairr_seq_red :  forall M N N', seq_red1 N N' -> seq_red1 (Pair M N) (Pair M N')
  | ref_seq_red : forall i M M' ,  seq_red1 M M' -> seq_red1 (Ref i M) (Ref i M')
  | abs_seq_red :  forall M M', seq_red1 M M' -> seq_red1 (Abs M) (Abs M') 
  | appl_seq_red :  forall M M' N, seq_red1 M M' -> seq_red1 (App M N) (App M' N)
  | appr_seq_red :  forall M N N', seq_red1 N N' -> seq_red1 (App M N) (App M N')
  | ref_app_seq_red : forall i M N, seq_red1 (App (Ref i M) N) (Ref i (Pair M N))
  | beta_id_seq_red : forall N, seq_red1 (App (Abs (Ref 0 Unit)) N) N
  | beta_const_seq_red : forall i N, seq_red1 (App (Abs (Ref (S i) Unit)) N) (Ref i Unit)
  | beta_pair_seq_red : forall i M N P, 
                      seq_red1 (App (Abs (Ref i (Pair P M))) N) 
                                 (App (App (Abs (Ref i P)) N) (App (Abs M) N))
  | beta_abs_seq_red : forall M N, seq_red1 (App (Abs (Abs M)) N) 
                               (Abs (App (Abs (swap 0 M)) (lift N)))
.


Definition seq_red := multi_step seq_red1. 

Hint Constructors seq_red1 .


Lemma reflective_seq_red: reflective seq_red. 
Proof. red; red; reflect. Qed. 
Hint Resolve reflective_seq_red.


Lemma preserves_pairl_seq_red: preserves_pairl seq_red. 
Proof. eapply2 preserves_pairl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_pairl_seq_red.

Lemma preserves_pairr_seq_red: preserves_pairr seq_red. 
Proof. eapply2 preserves_pairr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_pairr_seq_red.


Lemma preserves_pair_seq_red: preserves_pair seq_red. 
Proof. 
red; split_all. 
apply transitive_red with (Pair M' N); split_all. 
eapply2 preserves_pairl_seq_red. 
eapply2 preserves_pairr_seq_red. 
Qed. 
Hint Resolve preserves_pair_seq_red.



Lemma preserves_apl_seq_red: preserves_apl seq_red. 
Proof. eapply2 preserves_apl_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apl_seq_red.

Lemma preserves_apr_seq_red: preserves_apr seq_red. 
Proof. eapply2 preserves_apr_multi_step. red; split_all.  Qed.
Hint Resolve preserves_apr_seq_red.

Lemma preserves_app_seq_red: preserves_app seq_red. 
Proof. 
red; split_all. 
apply transitive_red with (App M' N); split_all. 
eapply2 preserves_apl_seq_red. 
eapply2 preserves_apr_seq_red. 
Qed. 
Hint Resolve preserves_app_seq_red.


Lemma preserves_abs_seq_red: preserves_abs seq_red. 
Proof. eapply2 preserves_abs_multi_step. red; split_all.  Qed. 

Hint Resolve preserves_app_seq_red preserves_abs_seq_red.


Lemma preserves_ref_seq_red: preserves_ref seq_red. 
Proof. eapply2 preserves_ref_multi_step. red; split_all.  Qed. 

Hint Resolve preserves_ref_seq_red.


Lemma seq_red1_to_tuple_red1 : implies_red seq_red1 tuple_red1. 
Proof.  red. intros M N B; induction B; split_all; try (red; one_step; fail). Qed. 


Lemma seq_red_to_tuple_red: implies_red seq_red tuple_red. 
Proof.
  eapply2 implies_red_multi_step. red; split_all; one_step; eapply2 seq_red1_to_tuple_red1.
Qed. 



Lemma to_seq_red_multi_step: forall red, implies_red red seq_red -> implies_red (multi_step red) seq_red. 
Proof. 
red.  intros red B M N R; induction R; split_all.
red; split_all. 
assert(seq_red M N) by eapply2 B. 
apply transitive_red with N; auto. 
eapply2 IHR. 
Qed. 

Hint Resolve preserves_app_seq_red preserves_abs_seq_red. 

Lemma lift_rec_preserves_seq_red1: 
forall M N, seq_red1 M N -> forall n, seq_red1 (lift_rec M n) (lift_rec N n).
Proof.
intros M N r; induction r; split_all. 
rewrite relocate_succ. auto. 
unfold lift; rewrite lift_lift_rec. 
rewrite lift_rec_preserves_swap. eapply2 beta_abs_seq_red. omega. omega. 
Qed. 

Lemma lift_rec_preserves_seq_red: 
forall red M N, multi_step red M N -> red = seq_red1 -> 
forall n, seq_red (lift_rec M n) (lift_rec N n).
Proof.
intros red M N r; induction r; split_all; subst. 
eapply succ_red. eapply lift_rec_preserves_seq_red1. eexact H. eapply2 IHr. 
Qed. 


Lemma swap_preserves_seq_red1: 
forall M N, seq_red1 M N -> forall j, seq_red1 (swap j M) (swap j N). 
Proof.
intros M N r; induction r; split_all. 
(* 5 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S j) i); split_all; try noway. elim a; split_all; try noway. 
(* 4 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S j) i); split_all; try noway. elim a; split_all; try noway. 
(* 3 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S i) (S j)); split_all; try noway. elim a1; split_all; try noway. 
subst; elim(compare (S j) (S j)); split_all; try noway. elim a0; split_all; try noway. 
elim(compare (S i) (S j)); split_all; try noway. elim a; split_all; try noway. 
elim(compare (S (S j)) (S i)); split_all; try noway. elim a; split_all; try noway. 
elim(compare (S j) i); split_all; try noway. elim a1; split_all; try noway. 
elim(compare (S j) i); split_all; try noway. elim a0; split_all; try noway. 
(* 2 *) 
elim(compare i (S j)); split_all. elim a; split_all. 
elim(compare (S (S j)) i); split_all; try noway. elim a; split_all; try noway. 
(* 1 *) 
rewrite swap_swap; try omega. 
cut(swap (S j) (lift N) = lift (swap j N)).  
intro c; rewrite c; auto. 
unfold lift. 
cut(forall j k, k<= j -> swap (S j) (lift_rec N k) = lift_rec (swap j N) k). 
split_all. eapply2 H. omega. 
(* 1 *) 
clear. induction N; split_all. 
(* 4 *) 
rewrite IHN1; split_all; rewrite IHN2; split_all. 
(* 3 *) 
unfold relocate. elim(test k n); split_all. 
elim(compare (S n) (S j)); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare n j); split_all; try noway. 
elim a2; split_all; try noway. 
unfold relocate; try noway. 
elim(test k n); split_all; try noway. 
rewrite IHN; split_all. 
elim(compare n j); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate; try noway. 
elim(test k (S n)); split_all; try noway.
rewrite IHN; split_all. 
elim(compare n j); split_all; try noway. 
elim a0; split_all; try noway. 
elim(compare (S j) n); split_all; try noway. 
elim a0; split_all; try noway. 
unfold relocate. elim(test k n); split_all. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim a3; split_all; try noway. 
rewrite IHN; split_all. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim(compare (S (S j)) (S n)); split_all; try noway. 
elim a1; split_all; try noway. 
unfold relocate. elim(test k j); split_all; try noway. 
rewrite IHN; split_all. 
elim(compare n j); split_all; try noway. 
elim a; split_all; try noway. 
elim(compare n (S j)); split_all; try noway. 
elim a1; split_all; try noway. 
rewrite IHN; split_all. 
unfold relocate. elim(test k n); split_all; try noway. 
(* 2 *) 
rewrite IHN; split_all. omega. 
(* 1 *) 
rewrite IHN1; split_all. rewrite IHN2; split_all. 
Qed. 

Lemma swap_preserves_seq_red: 
forall red M N, multi_step red M N -> red = seq_red1 -> 
forall j, seq_red (swap j M) (swap j N). 
Proof.
intros red M N r; induction r; split_all; subst. eapply succ_red. 
eapply2 swap_preserves_seq_red1. eapply2 IHr. 
Qed.



Lemma tuple_red1_to_seq_red: implies_red tuple_red1 seq_red .
Proof. 
  red.  intros M N OR; induction OR; split_all; eapply2 succ_red;
        try eapply2 preserves_ref_seq_red;
        try eapply2 preserves_pair_seq_red;
        try eapply2 preserves_abs_seq_red; 
        try eapply2 preserves_app_seq_red; 
        try eapply2 preserves_aps_seq_red.
eapply2 preserves_abs_seq_red. 
eapply2 swap_preserves_seq_red. 
unfold lift. eapply2 lift_rec_preserves_seq_red. 
Qed.

Hint Resolve tuple_red1_to_seq_red.

Lemma tuple_red_to_seq_red: implies_red tuple_red seq_red. 
Proof. eapply2 to_seq_red_multi_step. Qed.


Lemma diamond_seq_red: diamond seq_red seq_red. 
Proof. 
red; split_all. 
assert(tuple_red M N) by eapply2 seq_red_to_tuple_red.  
assert(tuple_red M P) by eapply2 seq_red_to_tuple_red.  
elim(tuple_parallel_confluence M N H1 P); split_all. 
exist x; eapply2 tuple_red_to_seq_red. 
Qed. 


Theorem tuple_confluence: confluence lambda seq_red. 
Proof. red. split_all. eapply2 diamond_seq_red. Qed.

