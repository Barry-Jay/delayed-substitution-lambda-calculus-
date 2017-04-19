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
(*                Delayed Substitution Lambda Calculu                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                    Delayed_standardisation.v                       *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Omega Test Delayed_Terms Delayed_Tactics Delayed_reduction Delayed_Normal.

(* standardisation via head reduction *)

Inductive hnf_tuple: lambda -> Prop := 
| hnft_unit : hnf_tuple Unit 
| hnft_pair : forall s t, hnf_tuple s -> hnf_tuple (Pair s t)
.

Inductive hnf: lambda -> Prop := 
| hnf_ref : forall i s, hnf_tuple s -> hnf (Ref i s)
| hnf_abs : forall t, hnf t -> hnf (Abs t)
.

Hint Constructors hnf_tuple hnf . 


Lemma swap_preserves_hnf_tuple :
forall M, hnf_tuple M -> forall j, hnf_tuple (swap j M). 
Proof. intros M h; induction h; split_all. Qed. 

Lemma swap_preserves_hnf :
forall M, hnf M -> forall j, hnf (swap j M). 
Proof.
intros M h; induction h; split_all. 
elim(compare i j); split_all. elim a; split_all; eapply2 hnf_ref;
eapply2 swap_preserves_hnf_tuple. 
elim(compare (S j) i); split_all. elim a; split_all; eapply2 hnf_ref;
eapply2 swap_preserves_hnf_tuple. eapply2 hnf_ref;
eapply2 swap_preserves_hnf_tuple. 
Qed. 

Lemma nf_implies_hnf_tuple : forall st s, normal st s -> st = Tuple -> hnf_tuple s. 
Proof. intros st s nf; induction nf; split_all; subst; inversion H; subst; eauto. Qed. 

Lemma nf_implies_hnf : forall st t, normal st t -> st = Term -> hnf t . 
Proof. 
intros t nf; induction nf; split_all; subst; inversion H; subst; eauto. 
eapply2 hnf_ref. eapply2 nf_implies_hnf_tuple. 
Qed. 


Fixpoint head_tuple t :=
(* t is assumed to be a well-formed tuple *) 
  match t with 
| Unit => Unit 
| Pair s u => Pair (head_tuple s) u 
| _ => t 
end
. 
 

Fixpoint head_app t u := 
match t with 
| Abs t1 => 
  match t1 with 
    | Ref 0 Unit => u 
    | Ref (S i) Unit => Ref i Unit
    | Ref i (Pair s t1) => (App (App (Abs (Ref i s)) u) (App (Abs t1) u))
    | Abs t2 =>  Abs (App (Abs (swap 0 t2)) (lift u))
    | _ => App t u 
  end
| Ref i s => Ref i (Pair s u)
| _ => App t u 
end. 

Inductive head : nat -> termred :=
| hd_ref : forall i s, head 0 (Ref i s) (Ref i (head_tuple s))
| hd_abs : forall n t v, head n t v ->  head n (Abs t) (Abs v) 
| hd_app: forall n1 t1 v1,  head n1 t1 v1 -> 
          forall n2 t2 v, head n2 (head_app v1 t2) v -> head (S (n1+n2)) (App t1 t2) v 
.

Hint Constructors head . 




Lemma head_tuple_is_hnf_tuple: 
forall st t, well_formed st t -> st = Tuple -> hnf_tuple (head_tuple t). 
Proof. 
intros st t wf; induction wf; split_all; subst.
Qed. 


Lemma head_tuple_preserves_well_formed: 
forall st t, well_formed st t -> st = Tuple -> well_formed Tuple (head_tuple t). 
Proof.
intros t wf; induction wf; split_all; subst; inversion H; subst; eauto.
Qed. 



Lemma head_app_preserves_well_formed: 
forall t1, forall t2, well_formed Term t1 -> well_formed Term t2 -> 
well_formed Term (head_app t1 t2). 
Proof.
induction t1; split_all; inversion H; subst; split_all. 
inversion H2; subst. 
case i; split_all; inversion H1; subst; auto. 
eapply2 wf_abs. eapply2 wf_app. eapply2 wf_abs.  eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
eapply2 wf_app. 
Qed. 



Lemma head_is_hnf: 
forall st n t v, well_formed st t -> head n t v -> hnf v /\ well_formed Term v /\ st = Term. 
Proof. 
intros st n t v wf e; induction e; inversion wf; subst; split_all. 
(* 6 *) 
eapply2 hnf_ref. eapply2 head_tuple_is_hnf_tuple. 
eapply2 wf_ref. eapply2 head_tuple_preserves_well_formed. 
(* 4 *) 
eapply2 hnf_abs.  eapply2 IHe. eapply2 wf_abs.  eapply2 IHe. 
(* 2 *) 
 eapply2 IHe2. eapply2 (head_app_preserves_well_formed). eapply2 IHe1. 
(* 1 *) 
 eapply2 IHe2. eapply2 (head_app_preserves_well_formed).  eapply2 IHe1. 
Qed. 


Lemma head_tuple_of_hnf_tuple: forall n, hnf_tuple n -> head_tuple n = n.
Proof. intros n nf; induction nf; split_all. Qed. 

Lemma head_of_hnf: forall n, hnf n -> head 0 n n.
Proof. intros n nf; induction nf; split_all. 
assert (head_tuple s = s). eapply2  head_tuple_of_hnf_tuple. rewrite <- H0 at 2. 
eapply2 hd_ref. 
Qed. 




Lemma head_app_head_reduces : forall t u, tuple_red (App t u) (head_app t u). 
Proof. 
induction t; split_all; try (eapply2 zero_red; fail); try red; try (one_step; fail). 
case t; split_all; try one_step. case l; split_all; case n; split_all. 
Qed. 


Lemma head_tuple_reduces : forall t, tuple_red t (head_tuple t). 
Proof. 
intros t; induction t; split_all; 
try (eapply2 zero_red; fail); try red; try (one_step; fail). 
eapply2 preserves_pair_tuple_red. eapply2 zero_red. 
Qed. 


Lemma head_reduces : forall n t v, head n t v -> tuple_red t v. 
Proof. 
intros n t v e; induction e; split_all; 
try (eapply2 zero_red; fail); try red; try (one_step; fail). 
(* 3 *) 
eapply preserves_ref_tuple_red.  2: eauto. eapply2 head_tuple_reduces. 
(* 2 *) 
 eapply2 preserves_abs_tuple_red.  
(* 1 *) 
eapply transitive_red. eapply preserves_app_tuple_red.  eexact IHe1. eapply2 zero_red. 
eapply transitive_red. eapply2 head_app_head_reduces. auto. 
Qed. 


Lemma head_is_functional: 
forall n1 t v1, head n1 t v1 -> forall n2 v2, head n2 t v2 -> n1 = n2 /\ v1 = v2. 
Proof.
intros n1 t v1 e; induction e; intros; 
try (inversion H; subst; auto; rewrite (IHe v0); split_all; fail). 
(* 2 *)  
inversion H; subst; auto.
assert(n = n2 /\ v = v0) by eapply2 IHe; subst.
split_all; subst. 
(* 1 *) 
inversion H; subst; auto.
assert(n1 = n3 /\ v1 = v0) by eapply2 IHe1. inversion H0; subst. 
assert(n2 = n4 /\ v = v2) by eapply2 IHe2. split_all. 
Qed. 



Lemma head_tuple_preserves_tuple_red1: 
forall t u, well_formed Tuple t -> tuple_red1 t u -> tuple_red1 (head_tuple t) (head_tuple u).
Proof.
intros t u wf r; induction r; inversion wf; subst; split_all; eauto. 
Qed. 

(* delete ??
Lemma head_app_preserves_tuple_red1: 
  forall t t1, well_formed Term t -> tuple_red1 t t1 ->
  forall u u1, tuple_red1 u u1 ->  well_formed Term u -> 
               tuple_red1 (head_app t u) (head_app t1 u1) . 
Proof.
induction t; split_all; inversion H; subst; split_all;
try (inversion H0; subst; split_all; fail). 
(* 2 *) 
inversion H0; subst; split_all.  inversion H4; subst. 
(* 4 *) 
inversion H5; subst; split_all. 
case i; split_all; inversion H3; subst; split_all; inversion H9; subst;   auto. 
(* 3 *) 
inversion H4; subst; split_all. inversion H5; subst; split_all. 
eapply2 abs_tuple_red. eapply2 app_tuple_red. 
unfold lift; eapply2 lift_rec_preserves_tuple_red1. 
(* 2 *) 
case i; split_all; inversion H3; subst; split_all; inversion H9; subst;   auto. 
(* 1 *) 
inversion H4; subst; auto.  
eapply2 abs_tuple_red. eapply2 app_tuple_red. 
unfold lift. eapply2 lift_rec_preserves_tuple_red1. 
Qed. 

*) 


Lemma head_app_preserves_tuple_red1: 
  forall t, hnf t -> forall t1, tuple_red1 t t1 ->
  forall u u1, tuple_red1 u u1 ->  well_formed Term u -> 
               tuple_red1 (head_app t u) (head_app t1 u1) . 
Proof.
induction t; split_all; inversion H0; subst; split_all; inversion H; subst. 
inversion H5; subst; split_all. 
(* 2 *) 
inversion H4; subst. 
case i; split_all; 
inversion H3; subst; split_all; inversion H9; subst;   auto. 
(* 1 *) 
inversion H4; subst; auto.  
eapply2 abs_tuple_red. eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1. 
unfold lift. eapply2 lift_rec_preserves_tuple_red1. 
Qed. 


Lemma head_tuple_of_swap: 
forall j M, head_tuple(swap j M) = swap j (head_tuple M). 
Proof.
induction M; split_all. 
elim(compare n j); split_all. elim a; split_all. 
elim(compare (S j) n); split_all. elim a; split_all. 
Qed. 


Lemma head_app_of_swap: 
forall M, well_formed Term M -> forall N j, well_formed Term N -> 
head_app (swap j M) (swap j N) = swap j (head_app M N). 
Proof. 
intros M wf; induction wf; split_all. 
(* 2 *) 
elim(compare i j); split_all. elim a; split_all. 
elim(compare (S j) i); split_all; try noway. elim a; split_all. 
(* 1 *) 
gen2_case wf IHwf M. 
(* 2 *) 
inversion wf; subst. 
elim(compare n (S j)); split_all. elim a; split_all.  
(* 4 *) 
gen2_case IHwf a0 n. 
gen_case IHwf l. 
elim(compare n0 (S j)); split_all; try noway. elim a1; split_all; try noway.  
elim(compare (S(S j)) n0); split_all; try noway. elim a1; split_all; try noway.  
gen2_case H2 IHwf l; inversion H2; subst. 
elim(compare n0 (S j)); split_all; try noway. 
elim(compare n0 j); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S n0) (S j)); split_all; try noway. 
elim a1; split_all; try noway. subst.
(* 3 *) 
gen2_case IHwf H2 l. 
(* 7 *) 
elim(compare j j); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S j) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare n (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S j) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
(* 6 *) 
elim(compare (S j) (S j)); split_all; try noway. subst. 
elim a1; split_all; try noway.  
elim(compare (S(S j)) n); split_all. elim a0; split_all; try noway.  
elim(compare (S j) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S j) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
(* 5 *) 
elim(compare (S j) (S j)); split_all; try noway. 
(* 4 *) 
elim(compare (S j) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
(* 3 *) 
elim(compare (S j) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
(* 2 *) 
elim(compare (S(S j)) n); split_all; try noway. 
elim a; split_all; try noway.  
replace n with (S (pred n)) by omega. 
gen2_case IHwf H2 l. 
(* 7 *) 
elim(compare (pred n) j); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S j) (pred n)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (pred n)) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a1; split_all; try noway.  
(* 5 *) 
elim(compare n0 (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S(pred n)) (S j)); split_all; try noway. 
elim a3; split_all; try noway.  
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a3; split_all; try noway.  
elim(compare (S (pred n)) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) n0); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (pred n)) (S j)); split_all; try noway. 
elim a3; split_all; try noway.  
(* 5 *) 
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a3; split_all; try noway. 
elim(compare (S (pred n)) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
(* 3 *) 
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a2; split_all; try noway.  
(* 2 *) 
elim(compare (S(pred n)) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a1; split_all; try noway.  
(* 3 *) 
elim(compare (S(pred n)) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) (S (pred n))); split_all; try noway. 
elim a1; split_all; try noway.  
subst. 
gen2_case IHwf H2 l. 
(* 6 *) 
elim(compare (S j) j); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S j) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
(* 5 *) 
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a0; split_all; try noway.  
(* 4 *) 
elim(compare n (S j)); split_all; try noway. elim a0; split_all; try noway. 
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) n); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a2; split_all; try noway.  
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a1; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a1; split_all; try noway.  
(* 3 *) 
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S (S j)) (S j)); split_all; try noway. 
elim a0; split_all; try noway.  
elim(compare (S (S j)) (S (S j))); split_all; try noway. 
elim a0; split_all; try noway.  
(* 1 *) 
inversion wf; subst. 
rewrite <- swap_swap. 
unfold lift. rewrite lift_rec_preserves_swap2. auto. omega. omega. 
Qed. 


Lemma head_reflects_swap: 
forall n M v, head n M  v -> 
forall j M0, M = swap j M0 -> well_formed Term M0 -> 
exists v0, v = swap j v0 /\ head n M0 v0.
Proof.
intros n M v h; induction h; split_all. 
(* 3 *) 
gen2_case H H0 M0; split_all. 
generalize H; elim(compare n j); split_all. 
generalize H1; elim a; split_all. 
(* 5 *) 
inversion H2; subst. 
rewrite head_tuple_of_swap. 
exist(Ref n (head_tuple l)). 
elim(compare n j); split_all; try noway.
elim a1; split_all; try noway.
(* 4 *) 
inversion H2; subst. 
exist(Ref j (head_tuple l)). 
elim(compare j j); split_all; try noway.
elim a0; split_all; try noway.
rewrite head_tuple_of_swap. auto. 
(* 3 *) 
generalize H1. elim(compare (S j) n); split_all; try noway. 
generalize H2. elim a; split_all; try noway. 
inversion H3; subst. 
exist (Ref n (head_tuple l)). 
elim(compare n j); split_all; try noway.
elim a1; split_all; try noway.
elim(compare (S j) n); split_all; try noway. 
elim a1; split_all; try noway. 
rewrite head_tuple_of_swap. auto. 
inversion H3; subst. 
exist (Ref (S j) (head_tuple l)). 
elim(compare (S j) j); split_all; try noway.
elim a0; split_all; try noway.
elim(compare (S j) (S j)); split_all; try noway.
elim a0; split_all; try noway.
rewrite head_tuple_of_swap. auto. 
(* 2 *) 
gen2_case H H0 M0. 
generalize H. elim(compare n0 j); split_all; try noway. 
generalize H1. elim a; split_all; try noway. 
generalize H1. elim(compare (S j) n0); split_all; try noway. 
generalize H2. elim a; split_all; try noway. 
inversion H; subst. 
elim(IHh (S j) l); split_all. subst. 
exist (Abs x). 
inversion H0; subst. auto. 
(* 1 *) 
gen2_case H H0 M0. 
generalize H. elim(compare n j); split_all; try noway. 
generalize H1. elim a; split_all; try noway. 
generalize H1. elim(compare (S j) n); split_all; try noway. 
generalize H2. elim a; split_all; try noway. 
inversion H; subst. 
inversion H0; subst. 
elim(IHh1 j l); split_all. subst. 
rewrite head_app_of_swap in IHh2; split_all. 
elim(IHh2 j (head_app x l0)); split_all. subst. 
exist x0. 
eapply2 hd_app. 
eapply2 head_app_preserves_well_formed. eapply2 (head_is_hnf Term n1 l). 
eapply2 (head_is_hnf Term n1 l). 
Qed. 





Lemma tuple_red1_then_head_implies_head_then_tuple_red1: 
  forall n u v, head n u v -> forall t, well_formed Term t -> tuple_red1 t u ->
  exists n1 v1, head n1 t v1 /\ tuple_red1 v1 v.
Proof.
cut(forall p n, n<p -> 
 forall u v, head n u v -> forall t, well_formed Term t -> tuple_red1 t u ->
  exists n1 v1, head n1 t v1 /\ tuple_red1 v1 v).
split_all. eapply2 H. 
induction p. split_all; noway. 
(* 1 *) 
intros n c u v h; induction h; split_all; eauto. 
(* 3 *) 
generalize t s i H H0; clear. induction t; split_all;  inversion H0; subst. 
(* 6 *) 
inversion H; subst. exist 0; exist (Ref i (head_tuple t)). 
eapply2 ref_tuple_red. 
eapply2 head_tuple_preserves_tuple_red1.
(* 5 *) 
inversion H; subst. inversion H3; subst. 
exists (S (0+0)); exists(head_app (Ref i (head_tuple M)) t2). split. 
eapply hd_app. eapply2 hd_ref. 
eapply2 head_of_hnf. eapply2 hnf_ref. eapply2 hnft_pair. 
eapply2 head_tuple_is_hnf_tuple. 
split_all. eapply2 ref_tuple_red. eapply2 pair_tuple_red. 
eapply2 head_tuple_preserves_tuple_red1. 
(* 4 *) 
inversion H; subst. 
elim(IHt2 s i); split_all. 
exists (S(0+x)); exists x0. split. 
eapply2 hd_app. auto. 
(* 3 *) 
exists (S(0+0)); exists (Ref i Unit). split. 
eapply2 hd_app. simpl. eapply2 head_of_hnf. split_all. 
(* 2 *)
assert(forall t0 t1, tuple_red1 t0 t1 -> forall t, t1 = Abs t ->
(forall n : nat,
        n < p ->
        forall u v : lambda,
        head n u v ->
        forall t : lambda,
        well_formed Term t ->
        tuple_red1 t u ->
        exists (n1 : nat) (v1 : lambda), head n1 t v1 /\ tuple_red1 v1 v) -> 
forall n v, head n t v -> n < S p -> 
 well_formed Term t0 -> 
(n < S p ->
        forall t0 : lambda,
        well_formed Term t0 ->
        tuple_red1 t0 t ->
        exists (n1 : nat) (v1 : lambda), head n1 t0 v1 /\ tuple_red1 v1 v) -> 
  exists (n0 : nat) (v0 : lambda), head n0 t0 v0 /\ tuple_red1 v0 (Abs v)).
clear. 
intros t0 t1 r; induction r; split_all; subst; split_all; invsub. 
(* 5 *) 
inversion H3; subst. elim(H4 H2 M); split_all. exist x; exist (Abs x0). 
(* 4 *) 
inversion H3; subst. 
assert(exists (n0 : nat) (v0 : lambda), head n0 N v0 /\ tuple_red1 v0 (Abs v)). 
eapply2 IHr. split_all. 
exists (S (0+x)); exists x0. split. eapply2 hd_app. auto. 
(* 3 *) 
inversion H1; subst. inversion H7; subst. inversion H3; inversion H8;  inversion H12; subst. 
assert(n1<p) by omega. 
assert(exists (n0 : nat) (v1 : lambda), head n0 (swap 0 M) v1 /\ tuple_red1 v1 v0). 
eapply2 (H0 n1 H (swap 0 M') v0). eapply2 swap_preserves_well_formed. 
eapply2 swap_preserves_tuple_red1. split_all.
assert(n2<p) by omega. 
assert(exists (n0 : nat) (v1 : lambda), head n0 (head_app (Abs x0) (lift N)) v1 /\ tuple_red1 v1 v). 
eapply2 (H0 n2 H5  (head_app (Abs v0) (lift N')) v). 
eapply2 head_app_preserves_well_formed. 
eapply2 wf_abs.  eapply2 (head_is_hnf Term x (swap 0 M)).
eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
eapply2 head_app_preserves_tuple_red1.  
eapply2 hnf_abs. eapply2 (head_is_hnf Term x (swap 0 M)). 
eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_tuple_red1. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
split_all. 
exists (S(x+ S(0+x1))); exists (Abs x2). split. 
2: eapply2 abs_tuple_red. 
elim(head_reflects_swap x (swap 0 M) x0 H11 0 M); intros; try (split_all; fail).  
inversion H15; subst. 
eapply hd_app. eapply hd_abs.  eapply hd_abs.  eexact H19. 
unfold head_app; fold head_app. eapply hd_abs. eapply hd_app.  eapply hd_abs.  
eapply2 head_of_hnf. 
eapply2 swap_preserves_hnf. eapply2 (head_is_hnf Term x M). auto.  
(* 2 *) 
eapply2 H1. 
(* end of sub-lemma *) 
(* 1 *) 
cut(forall t0 t, tuple_red1 t0 t -> forall t1 t2, t = App t1 t2 -> forall v, 
(forall n : nat,
        n < p ->
        forall u v : lambda,
        head n u v ->
        forall t : lambda,
        well_formed Term t ->
        tuple_red1 t u ->
        exists (n1 : nat) (v1 : lambda), head n1 t v1 /\ tuple_red1 v1 v) -> 
forall n1 v1, head n1 t1 v1 -> 
forall n2, head n2 (head_app v1 t2) v -> (S (n1+n2)) < S p -> 
 well_formed Term t0 -> 
(n1 < S p ->
         forall t : lambda,
         well_formed Term t ->
         tuple_red1 t t1 ->
         exists (n1 : nat) (v2 : lambda), head n1 t v2 /\ tuple_red1 v2 v1) -> 
(n2 < S p ->
         forall t : lambda,
         well_formed Term t ->
         tuple_red1 t (head_app v1 t2) ->
         exists (n1 : nat) (v1 : lambda), head n1 t v1 /\ tuple_red1 v1 v) -> 
  exists (n0 : nat) (v0 : lambda), head n0 t0 v0 /\ tuple_red1 v0 v).
split_all. eapply2 H1. 
clear. 
intros t0 t r; induction r; split_all; subst; split_all; invsub; inversion H4; subst. 
(* 3 *) 
assert(n1<p) by omega. 
elim(H0 n1 H t1 v1 H1 M); split_all. 
assert(n2<p) by omega. 
elim(H0 n2 H10 (head_app v1 t2) v H2 (head_app x0 N)); split_all. 
exist(S(x+x1)); exist x2. eapply2 hd_app. 
eapply2 head_app_preserves_well_formed. 
eapply2 (head_is_hnf Term x M). 
eapply2 head_app_preserves_tuple_red1. eapply2 (head_is_hnf Term x M). 
(* 2 *) 
assert(exists (n0 : nat) (v0 : lambda), head n0 N v0 /\ tuple_red1 v0 v) by eapply2 IHr. 
split_all. 
exists (S(0+ x)); exists x0. split. eapply2 hd_app. auto. 
(* 1 *) 
inversion H8; subst. inversion H7; subst. inversion H11; subst. 
assert(n1<p) by omega. 
elim(H0 n1 H (App (Abs (Ref i P')) N') v1 H1 (App (Abs (Ref i P)) N)); split_all.
assert(n2<p) by omega. 
elim(H0 n2 H14 (head_app v1 (App (Abs M') N')) v H2  (head_app x0 (App (Abs M) N))); split_all.
exists(S(0+ S(x+x1))); exists x2. split. 
eapply2 hd_app. unfold head_app.
gen_case H10 i.
eapply2 hd_app. inversion H10; subst; split_all. 
inversion H21; subst; split_all. 
inversion H20; subst; split_all. 
replace (S n3) with (S(0+n3)) by omega. eapply2 hd_app. 
replace(head_tuple (head_tuple P)) with (head_tuple P).  auto. 
rewrite (head_tuple_of_hnf_tuple (head_tuple P)). auto. 
eapply2 head_tuple_is_hnf_tuple. 
eapply2 hd_app. 
inversion H10; subst; split_all. 
inversion H21; subst; split_all. 
inversion H20; subst; split_all. 
replace (S n3) with (S(0+n3)) by omega. eapply2 hd_app. 
replace(head_tuple (head_tuple P)) with (head_tuple P).  auto. 
rewrite (head_tuple_of_hnf_tuple (head_tuple P)). auto. 
eapply2 head_tuple_is_hnf_tuple. 
auto. 
eapply2 head_app_preserves_well_formed. 
eapply2 (head_is_hnf Term x (App (Abs (Ref i P)) N)). 
eapply2 head_app_preserves_tuple_red1. 
eapply2 (head_is_hnf Term x (App (Abs (Ref i P)) N)). 
Qed. 



(* leftmost_outermost reduction *) 

Inductive leftmost_outermost : termred := 
| lo_unit : leftmost_outermost Unit Unit 
| lo_pair : forall t1 v1, leftmost_outermost t1 v1 -> 
            forall t2 v2, leftmost_outermost t2 v2 -> 
                             leftmost_outermost (Pair t1 t2) (Pair v1 v2)
| lo_ref : forall s v i, leftmost_outermost s v -> leftmost_outermost (Ref i s) (Ref i v)
| lo_abs : forall t v, leftmost_outermost t v -> leftmost_outermost (Abs t) (Abs v) 
| lo_app : forall n t1 t2 v1, head n (App t1 t2) v1 -> 
           forall v, leftmost_outermost v1 v -> leftmost_outermost (App t1 t2) v
. 
 
Hint Constructors leftmost_outermost. 




Lemma lo_is_nf: 
forall t v, leftmost_outermost t v -> forall st, well_formed st t -> normal st v.
Proof. 
intros t v e; induction e; intros st wf; inversion wf; subst; eauto. 
eapply2 IHe. eapply2 (head_is_hnf Term n (App t1 t2)). 
Qed. 

Lemma lo_of_normal: forall st n, normal st n -> leftmost_outermost n n.
Proof. intros st n nf; induction nf; split_all. Qed. 


Lemma lo_normal_is_same2 : 
forall n n1, leftmost_outermost n n1 -> forall st,  normal st n ->  n1 = n.
Proof. 
intros n n1 e; induction e; intros st nf; inversion nf; subst; eauto. 
(* 3 *) 
rewrite (IHe1 Tuple); auto. rewrite (IHe2 Term); auto. 
(* 2 *) 
rewrite (IHe Tuple); auto. 
(* 1 *) 
rewrite (IHe Term); auto. 
Qed. 

Lemma lo_reduces : forall t v, leftmost_outermost t v -> tuple_red t v. 
Proof. 
intros t v e; induction e; split_all; 
try (eapply2 zero_red; fail); try red; try (one_step; fail). 
(* 4 *) 
eapply2 preserves_pair_tuple_red. 
(* 3 *) 
eapply2 preserves_ref_tuple_red. 
(* 2 *) 
eapply preserves_abs_tuple_red.  eexact IHe. auto. 
(* 1 *) 
eapply transitive_red. 
2: eexact IHe. eapply2 head_reduces. 
Qed. 


Lemma lo_is_functional: 
forall t v1, leftmost_outermost t v1 -> forall v2, leftmost_outermost t v2 -> v1 = v2. 
Proof.
intros t v1 e; induction e; intros; inversion H; subst; auto; 
try(inversion H0; subst; assert(v1 = v0) by eapply2 head_is_functional; subst; eapply2 IHe; fail). 
(* 4 *) 
rewrite (IHe1 v3); auto; rewrite (IHe2 v4); auto. 
(* 3 *) 
rewrite (IHe v0); auto. 
(* 2 *) 
assert(v = v0) by eapply2 IHe. subst; auto. 
(* 1 *) 
inversion H0; subst. inversion H3; subst. 
assert((n1=n0 /\ v0 = v4)) by eapply2 head_is_functional. split_all; subst.
assert((S(n0+n2)) = (S(n0+n3)) /\ v1 = v3) by eapply2 head_is_functional. split_all; subst.
eapply2 IHe. 
Qed. 



Lemma leftmost_outermost_tuple_implies_head_tuple: 
forall N v, leftmost_outermost N v -> well_formed Tuple N -> 
leftmost_outermost (head_tuple N) v. 
Proof.
intros N v l; induction l; intro wf; split_all; inversion wf; subst; split_all; eauto.
Qed. 


Lemma leftmost_outermost_implies_head: 
forall N v, leftmost_outermost N v -> well_formed Term N -> 
exists n h, head n N h /\ leftmost_outermost h v. 
Proof.
intros N v l; induction l; intro wf; split_all; inversion wf; subst; split_all; eauto. 
(* 2 *) 
exist 0; exist (Ref i (head_tuple s)) . eapply2 lo_ref. 
eapply2 leftmost_outermost_tuple_implies_head_tuple. 
(* 1 *) 
elim(IHl); split_all. 
exist x; exist (Abs x0). 
Qed. 



Lemma leftmost_outermost_head_tuple: 
forall s v, leftmost_outermost (head_tuple s) v -> well_formed Tuple s -> 
leftmost_outermost s v.
Proof. induction s; split_all. inversion H0; inversion H; subst. eapply2 lo_pair. Qed. 

Lemma aux3: 
forall M n v0, head n M v0 -> well_formed Term M -> 
forall v, leftmost_outermost v0 v -> leftmost_outermost M v.
Proof.
induction M; split_all; inversion H0; subst; inversion H; subst. 
(* 3 *) 
inversion H1; subst. eapply2 lo_ref. eapply2 leftmost_outermost_head_tuple. 
(* 2 *) 
inversion H1; subst. eapply2 lo_abs. 
(* 1 *) 
eapply2 lo_app. 
Qed. 


Lemma aux: 
forall M N, tuple_red1 M N -> well_formed Term M -> forall i s, N = Ref i s -> 
forall v, leftmost_outermost s v -> 
(forall (st : sort) (M : lambda),
        well_formed st M -> tuple_red1 M s -> leftmost_outermost M v) -> 
leftmost_outermost M (Ref i v). 
Proof. 
intros M N r; induction r; split_all; subst; invsub. 
(* 4 *) 
eapply2 lo_ref. inversion H; subst. eapply2 H2. 
(* 3 *) 
inversion H; subst. inversion H4; subst. inversion H1; subst. 
assert(leftmost_outermost (Pair M N) (Pair v1 v2)). eapply2 H2. 
inversion H0; subst. 
eapply lo_app. eapply hd_app.  eapply2 hd_ref. simpl.  eapply2 hd_ref. simpl. 
eapply2 lo_ref. eapply2 lo_pair. 
replace(head_tuple (head_tuple M)) with (head_tuple M).  
eapply2 leftmost_outermost_tuple_implies_head_tuple. 
rewrite (head_tuple_of_hnf_tuple (head_tuple M)). auto. 
eapply2 head_tuple_is_hnf_tuple. 
(* 2 *)
inversion H; subst. assert(leftmost_outermost N (Ref i v)) by  eapply2 IHr. 
elim(leftmost_outermost_implies_head N (Ref i v)); split_all. 
eapply lo_app. eapply hd_app. 
eapply2 (head_of_hnf (Abs (Ref 0 Unit)) ). simpl. 
eexact H3; split_all. auto. 
(* 1 *) 
eapply2 lo_app. eapply2 hd_app. simpl. 
eapply2 head_of_hnf. 
Qed. 


Lemma aux2: 
forall M N, tuple_red1 M N -> well_formed Term M -> forall t, N = Abs t -> 
forall v, leftmost_outermost t v -> 
(forall (st : sort) (M : lambda),
        well_formed st M -> tuple_red1 M t -> leftmost_outermost M v) -> 
leftmost_outermost M (Abs v). 
Proof. 
intros M N r; induction r; split_all; subst; invsub; inversion H; subst. 
(* 3 *) 
eapply2 lo_abs. 
(* 2 *) 
assert(leftmost_outermost N (Abs v)) by eapply2 IHr.
elim(leftmost_outermost_implies_head N (Abs v)); split_all. 
eapply lo_app. eapply hd_app. 
eapply2 (head_of_hnf (Abs (Ref 0 Unit)) ). simpl. 
eexact H3; split_all. auto. 
(* 1 *)
inversion H4; subst. inversion H3; subst. 
assert(leftmost_outermost (App (Abs (swap 0 M)) (lift N)) v). eapply2 H2. eapply2 wf_app. 
eapply2 wf_abs. eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
eapply2 app_tuple_red. eapply2 abs_tuple_red. 
eapply2 swap_preserves_tuple_red1. 
unfold lift; eapply2 lift_rec_preserves_tuple_red1. 
elim(leftmost_outermost_implies_head (App (Abs (swap 0 M)) (lift N)) v); split_all. 
inversion H7; subst. inversion H12; subst. 
elim(head_reflects_swap n1 (swap 0 M) v0 H11 0 M); split_all. subst. 
eapply2 lo_app. eapply2 hd_app. eapply2 hd_abs.  eapply2 hd_app. 
eapply2 head_of_hnf. eapply2 hnf_abs. eapply2 (head_is_hnf Term n1 (swap 0 M)). 
eapply2 swap_preserves_well_formed. 
eapply2 wf_app. 
eapply2 wf_abs. eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
Qed. 

Lemma tuple_red1_then_lo: 
forall N P, leftmost_outermost N P -> 
forall st M, well_formed st M -> tuple_red1 M N -> leftmost_outermost M P. 
Proof.
intros N P e; induction e; intros st M wf r; split_all. 
(* 5 *)
assert(well_formed st Unit) by eapply2 tuple_red1_preserves_well_formed. inversion H.  subst. 
inversion r; subst; inversion wf; subst; split_all. 
(* 4 *) 
assert(well_formed st (Pair t1 t2)) by eapply2 tuple_red1_preserves_well_formed. inversion H.  subst. 
inversion r; subst; inversion wf; subst; split_all. 
eapply2 lo_pair. 
(* 3 *) 
assert(well_formed st (Ref i s)) by eapply2 tuple_red1_preserves_well_formed. 
inversion H; subst. 

eapply2 aux. 

(* 2 *) 
assert(well_formed st (Abs t)) by eapply2 tuple_red1_preserves_well_formed. 
inversion H; subst. 

eapply2 aux2. 

(* 1 *) 
assert(well_formed st (App t1 t2)) by eapply2 tuple_red1_preserves_well_formed. 
inversion H0; subst. 
assert(exists n0 v0, head n0 M v0 /\ tuple_red1 v0 v1). 
eapply2 tuple_red1_then_head_implies_head_then_tuple_red1. split_all.
assert(leftmost_outermost x0 v). eapply2 IHe. 
eapply2 (head_is_hnf Term x M). 
eapply2 aux3. 
Qed.


Lemma tuple_red_then_lo: 
forall M N, tuple_red M N -> forall st, well_formed st M -> 
forall  P, leftmost_outermost N P ->  leftmost_outermost M P. 
Proof.
cut(forall red M N, multi_step red M N -> red = tuple_red1 -> 
forall st, well_formed st M -> 
forall  P, leftmost_outermost N P ->  leftmost_outermost M P). 
split_all. 
eapply2 H. 
intros red M N r; induction r; split_all; subst. 
eapply2 (tuple_red1_then_lo N P0); split_all. eapply2 IHr. 
eapply2 tuple_red1_preserves_well_formed. 
Qed. 




Theorem standardisation: 
forall st t n, well_formed st t -> normal st n -> tuple_red t n -> leftmost_outermost t n.
Proof. 
intros. assert(leftmost_outermost n n). eapply2 lo_of_normal. eapply2 tuple_red_then_lo. 
Qed. 

