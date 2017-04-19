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
(*                  Delayed Substitution Lambda Calculus              *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation               *) 
(* of Lambda Calculus  from Project Coq                               *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Delayed_Normal.v                              *)
(*                                                                    *)
(*                      Barry Jay                                     *)
(*                                                                    *)
(**********************************************************************)


Require Import Omega Delayed_Terms Delayed_Tactics Delayed_reduction.


Inductive sort := 
  Tuple 
| Index 
| Term 
| Funty : sort -> sort -> sort
.

Inductive well_formed : sort -> lambda -> Prop := 
| wf_un: well_formed Tuple Unit 
| wf_pair:forall P M, well_formed Tuple P -> well_formed Term M -> well_formed Tuple (Pair P M)
| wf_ref: forall i M, well_formed Tuple M -> well_formed Term (Ref i M) 
| wf_abs : forall M, well_formed Term M -> well_formed Term (Abs M)
| wf_app: forall M N, well_formed Term M -> well_formed Term N -> well_formed Term (App M N)
.

Hint Constructors well_formed. 

Lemma swap_preserves_well_formed: 
forall st M, well_formed st M -> forall j, well_formed st (swap j M). 
Proof.
intros st M wf; induction wf; split_all. 
elim(Test.compare i j); split_all. elim a; split_all. 
elim(Test.compare (S j) i); split_all. elim a; split_all. 
Qed. 

Lemma unique_sort: 
forall t s1 s2, well_formed s1 t -> well_formed s2 t -> s1 = s2.
Proof. induction t; split_all; inversion H; inversion H0; subst; auto. Qed. 

Lemma lift_rec_preserves_well_formed:
forall s M, well_formed s M -> forall n, well_formed s (lift_rec M n). 
Proof. intros s M wf; induction wf; split_all. Qed. 


Lemma tuple_red1_preserves_well_formed: 
forall M N, tuple_red1 M N -> forall s, well_formed s M -> well_formed s N. 
Proof.
intros M N r; induction r; split_all; try (inversion H; subst; auto; fail). 
(* 3 *) 
inversion H; subst; auto. eapply2 wf_ref. eapply2 wf_pair. inversion H3; auto. 
(* 2 *) 
inversion H; subst. inversion H3; subst.  inversion H1; subst.  inversion H5; subst.
eapply2 wf_app. eapply2 wf_app. 
(* 1 *) 
inversion H; subst. inversion H3; subst.  inversion H1; subst.  
eapply2 wf_abs. eapply2 wf_app. eapply2 wf_abs. 
eapply2 swap_preserves_well_formed. 
unfold lift. eapply2 lift_rec_preserves_well_formed. 
Qed. 

Lemma tuple_red_preserves_well_formed: 
forall red M N, multi_step red M N -> red = tuple_red1 -> 
forall s, well_formed s M -> well_formed s N. 
Proof.
intros red M N r; induction r; split_all; subst. eapply2 IHr. 
eapply2 tuple_red1_preserves_well_formed. 
Qed. 



(* normal terms *) 

Inductive normal : sort -> lambda -> Prop :=
| nf_un: normal Tuple Unit
| nf_pair: forall s u,  normal Tuple s -> normal Term u -> normal Tuple (Pair s u)
| nf_ref: forall i s, normal Tuple s -> normal Term (Ref i s)
| nf_abs : forall M, normal Term M -> normal Term (Abs M)
.

Hint Constructors normal. 

Lemma normal_is_decidable : forall M s, normal s M \/ ~(normal s M).
Proof.
induction M; intro s; case s; auto;
try (right; intro n1;  inversion n1; fail). 
(* 3 *) 
elim(IHM1 Tuple); elim(IHM2 Term); split_all. 
right; intro n; inversion n; assert False by eapply2 H; noway. 
(* 4 *) 
right; intro n; inversion n; assert False by eapply2 H0; noway. 
(* 3 *) 
right; intro n; inversion n; assert False by eapply2 H0; noway. 
(* 2 *) 
elim(IHM Tuple); split_all. right; intro n1; inversion n1; assert False by eapply2 H; noway. 
(* 1 *) 
elim(IHM Term); split_all. right; intro n1; inversion n1; assert False by eapply2 H; noway. 
Qed. 



Lemma normal_implies_well_formed: forall M s, normal s M -> well_formed s M. 
Proof. intros M; induction M; split_all; inversion H; auto; subst.  Qed. 

Definition irreducible M (red:termred) := forall N, red M N -> False. 

Lemma normal_is_irreducible: 
forall s M, normal s M -> irreducible M seq_red1. 
Proof. 
intros s M nor; induction nor; split_all; intro; intro r; inversion r; subst; split_all.  
(* 4 *) 
eapply2 IHnor1.
(* 3 *)
eapply2 IHnor2.
(* 2 *) 
eapply2 IHnor.
(* 1 *) 
eapply2 IHnor.
Qed. 

(* 
The basic progress result, that all irreducible terms are normal.
 *) 

Lemma beta_normal:
  forall M N, normal Term M -> well_formed Term (App (Abs M) N) ->
                   exists P, seq_red1 (App (Abs M) N) P. 
Proof.
  induction M; split_all; inversion H; subst; eauto.
inversion H3; subst. 
  assert(n=0 \/ n> 0) by omega. inversion H1; subst; eauto. 
replace n with (S (pred n)) by omega. eauto. 
eauto. 
Qed. 


Theorem tuple_progress : 
forall (M : lambda) s, well_formed s M -> (normal s M) \/ (exists N, seq_red1 M N) .
Proof. 
induction M; try (inversion IHM); subst; split_all; eauto.  
(* 5 *) 
inversion H; subst; eauto. 
(* 4 *) 
inversion H; subst; eauto. 
assert((normal Tuple M1) \/ (exists N : lambda, seq_red1 M1 N)). 
eapply2 IHM1. 
inversion H0; split_all. 
assert((normal Term M2) \/ (exists N : lambda, seq_red1 M2 N)). 
eapply2 IHM2. 
inversion H2; split_all; subst; eauto. 
right; exist (Pair x M2). 
(* 3 *) 
inversion H; subst. 
assert(normal Tuple M \/ (exists N : lambda, seq_red1 M N)) by  eapply2 IHM. 
inversion H0; split_all. right; eauto. 
(* 2 *) 
 inversion H; subst. 
elim(IHM Term); split_all. 
right; eauto. 
(* 1 *) 
right. 
inversion H; subst; eauto. 
elim(IHM1 Term); split_all. 
inversion H0; subst; eauto. 
inversion H0; subst. eapply2 beta_normal.
eauto. 
Qed. 

Lemma irreducible_is_normal: 
forall s M, well_formed s M -> irreducible M seq_red1 -> normal s M. 
Proof. split_all. elim(tuple_progress M s); split_all. assert False by eapply2 H0; noway. Qed. 

Theorem irreducible_iff_normal: forall s M, well_formed s M -> (irreducible M seq_red1 <-> normal s M). 
Proof. split_all. eapply2 irreducible_is_normal. eapply2 normal_is_irreducible. Qed. 
