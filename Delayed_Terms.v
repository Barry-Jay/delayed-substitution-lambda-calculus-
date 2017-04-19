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
(*               Delayed Substitution Lambda Calculus                 *)
(*                                                                    *)
(* is implemented in Coq by adapting the implementation of            *)
(* Lambda Calculus from Project Coq                                   *)
(* 2015                                                               *)
(**********************************************************************)

(**********************************************************************)
(*                      Delayed_Terms.v                               *)
(*                                                                    *)
(* adapted from Terms.v for Lambda Calculus                           *)
(*                                                                    *)
(*                          Barry Jay                                 *)
(*                                                                    *)
(**********************************************************************)



Require Import Omega Test.

Ltac noway := intros; assert False by omega; contradiction. 


(* lambda terms using traditional de Bruijn's indices *)

Inductive lambda:  Set :=
| Unit  : lambda
| Pair: lambda -> lambda -> lambda
| Ref : nat -> lambda -> lambda 
| Abs : lambda -> lambda  
| App : lambda -> lambda -> lambda .



(* Lifting *)

Definition relocate (i k : nat) :=
  match test k i with
  
      (* k<=i *) | left _ => S i
   (* k>i  *) | _ => i
  end.


Lemma relocate_succ :
forall n n0, relocate (S n) (S n0) = S(relocate n n0).
Proof. 
intros; unfold relocate; elim(test(S n0) (S n)); elim(test n0 n); intros; auto; 
assert False by omega; contradiction. 
Qed. 


Fixpoint lift_rec (L : lambda) : nat -> lambda :=
  fun k : nat =>
  match L with
    | Unit  => Unit
    | Pair s t => Pair (lift_rec s k) (lift_rec t k)
    | Ref i s => Ref (relocate i k) (lift_rec s k)
    | Abs M => Abs (lift_rec M (S k))
    | App M N => App (lift_rec M k) (lift_rec N k)
  end.

Definition lift (N : lambda) := lift_rec N 0.


Lemma lift_lift_rec :
 forall (U : lambda) (n i : nat),
 i <= n ->
 lift_rec (lift_rec U i) (S n) = lift_rec (lift_rec U n) i.
Proof.
simple induction U; simpl in |- *;  intros; auto.
(* 4 *) 
rewrite H; auto. rewrite H0; auto. 
(* 3 *) 
unfold relocate.
elim(test i n); intros; auto; try noway. 
elim(test n0 n); intros; auto; try noway. 
elim(test (S n0) (S n)); intros; auto; try noway. 
elim(test i (S n)); intros; auto; try noway. 
rewrite H; auto. 
elim(test (S n0) (S n)); intros; auto; try noway. 
elim(test i n); intros; auto; try noway. 
rewrite H; auto. 
elim(test n0 n); intros; auto; try noway. 
elim(test (S n0) n); intros; auto; try noway. 
elim(test i n); intros; auto; try noway. 
rewrite H; auto. 
(* 2 *) 
rewrite H; auto. omega. 
(* 1 *) 
rewrite H; intros; auto.  rewrite H0; intros; auto. 
Qed. 

