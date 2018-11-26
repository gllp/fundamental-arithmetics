(* Copyright (C) 2005-2008 Sebastien Briais *)
(* http://lamp.epfl.ch/~sbriais/ *)

(* This library is free software; you can redistribute it and/or modify *)
(* it under the terms of the GNU Lesser General Public License as *)
(* published by the Free Software Foundation; either version 2.1 of the *)
(* License, or (at your option) any later version. *)

(* This library is distributed in the hope that it will be useful, but *)
(* WITHOUT ANY WARRANTY; without even the implied warranty of *)
(* MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU *)
(* Lesser General Public License for more details. *)

(* You should have received a copy of the GNU Lesser General Public *)
(* License along with this library; if not, write to the Free Software *)
(* Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA *)
(* 02110-1301 USA *)

(** Nesse arquivo estão as generalizações do conceito de divisão para *)
(** divisão euclidiana, ou seja, a ideia de quociente e resto, na versão *)
(** utilizada matematicamente. Em coq, a divisibilidade está definida com *)
(** quociente único e resto único (com sinal positivo ou negativo). *)
(** Tentamos adaptar para a versão matemática com quociente único e resto *)
(** único, sempre positivo. Os resultados aqui provados e definições *)
(** se referem para a prova do teorema da divisão euclidiana *)

Require Import missing.
Require Import division.

Unset Standard Proposition Elimination Names.

Open Scope positive_scope.

(** Lemma 1 euclides: Provamos aqui que positivos a e b multiplicados nunca gera um positivo *)
(** menor que o positivo a * 1. Para isso, *)
(** utilizamos resultados da biblioteca de positives para obtermos as implicações, *)
(** bem como intuition para finalizar a prova *)
Lemma never_lesser_mult_positive_1 : forall (a b : positive), ~ (a * b < a * 1).
Proof.
  intros.
  unfold not.
  intros.
  apply Pos.mul_lt_mono_l in H.
  apply Pos.nlt_1_r in H.
  intuition.
Qed.

(** Lemma 2 euclides: Provamos aqui que positivos a e b multiplicados nunca gera um positivo *)
(** menor que o positivo a * 1 <-> a * b > a. Isso foi feito para poder *)
(** provar que a < a * b, sem multiplicar por 1. Para isso, *)
(** utilizamos resultados da biblioteca de positives para obtermos as implicações, *)
(** bem como intuition para finalizar a prova *)
Lemma never_lesser_mult_positive_eq : forall (a b : positive), ~ (a * b < a * 1) <-> ~ (a * b < a).
Proof.
  intros.
  unfold not.
  intros.
  split.
  - intros.
    unfold not in H.
    destruct H.
    rewrite Pos.mul_1_r.
    apply H0.
  - intros.
    apply never_lesser_mult_positive_1 in H0; intuition.
Qed.

(** Lemma 3 euclides: Provamos aqui que positivos a e b multiplicados nunca gera um positivo *)
(** menor que o positivo a. Para isso, *)
(** utilizamos resultados da biblioteca de positives para obtermos as implicações, *)
(** bem como intuition para finalizar a prova  *)
Lemma never_lesser_mult_positive : forall (a b : positive), ~ (a * b < a).
Proof.
  intros.
  apply never_lesser_mult_positive_eq.
  apply never_lesser_mult_positive_1.
Qed.

Open Scope Z_scope.

(** Lemma 4 euclides: se b | a e |a| < |b| -> a = 0 *)
(** Complemento ao lemma 16 do arquivo division.v . Para provarmos, *)
(** untilizamos resultados provados anteriormente, bem como a definição *)
(** de divides. *)
Lemma divides_zero_module : forall (a b : Z), divides b a /\ Z.abs a < Z.abs b -> a = 0.
Proof.
  intros.
  destruct H.
  unfold divides in H.
  destruct H.
  - destruct a.
    + reflexivity.
    + destruct b.
      * inversion H.
      * destruct x.
        { inversion H. }
        {
          rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
        }
        {
          inversion H.
        }
      * destruct x.
        { inversion H. }
        { inversion H. }
        {
           rewrite H in H0.
           simpl in H0.
           apply never_lesser_mult_positive in H0.
           inversion H0.
        }
   + destruct b.
     * inversion H.
     * destruct x.
       { inversion H. }
       { inversion H. }
       {
          rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
       }
     * destruct x.
       { inversion H. }
       { rewrite H in H0.
          simpl in H0.
          apply never_lesser_mult_positive in H0.
          inversion H0.
       }
       { inversion H. }
Qed.

(** Lemma 5 euclides: Se a < 0 -> ~(a >= 0) *)
(** Lemma provado com a finalidade de ajudar na prova do Lemma 6. *)
(** A explicação está no próximo enunciado. *)
Lemma impossible_Zneg : forall (p : positive), ~ (0 <= Z.neg p).
Proof.
  intros.
  unfold not.
  intros.
  auto.
Qed.

(** Lemma 6 euclides: para todo a b em Z, *)
(** |a - b| = max a b - min a b *)
(** Usou-se este lemma para auxiliar na prova do lemma 7 *)
(** Não conseguimos efetuar a prova a tempo deste teorema, mas *)
(** a ideia que tivemos seria partir do estudo dos casos em Z para a e b. *)
Lemma abs_max_min : forall (a b : Z), Z.abs (a - b) = (Z.max a b) - (Z.min a b).
Proof.
Admitted.

(** Lemma 7 euclides: para todo b x x0, *)
(** 0 <= x < |b| e 0 <= x0 < b -> |x - x0| < |b| *)
(** Provou-se este lemma para auxiliar na prova da unicidade *)
(** do quociente na divisão euclidiana. *)
(** A ideia foi estudar os vários casos possíveis de b x x0 em Z e  *)
(** utilizá-los para provar o lemma. Usamos propriedades de máximo, mínimo *)
(**e módulo para provarmos *)
Lemma smaller_number_div : forall (b x x0 : Z), (0 <= x < Z.abs b) /\ (0 <= x0 < Z.abs b)
  -> Z.abs (x - x0) < Z.abs b.
Proof.
  intros.
  destruct H.
  destruct H.
  destruct H0.
  destruct b.
  - simpl in H2.
    intuition.
  - simpl in H2.
    simpl in H1.
    destruct x.
    + destruct x0.
      * simpl. intuition.
      * simpl. apply H2.
      * simpl. apply impossible_Zneg in H0. intuition.
    + destruct x0.
      * simpl. apply H1.
      * assert (H3: Z.max (Z.pos p0) (Z.pos p1) < Z.pos p).
        {
          apply Z.max_lub_lt.
          apply H1.
          apply H2.
        }
        assert (H4: forall (a b : Z), (Z.min a b) <= (Z.max a b) ).
        {
          intros.
          apply Z.min_le_iff.
          left.
          apply Z.le_max_l.
        }
        assert (H5: 0 < Z.min (Z.pos p1) (Z.pos p0)).
        {
          apply Z.min_glb_lt.
          intuition.
          intuition.
        }
        assert (H6: Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p1) (Z.pos p0) < Z.max (Z.pos p0) (Z.pos p1)  ).
        {
          apply Z.lt_sub_pos.
          apply H5.
        }
        assert (H7: Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p1) (Z.pos p0) < Z.pos p).
        {
          apply Z.lt_trans with (m:= Z.max (Z.pos p0) (Z.pos p1)).
          apply H6.
          apply H3.
        }
        assert (H8: Z.abs(Z.pos p0 - Z.pos p1) = Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p0) (Z.pos p1)).
        {
          apply abs_max_min with (a:=(Z.pos p0)) (b:=(Z.pos p1)).
        }
        rewrite H8.
        rewrite Z.min_comm.
        apply H7.
      * apply impossible_Zneg in H0.
        inversion H0.
    + apply impossible_Zneg in H.
        inversion H.
  - simpl. simpl in H1. simpl in H2.
    destruct x.
    + destruct x0.
      * simpl. intuition.
      * simpl. apply H2.
      * simpl. apply impossible_Zneg in H0. intuition.
    + destruct x0.
      * simpl. apply H1.
      * assert (H3: Z.max (Z.pos p0) (Z.pos p1) < Z.pos p).
        {
          apply Z.max_lub_lt.
          apply H1.
          apply H2.
        }
        assert (H4: forall (a b : Z), (Z.min a b) <= (Z.max a b) ).
        {
          intros.
          apply Z.min_le_iff.
          left.
          apply Z.le_max_l.
        }
        assert (H5: 0 < Z.min (Z.pos p1) (Z.pos p0)).
        {
          apply Z.min_glb_lt.
          intuition.
          intuition.
        }
        assert (H6: Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p1) (Z.pos p0) < Z.max (Z.pos p0) (Z.pos p1)  ).
        {
          apply Z.lt_sub_pos.
          apply H5.
        }
        assert (H7: Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p1) (Z.pos p0) < Z.pos p).
        {
          apply Z.lt_trans with (m:= Z.max (Z.pos p0) (Z.pos p1)).
          apply H6.
          apply H3.
        }
        assert (H8: Z.abs(Z.pos p0 - Z.pos p1) = Z.max (Z.pos p0) (Z.pos p1) - Z.min (Z.pos p0) (Z.pos p1)).
        {
          apply abs_max_min with (a:=(Z.pos p0)) (b:=(Z.pos p1)).
        }
        rewrite H8.
        rewrite Z.min_comm.
        apply H7.
      * apply impossible_Zneg in H0.
        inversion H0.
    + apply impossible_Zneg in H.
        inversion H.
Qed.

(** Lemma 8 euclides: se q é o quociente de a = b*q + r, e b > 0, *)
(** então q = floor (a / b) e a < b*q + q. Utlizado na prova *)
(** do teorema da divisão euclidiana, não conseguimos prová-lo a tempo, *)
(** mas está correto matematicamente, tendo sido verificado em "Teoria dos Números: um passeio pelo mundo inteiro com primos
e outros números familiares", IMPA. *)
Lemma less_then_floor_mult : forall (x y : Z), y > 0 -> x - y * (x/y) < y.
Proof.
Admitted.

(** Definição de teto da divisão de dois números inteiros, necessária *)
(** para a definição de divisibilidade com b < 0 e resto positivo *)
Definition ceil_div (a b : Z) : Z :=
  if (a - b*(a/b) =? 0) then a / b
  else a / b + 1.

(** Definição de quociente da divisão euclidiana *)
Definition quotient (q a b : Z) := exists (r : Z), 0 <= r < Z.abs b /\ a = b * q + r.

(** Definição de resto da divisão euclidiana *)
Definition remainder (r a b : Z) := exists (q : Z), a = b * q + r /\ (0 <= r < Z.abs b).

(** Lemma 9 euclides: se b < 0, b * q <= a, onde q = ceil (a b). *)
(** Lemma usado na prova do teorema da divisão euclidiana, com b < 0. *)
(** Para b < 0, o quociente é dado por ceil (a / b), o que garante r >= 0. *)
(** Utilizado na prova do teorema da divisão euclidiana, não conseguimos prová-lo a tempo, *)
(** mas está correto matematicamente, tendo sido verificado em "Teoria dos Números: um passeio pelo mundo inteiro com primos
e outros números familiares", IMPA. *)
Lemma greater_then_ceil_neg : forall (a b : Z), (b < 0) ->  b * (ceil_div a b) <= a.
Proof.
Admitted.

(** Lemma 10 euclides: se b < 0, a - b * q < - b, onde q = ceil (a b). *)
(** Lemma usado na prova do teorema da divisão euclidiana, com b < 0. *)
(** Para b < 0, o quociente é dado por ceil (a / b), o que garante r >= 0. *)
(** Utilizado na prova do teorema da divisão euclidiana, não conseguimos prová-lo a tempo, *)
(** mas está correto matematicamente, tendo sido verificado em "Teoria dos Números: um passeio pelo mundo inteiro com primos
e outros números familiares", IMPA. *)
Lemma less_then_ceil_mult : forall (x y : Z), y < 0 -> x - y * (ceil_div x y) < Z.abs (y).
Proof.
Admitted.

(** Teorema da divisão euclidiana: para todo a, b em Z, a = b*q + r, *)
(** existindo q, r em Z, com 0 <= r < |b|. Para a prova do teorema *)
(** se destruiu a e b em seus possíveis casos (0, Z.pos, Z.neg) e *)
(** aplicou-se resultados anteriores. A prova foi basicamente análise *)
(** de casos, se valendo da definição de ceil para b < 0 e de *)
(** a/ b = floor a b para b > 0. *)
Theorem euclide : forall (a b : Z), (b <> 0) -> exists (q r : Z), quotient q a b /\ remainder r a b.
Proof.
  intros.
  destruct b.
  - unfold not in H. intuition.
  - destruct a.
    + unfold not in H.
      exists 0.
      exists 0.
      split.
      * unfold quotient.
        exists 0.
        split.
        {
           simpl.
           intuition.
        }
        {
           reflexivity.
        }
      * unfold remainder.
        exists 0.
        split.
        {
          reflexivity.
        }
        {
           simpl.
           intuition.
        }
   + exists (Z.pos p0 / Z.pos p).
     exists (Z.pos p0 - (Z.pos p * (Z.pos p0 / Z.pos p))).
     split.
     * unfold quotient.
       exists (Z.pos p0 - (Z.pos p * (Z.pos p0 / Z.pos p))).
       split.
       {
           assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           split.
          {
             apply H1.
             intuition.
          }
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
       }
       {
         intuition.
       }
    * unfold remainder.
      exists (Z.pos p0 / Z.pos p).
      split.
      {
        intuition.
      }
      {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
      }
  + exists (Z.neg p0 / Z.pos p).
    exists (Z.neg p0 - (Z.pos p * (Z.neg p0 / Z.pos p))).
    split.
    * unfold quotient.
      exists (Z.neg p0 - (Z.pos p * (Z.neg p0 / Z.pos p))).
      split.
      {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
      }
      {
        intuition.
      }
   * unfold remainder.
     exists (Z.neg p0 / Z.pos p).
     split.
     {
       intuition.
     }
     {
        split.
        {
          assert (H0: forall (x y : Z), y > 0 -> y * (x/y) <= x).
           {
              intros.
              apply Z.mul_div_le.
              intuition.
           }
           assert (H1: forall (x y : Z), y > 0 -> 0 <= x - y * (x/y)).
           {
              intros.
              apply Zle_minus_le_0.
              apply H0.
              apply H1.
           }
           apply H1.
           intuition.
        }
        {
          unfold Z.abs.
          apply less_then_floor_mult.
          intuition.
        }
     }
  - destruct a.
    + exists 0.
      exists 0.
      split.
      * unfold quotient.
        exists 0.
        intuition.
        simpl.
        intuition.
      * unfold remainder.
        exists 0.
        intuition.
        simpl.
        intuition.
    + exists (ceil_div (Z.pos p0) (Z.neg p)).
      exists (Z.pos p0 - Z.neg p * (ceil_div (Z.pos p0) (Z.neg p))).
      split.
      * unfold quotient.
        exists (Z.pos p0 - Z.neg p * (ceil_div (Z.pos p0) (Z.neg p))).
        split.
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
        intuition.
      * unfold remainder.
        exists (ceil_div (Z.pos p0) (Z.neg p)).
        split.
        {
          intuition.
        }
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
    + exists (ceil_div (Z.neg p0) (Z.neg p)).
      exists (Z.neg p0 - Z.neg p * (ceil_div (Z.neg p0) (Z.neg p))).
      split.
      * unfold quotient.
        exists (Z.neg p0 - Z.neg p * (ceil_div (Z.neg p0) (Z.neg p))).
        split.
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
        intuition.
      * unfold remainder.
        exists (ceil_div (Z.neg p0) (Z.neg p)).
        split.
        {
          intuition.
        }
        {
           split.
           {
               assert (H1: forall (x y : Z), y < 0 -> 0 <= x - y * ceil_div x y).
               {
                  intros.
                  apply Zle_minus_le_0.
                  apply greater_then_ceil_neg.
                  apply H0.
               }
               apply H1.
               apply Pos2Z.neg_is_neg.
           }
           {
              apply less_then_ceil_mult.
              apply Pos2Z.neg_is_neg.
           }
        }
Qed.

(** Lemma 11 euclides: unicidade do quociente *)
(** Prova que, dado a = b*q + r, q é único *)
(** Para provarmos, utilizamos resultados provados anteriormente, *)
(** precisando do resultado do lemma 6, além de resultados em missing.v, *)
(** bem como resultados de bibliotecas, os quais às vezes precisaram ser *)
(** adaptados.*)
Lemma quotient_uniquiness : forall (a b q q1 : Z), (b <> 0) /\ (quotient q a b) /\ (quotient q1 a b) -> q = q1.
Proof.
  intros.
  destruct H as [H1 H2].
  destruct H2 as [H3 H4].
  unfold quotient in H3.
  unfold quotient in H4.
  destruct H3.
  destruct H4.
  destruct H.
  destruct H0.
  rewrite H3 in H2.
  rewrite Z.add_move_l in H2.
  rewrite Z.add_sub_swap in H2.
  rewrite <- Z.mul_sub_distr_l in H2.
  symmetry in H2.
  rewrite Zeq_plus_swap in H2.
  assert (H7: forall (p q : positive), Z.pos_sub q p = - Z.pos_sub p q).
  {
      intros.
      symmetry.
      apply Z.pos_sub_opp.
  }
  assert (H4: Z.abs (x0 - x) < Z.abs b).
  {
     apply smaller_number_div.
     split.
     apply H0.
     apply H.
  }
  assert (H5: x - x0 = 0).
  {
    apply divides_zero_module with (b:=b).
    split.
    - unfold divides.
      exists (q1 - q).
      rewrite Zmult_minus_distr_l in H2.
      symmetry.
      rewrite Zmult_minus_distr_l.
      intuition.
    - assert (H5: Z.abs(x - x0) = Z.abs(x0 - x)).
      {
        destruct x.
        - destruct x0.
          + reflexivity.
          + reflexivity.
          + reflexivity.
        - destruct x0.
          + reflexivity.
          + simpl. rewrite H7. rewrite Z.abs_opp. reflexivity.
          + simpl. rewrite Pos2Z.inj_add. symmetry. rewrite Pos2Z.inj_add.
            rewrite Z.add_comm. reflexivity.
        - destruct x0.
          + reflexivity.
          + simpl. rewrite Pos2Z.inj_add. symmetry. rewrite Pos2Z.inj_add.
            rewrite Z.add_comm. reflexivity.
          + simpl. rewrite H7. rewrite Z.abs_opp. reflexivity.
      }
      rewrite H5.
      apply H4.
  }
  assert (H6: x0 - x = 0).
  {
     intuition.
  }
  rewrite H6 in H2.
  apply mult_lemma2_Z in H2.
  destruct H2 as [H8 | H9].
  - unfold not in H1.
    apply H1 in H8.
    inversion H8.
  - apply Zminus_eq in H9.
    apply H9.
Qed.

(** Lemma 12 euclides: unicidade do resto *)
(** Prova que, dado a = b*q + r, r é único *)
(** Para provarmos, utilizamos resultados provados anteriormente, *)
(** precisando do resultado do lemma 6, além de resultados em missing.v, *)
(** bem como resultados de bibliotecas, os quais às vezes precisaram ser *)
(** adaptados e também o resultado que o quociente é único. *)
Lemma remainder_uniquiness :  forall (a b r r1 : Z), (b <> 0) /\ (remainder r a b) /\ (remainder r1 a b) -> r = r1.
Proof.
  intros.
  destruct H as [H1 [H2 H3]].
  unfold remainder in H2.
  unfold remainder in H3.
  destruct H2.
  destruct H3.
  destruct H.
  destruct H0.
  inversion H0.
  rewrite H in H0.
  rewrite Z.add_move_l in H0.
  rewrite Z.add_sub_swap in H0.
  rewrite <- Z.mul_sub_distr_l in H0.
  symmetry in H0.
  rewrite Zeq_plus_swap in H0.
  assert (H5: x0 = x).
  {
    apply quotient_uniquiness with (b:=b) (a:=a).
    split.
    apply H1.
    split.
    - unfold quotient. exists r1.
      split.
      apply H3.
      apply H4.
    - unfold quotient. exists r.
      split.
      apply H2.
      apply H.
  }
  apply Zeq_minus in H5.
  rewrite H5 in H0.
  rewrite mult_symm_0 in H0.
  symmetry in H0.
  apply Zminus_eq in H0.
  apply H0.
Qed.