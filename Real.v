(** * Real: Аксиоматизация вещественных чисел в Coq *)

Require Reals. 
Require Psatz.
Require Ring.
Require Field. 

(* ################################################################# *)
(** * Аксиоматизация множества R *)

(** Вещественные числа можно определить с помощью фундаментальных 
    последовательностей или с помощью дедекиндовых сечений. Эти
    представления математически точны, их можно записать в Coq, 
    реализацию можно найти в библиотеке Coq Repository at Nijmegen (CoRN).
    Однако это сложные представления и с ними сложно работать.
     
    Стандартная библиотека Coq предлагает другой подход: аксиоматический. *)

Module OurR.

Parameter R : Set.

Delimit Scope R_scope with R.
Local Open Scope R_scope.

(** Мы начнем с объявления двух важных вещественных чисел: нуля и единицы. *)
Parameter R0 : R.
Parameter R1 : R.

(** И объявим способы получить другие вещественные числа: *)
Parameter Rplus : R -> R -> R.
Parameter Rmult : R -> R -> R.
Parameter Ropp : R -> R.
Parameter Rinv : R -> R.

Infix "+" := Rplus : R_scope.
Infix "*" := Rmult : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Notation "/ x" := (Rinv x) : R_scope.

(** Другие базовые операции определены с помощью уже объявленных: *)

Definition Rminus (r1 r2:R) : R := r1 + - r2.
Definition Rdiv (r1 r2:R) : R := r1 * / r2.

Infix "-" := Rminus : R_scope.
Infix "/" := Rdiv : R_scope.

(** Мы хотим иметь возможность конвертировать натуральные числа в элементы
    множества R, чтобы можно было писать числа 0, 1, 2, 3... *)

Fixpoint INR (n : nat) : R :=
  match n with
  | O    => R0
  | 1    => R1            
  | S n' => R1 + INR n'
  end.

(** Стандартная библиотека определяет коэрсию из Z, которая
    немного полезнее, но хуже читается. *)

(** _Коэрсия_ предлагает Coq'у попробовать применить данную функцию
   в тех ситуациях, когда типы не совпадают. Например, сейчас [Rplus 4 5]
   выдаст type error. *)

Fail Check (4 + 5).

Coercion INR : nat >-> R.
 
Check 4 + 5.
Compute (4 + 5).

(* ################################################################# *)
(** * Аксиомы поля *)

(** Посмотрим на самую суть библиотеки вещественных чисел - на аксиомы: *)

Axiom R1_neq_R0 : INR 1 <> INR 0.

(** Аксиомы сложения *)

Axiom Rplus_comm : forall r1 r2 : R, r1 + r2 = r2 + r1.

Axiom Rplus_assoc : forall r1 r2 r3 : R, r1 + r2 + r3 = r1 + (r2 + r3).

Axiom Rplus_opp_r : forall r : R, r + - r = 0.

Axiom Rplus_0_l : forall r : R, 0 + r = r.

(** Конечно, не все свойства вещественных чисел определяются как аксиомы: некоторые можно 
   доказать. *)

Lemma Rplus_0_r : forall r : R, r + 0 = r.
Proof.
  (* WORKED IN CLASS *)
  intros r. 
  rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.
  
Lemma Rplus_opp_l : forall r, -r + r = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  rewrite Rplus_comm.
  apply Rplus_opp_r.
Qed.

Lemma Ropp_0 : -0 = 0.
Proof.
  rewrite <- (Rplus_0_l (-0)).
  rewrite Rplus_opp_r.
  reflexivity.
Qed.

Lemma Rplus_cancel_l : forall r1 r2 r3, r1 + r2 = r1 + r3 -> r2 = r3.
Proof.
  intros r1 r2 r3 H.
  rewrite <- Rplus_0_l.
  rewrite <- (Rplus_opp_l r1).
  rewrite Rplus_assoc.
  rewrite <- H.
  rewrite <- Rplus_assoc.
  rewrite Rplus_opp_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.
    
Lemma R0_unique : forall r1 r2, r1 + r2 = r1 -> r2 = 0.
Proof.
  intros r1 r2 H.
  rewrite <- Rplus_0_r in H.
  eapply Rplus_cancel_l.
  apply H.
Qed.  

(** Аксиомы умножения *)

Axiom Rmult_comm : forall r1 r2:R, r1 * r2 = r2 * r1.

Axiom Rmult_assoc : forall r1 r2 r3:R, r1 * r2 * r3 = r1 * (r2 * r3).

Axiom Rinv_l : forall r:R, r <> 0 -> / r * r = 1.

Axiom Rmult_1_l : forall r:R, 1 * r = r.

Axiom Rmult_plus_distr_l : forall r1 r2 r3:R, r1 * (r2 + r3) = r1 * r2 + r1 * r3.

Lemma Rmult_0_r : forall r, r * 0 = 0.
Proof.
  (* WORKED IN CLASS *)
  intros r.
  apply (R0_unique (r * 0)).
  rewrite <- Rmult_plus_distr_l.
  rewrite Rplus_0_l.
  reflexivity.
Qed.

Lemma Rmult_plus_distr_r : forall r1 r2 r3:R, (r1 + r2) * r3 = r1 * r3 + r2 * r3.
Proof.
  (* WORKED IN CLASS *)
  intros r1 r2 r3.
  rewrite Rmult_comm.
  rewrite Rmult_plus_distr_l.
  rewrite 2 (Rmult_comm r3).
  reflexivity.
Qed.

Lemma Rinv_r : forall r:R, r <> 0 -> r * / r = 1.
Proof.
  (* WORKED IN CLASS *)
  intros. rewrite Rmult_comm.
  apply Rinv_l.
  assumption.
Qed.
  
(* ================================================================= *)
(** ** Тактики Ring и Field *)

(** Теперь, когда у нас есть основные леммы, мы можем сказать Coq'у, что R образует
    алгебраическое _кольцо_ и _поле_. *)

Export Ring.
Export Field.

Lemma R_Ring_Theory : ring_theory R0 R1 Rplus Rmult Rminus Ropp eq.
Proof.
  constructor.
  (* сложение *)
  (* 0 - нейтральный слева *) apply Rplus_0_l.
  (* коммутативность *) apply Rplus_comm.
  (* ассоциативность *) intros; rewrite Rplus_assoc; easy.
  (* умножение *)
  (* 1 - нейтральный слева *) apply Rmult_1_l.
  (* коммутативность *) apply Rmult_comm.
  (* ассоциативность *) intros; rewrite Rmult_assoc; easy.
  (* дистрибутивность *) apply Rmult_plus_distr_r.
  (* sub = opp *) reflexivity.
  (* существование обратного по сложению *) apply Rplus_opp_r.
Defined.

Add Ring RRing : R_Ring_Theory.  

Lemma R_Field_Theory : field_theory R0 R1 Rplus Rmult Rminus Ropp Rdiv Rinv eq.
Proof.
  constructor.
  (* аксиомы кольца *) apply R_Ring_Theory.
  (* 0 <> 1 *) apply R1_neq_R0.
  (* div = inv *) reflexivity.
  (* существование обратного по умножению *) apply Rinv_l.
Defined.

Add Field RField : R_Field_Theory.  

(** Посмотрим, на что способны эти тактики: *)

Example ring_test1 : forall (x : R), x + x = 2 * x. Proof. intros. simpl. ring. Qed.
Example ring_test2 : forall (x y z: R), x * y + z  = z + y * x. Proof. intros. ring. Qed.

Example field_test1 : forall (x y : R), x <> 0 -> x * y / x = y.
Proof. intros. Fail ring. field. assumption. Qed.

(* ################################################################# *)
(** * Порядок *)

(** Мы введем обычный порядок на вещественных числах, снова с помощью аксиом. *)

Parameter Rlt : R -> R -> Prop.

Infix "<" := Rlt : R_scope.

Definition Rgt (r1 r2:R) : Prop := r2 < r1.
Definition Rle (r1 r2:R) : Prop := r1 < r2 \/ r1 = r2.
Definition Rge (r1 r2:R) : Prop := Rgt r1 r2 \/ r1 = r2.

Infix "<=" := Rle : R_scope.
Infix ">=" := Rge : R_scope.
Infix ">" := Rgt : R_scope.

Axiom total_order_T : forall r1 r2 : R, {r1 < r2} + {r1 = r2} + {r1 > r2}.
  
Axiom Rlt_asym : forall r1 r2 : R, r1 < r2 -> ~ r2 < r1.

Axiom Rlt_trans : forall r1 r2 r3 : R, r1 < r2 -> r2 < r3 -> r1 < r3.

Axiom Rplus_lt_compat_l : forall r r1 r2 : R, r1 < r2 -> r + r1 < r + r2.

Axiom Rmult_lt_compat_l : forall r r1 r2 : R, 0 < r -> r1 < r2 -> r * r1 < r * r2.

(* ################################################################# *)
(** * Полнота *)

(** Конечно, не любое поле является полем вещественных чисел:
    даже рациональные числа (строгое подмножество вещественных) образуют
    поле. Последнее, что нужно для полного определения вещественных чисел, -
    аксиома _полноты_ (completeness). Эта аксиома утверждает, что любое 
    непустое ограниченное подмножество вещественных чисел имеет наименьшую
    верхнюю границу (верхнюю грань, супремум), которая сама является 
    вещественным числом.
	  
    Как обычно, множества мы будем записывать как функции типа [R -> Prop],
    которые по данному вещественному числу указывают, является ли оно элементом
    множества. *)

Definition is_upper_bound (E:R -> Prop) (m:R) := forall x:R, E x -> x <= m.

Definition bound (E:R -> Prop) := exists m : R, is_upper_bound E m.
 
Definition is_lub (E:R -> Prop) (m:R) :=
  is_upper_bound E m /\ (forall b:R, is_upper_bound E b -> m <= b).

Axiom
  completeness :
    forall E:R -> Prop,
      bound E -> (exists x : R, E x) -> { m:R | is_lub E m }.

(* ================================================================= *)
(** ** Как определять иррациональные числа *)

(** Взглянем на то, как на практике можно использовать аксиому полноты. Только 
    прежде нам понадобится определить одну дополнительную лемму, которую мы _можем_,
    но это сложнее, чем кажется на первый взгляд. *)

Lemma Rlt_0_1 : 0 < 1. Admitted.

(** Мы хотим определить квадратный корень из 2. Квадратный корень из 2 -
    наименьшая верхняя грань для предиката [x * x < 2] (или [x * x <= 2]).	
    Воспользуемся аксиомой полноты, чтобы показать, что эта наименьшая верхняя
    граница существует. *)

Definition lt_sqrt2 (x : R) := x * x < 2.

(** Сначала нужно показать, что у этого предиката есть верхняя граница. 
    Один разумный пример такой верхней границы - число 2 (числа 3/2 или 5 
    тоже подойдут). *)

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  left.
  destruct (total_order_T x 1) as [[L | E] | G].
  - rewrite <- (Rplus_0_r x).
    eapply Rlt_trans.
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
    rewrite Rplus_comm.
    apply Rplus_lt_compat_l.
    assumption.
  - rewrite E.
    rewrite <- (Rplus_0_r 1).
    apply Rplus_lt_compat_l.
    apply Rlt_0_1.
  - assert (x * 1 < x * x).
    apply Rmult_lt_compat_l. 
    eapply Rlt_trans. 
    apply Rlt_0_1.
    apply G. 
    apply G.
    rewrite Rmult_comm, Rmult_1_l in H0.
    eapply Rlt_trans.
    apply H0.
    apply H.
Qed.

Lemma bound_sqrt2 : bound lt_sqrt2.
Proof. exists 2. apply upper_bound_2_sqrt_2. Qed.

(** We also need to show that some number satisfies this predicate:
    0, 1 and -1 are all reasonable candidates. *)

Lemma ex_lt_sqrt2 : exists x, lt_sqrt2 x.
Proof. 
  exists 1. unfold lt_sqrt2. 
  rewrite Rmult_1_l. 
  rewrite <- (Rplus_0_r 1); simpl. 
  apply Rplus_lt_compat_l.
  apply Rlt_0_1.
Qed.

(** We can now plug these proofs into our completeness axiom/function,
    getting out a real number that is the least upper bound of
    [lt_sqrt2] -- that is, the square root of 2. *)

Definition sqrt2 := completeness lt_sqrt2 bound_sqrt2 ex_lt_sqrt2.

Print sqrt2.
(** In subsequent chapters we will make use of real numbers like 
    √2, π and e, which are defined in the Coq real number library
    using the completeness axiom. **)

End OurR.

(** Let's take a look at our upper bound proof using Coq's own
    real numbers and definitions. Here we will benefit from 
    Coq's automation tactics. *)

Export Reals. 
Export Psatz.

Open Scope R_scope.

Definition lt_sqrt2 (x : R) := x * x < 2.

Lemma upper_bound_2_sqrt_2 : is_upper_bound lt_sqrt2 2.
Proof.
  unfold is_upper_bound, lt_sqrt2; simpl.
  intros x H.
  destruct (total_order_T x 1) as [[L | E] | G]; try lra.
  assert (x * 1 <= x * x).
  { apply Rmult_le_compat_l; lra. }
  lra.
Qed.

(** [lra] stands for Linear Real Arithmetic and is broadly useful in
    proving real number (in)equalities *)

Notation "√ x" := (sqrt x) (at level 0).

Lemma pow2_sqrt : forall x:R, 0 <= x -> (√ x) ^ 2 = x. 
Proof. intros; simpl; rewrite Rmult_1_r, sqrt_def; auto. Qed.

Lemma pow2_sqrt2 : (√ 2) ^ 2 = 2.
Proof. apply pow2_sqrt. lra. Qed.

Lemma pown_sqrt : forall (x : R) (n : nat), 
  0 <= x -> √ x ^ (S (S n)) = (x * √ x ^ n)%R.
Proof.
  intros. simpl. rewrite <- Rmult_assoc. rewrite sqrt_sqrt; auto.
Qed.  

Lemma sqrt_neq_0_compat : forall r : R, 0 < r -> (√ r)%R <> 0.
Proof. intros. specialize (sqrt_lt_R0 r). lra. Qed.

Lemma sqrt_inv : forall (r : R), 0 < r -> √ (/ r) = (/ √ r)%R.
Proof.
  intros.
  replace (/r)%R with (1/r)%R by lra.
  rewrite sqrt_div_alt, sqrt_1 by lra.
  lra.
Qed.  

Lemma sqrt2_inv : √ (/ 2) = (/ √ 2)%R.
Proof.
  apply sqrt_inv; lra.
Qed.  

(* Sun Jan 19 21:29:28 CST 2020 *)
