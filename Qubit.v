(** * Qubit: Строительные блоки квантовых вычислений *)

From VQC Require Export Matrix.
Require Import FunctionalExtensionality.
Require Import Bool.
Require Import List.
Import ListNotations.

(* ################################################################# *)
(** * Кубиты *)

(** Начнем с базового "строительного блока" квантовых вычислений :
    с кубита *)

Notation Qubit := (Vector 2).

Definition qubit0 : Qubit := l2V [1;0]. 
Definition qubit1 : Qubit := l2V [0;1].

Notation "∣ 0 ⟩" := qubit0.
Notation "∣ 1 ⟩" := qubit1.

Arguments qubit0 _ _ /.
Arguments qubit1 _ _ /.

(** Одно из полезных свойств этих базисных кубитов - возможность
    представить любой кубит как их линейную комбинацию *)
Lemma qubit_decomposition : forall (ϕ : Qubit), exists (α β : C), ϕ == α * ∣0⟩ + β * ∣1⟩.
Proof.
  (* WORKED IN CLASS *)
  intros.
  exists (ϕ 0 0)%nat, (ϕ 1 0)%nat.
  lma.
Qed.
  
(** Кубит называется валидным, если ⎸α⎸² + ⎸β⎸² = 1. *)
Definition WF_Qubit (ϕ : Qubit) : Prop := (⎸(ϕ 0 0)%nat⎸² + ⎸(ϕ 1 0)%nat⎸² = 1)%C.

(** Обратите внимание, что это утверждение эквивалентно тому, что [⟨ϕ,ϕ⟩ = 1],
    что частично объясняет нотацию для кубитов. *)

(** **** Exercise: 2 stars, standard, recommended (WF_Qubit_alt)  

    Докажите это утверждение. *)
Theorem WF_Qubit_alt : forall ϕ : Qubit, WF_Qubit ϕ <-> ϕ† × ϕ == I 1.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** Заметка: В emacs и других текстовых редакторах, так же как в известном 
    xkcd-комиксе или в любой достаточно развитой эстетике, не одобряют
    использование открывающих левых скобок без одновременного использования
    закрывающих правых. (Винить за такие обозначения следует Дирака.) Поскольку
    автоматическая табуляция перестает нормально работать в этом месте файла, 
    рекомендую отключить ее с помощью M-x electric-indent-mode. *) 

(** Покажем, что базисные кубиты - валидные. *)

Lemma WF_qubit0 : WF_Qubit ∣0⟩. Proof. lca. Qed.
Lemma WF_qubit1 : WF_Qubit ∣1⟩. Proof. lca. Qed.

(* ################################################################# *)
(** * Унитарные матрицы *)

(** 
    Обычно матрицы действуют на векторы посредством операции умножения.
    Если A - матрица размера n x n, а v - n-мерный вектор, то A v - 
    тоже n-мерный вектор.
    
    В квантовом случае мы хотим рассматривать только такие матрицы A,
    что для любого валидного кубита ϕ, кубит A ϕ тоже валидный. 
    Давайте разберемся, какому условию должна удовлетворять матрица,
    чтобы кубиты под ее действием сохраняли валидность.
 *)

Lemma valid_qubit_function : exists (P : Matrix 2 2 -> Prop),
  forall (A : Matrix 2 2) (ϕ : Qubit), 
  P A -> WF_Qubit ϕ -> WF_Qubit (A × ϕ).
Proof.
  (* WORKED IN CLASS *)
  eexists.
  intros A ϕ p Q.
  rewrite WF_Qubit_alt. 
  rewrite WF_Qubit_alt in Q. 
  unfold inner_product.
  rewrite Mmult_adjoint. 
  rewrite Mmult_assoc.
  rewrite <- (Mmult_assoc (A†)).
  assert (P: A† × A = I 2). apply p.
  rewrite P.
  rewrite Mmult_1_l.
  apply Q.
Qed.
  
(** Эти матрицы матрицы называются унитарными. Они сохраняют
    скалярное произведение. *)

Notation Unitary n := (Matrix n n).

Definition WF_Unitary {n} (U : Unitary n) := U † × U == I n. 

(** Для начала посмотрим на пять полезных унитарных матриц:
    матрицы Паули I, X, Y и Z, и матрица Адамара H (Hadamard). *)

Definition X : Unitary 2 := l2M [[0;1];
                                 [1;0]].

Lemma WF_X : WF_Unitary X. Proof. lma. Qed.

Lemma X0 : X × ∣0⟩ == ∣1⟩. Proof. lma. Qed.
Lemma X1 : X × ∣1⟩ == ∣0⟩. Proof. lma. Qed.

Definition Y : Unitary 2 := l2M [[0; -i];
                                 [i;  0]].

Lemma WF_Y : WF_Unitary Y. Proof. lma. Qed.

Lemma Y0 : Y × ∣0⟩ == i * ∣1⟩. Proof. lma. Qed.
Lemma Y1 : Y × ∣1⟩ == -i * ∣0⟩. Proof. lma. Qed.


Definition Z : Unitary 2 := l2M [[1; 0];
                                 [0; -(1)]].

Lemma WF_Z : WF_Unitary Z. Proof. lma. Qed.

Lemma Z0 : Z × ∣0⟩ == ∣0⟩. Proof. lma. Qed.
Lemma Z1 : Z × ∣1⟩ == -(1) * ∣1⟩. Proof. lma. Qed.

Definition H : Unitary 2 := l2M [[/√2; /√2];
                                 [/√2;-/√2]].

Lemma WF_H : WF_Unitary H. 
Proof. 
  unfold WF_Unitary, H; autounfold with U_db; simpl.
  by_cell; try lca.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
  - apply c_proj_eq; simpl; try lra.
    field_simplify.
    repeat rewrite pown_sqrt; simpl; lra.
    nonzero.
Qed.

Definition q_plus : Qubit := l2V [/√2; /√2].
Definition q_minus : Qubit := l2V [/√2; -/√2]. 

Arguments q_plus _ _ /.
Arguments q_minus _ _ /.

Notation "∣ + ⟩" := q_plus.
Notation "∣ - ⟩" := q_minus.

Lemma H0 : H × ∣0⟩ == ∣+⟩. Proof. lma. Qed.
Lemma H1 : H × ∣1⟩ == ∣-⟩. Proof. lma. Qed.

(** Отметим, что если два раза применить преобразование Адамара, 
    получится тот же результат: *)

Lemma Hplus : H × ∣+⟩ == ∣0⟩.
Proof.
  unfold H, Mmult, q_plus; simpl.
  by_cell; simpl; try lca.
  C_field_simplify. 
  lca.
Qed.

Lemma Hminus : H × ∣-⟩ == ∣ 1 ⟩.
Proof. 
  unfold H, Mmult, q_minus; simpl.
  by_cell; C_field_simplify; lca.
Qed.

(** **** Exercise: 2 stars, standard, recommended (Htwice)  

    Докажите, что применение H дважды не изменит состояние любого кубита. *)
Theorem Htwice : forall ϕ : Qubit, H × (H × ϕ) == ϕ.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

(** * Измерение **)

(** Измерение это вероятностная операция на кубите. Поскольку у операции 
    измерения кубита могут быть различные результаты, мы представим измерение
    как отношение.

    Обратите внимание, что некоторые измерения (те, у которых вероятность 0),
    никогда не произойдут.
*)

Inductive measure : Qubit -> (R * Qubit) -> Prop :=
| measure0 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 0%nat 0%nat ⎸², ∣0⟩)
| measure1 : forall (ϕ : Qubit), measure ϕ (⎸ϕ 1%nat 0%nat ⎸², ∣1⟩). 

(** **** Exercise: 3 stars, standard, optional (measure_sum)  

    Сформулируйте и докажите теорему о том, что сумма измерений у валидного кубита 
    равна 1.
 
    Подсказка: Сравните определения norm2 и inner_product. *)
(* FILL IN HERE *)

(** [] *)

Lemma measure0_idem : forall ϕ p, measure ∣0⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣0⟩.
Proof.
  (* WORKED IN CLASS *)
  intros ϕ p M NZ.
  inversion M; subst.
  - reflexivity.
  - contradict NZ. lra.
Qed.
  
(** **** Exercise: 1 star, standard, recommended (measure1_idem)  *)
Lemma measure1_idem : forall ϕ p, measure ∣1⟩ (p, ϕ) -> p <> 0%R -> ϕ = ∣1⟩.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Lemma measure_plus : forall ϕ p, measure ∣+⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  intros ϕ p M.
  inversion M; subst. 
  - R_field.
  - R_field.
Qed.

(** **** Exercise: 2 stars, standard, recommended (measure_minus)  *)
Lemma measure_minus : forall ϕ p, measure ∣-⟩ (p, ϕ) -> p = (1/2)%R.
Proof.
  (* FILL IN HERE *) Admitted.
(** [] *)

Hint Unfold H X Y Z qubit0 qubit1 q_plus q_minus : U_db. 

(* *)

(* Sun Jan 19 21:29:28 CST 2020 *)
