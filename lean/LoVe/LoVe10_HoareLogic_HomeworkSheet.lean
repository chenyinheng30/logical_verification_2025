/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe09_OperationalSemantics_ExerciseSheet
import LoVe.LoVe10_HoareLogic_Demo


/- # LoVe 第10次作业（10分 + 1附加分）：霍尔逻辑

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（5分）：阶乘

以下WHILE程序旨在计算 `n₀` 的阶乘，结果存储在 `r` 中。 -/

def FACT : Stmt :=
  Stmt.assign "i" (fun s ↦ 0);
  Stmt.assign "r" (fun s ↦ 1);
  Stmt.whileDo (fun s ↦ s "i" ≠ s "n")
    (Stmt.assign "i" (fun s ↦ s "i" + 1);
     Stmt.assign "r" (fun s ↦ s "r" * s "i"))

/- 回忆 `fact` 函数的定义： -/

#print fact

/- 让我们使用一些新的Lean语法将其递归方程注册为简化规则，
以增强简化器和 `aesop` 的能力： -/

attribute [simp] fact

/- 使用 `vcg` 证明 `FACT` 的正确性。

提示：记得用 `s "n" = n₀` 强化循环不变量，
以捕获变量 `n` 不变的事实。 -/

theorem FACT_correct (n₀ : ℕ) :
    {* fun s ↦ s "n" = n₀ *} (FACT) {* fun s ↦ s "r" = fact n₀ *} :=
  sorry


/- ## 问题2（5分 + 1附加分）：
## 卫式命令语言的霍尔逻辑

回忆练习9中GCL的定义： -/

namespace GCL

#check Stmt
#check BigStep

/- 部分正确性的霍尔逻辑三元组定义并不意外： -/

def PartialHoare (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀s t, P s → (S, s) ⟹ t → Q t

macro (priority := high) "{*" P:term " *} " "(" S:term ")" " {* " Q:term " *}" :
  term =>
  `(PartialHoare $P $S $Q)

namespace PartialHoare

/- 2.1（5分）。证明以下霍尔规则： -/

theorem consequence {P P' Q Q' S} (h : {* P *} (S) {* Q *})
      (hp : ∀s, P' s → P s) (hq : ∀s, Q s → Q' s) :
    {* P' *} (S) {* Q' *} :=
  sorry

theorem assign_intro {P x a} :
    {* fun s ↦ P (s[x ↦ a s]) *} (Stmt.assign x a) {* P *} :=
  sorry

theorem assert_intro {P Q : State → Prop} :
    {* fun s ↦ Q s → P s *} (Stmt.assert Q) {* P *} :=
  sorry

theorem seq_intro {P Q R S T}
      (hS : {* P *} (S) {* Q *}) (hT : {* Q *} (T) {* R *}) :
    {* P *} (Stmt.seq S T) {* R *} :=
  sorry

theorem choice_intro {P Q Ss}
      (h : ∀i (hi : i < List.length Ss), {* P *} (Ss[i]'hi) {* Q *}) :
    {* P *} (Stmt.choice Ss) {* Q *} :=
  sorry

/- 2.2（1附加分）。证明 `loop` 的规则。注意与WHILE语言中 `while` 规则的相似性。 -/

theorem loop_intro {P S} (h : {* P *} (S) {* P *}) :
    {* P *} (Stmt.loop S) {* P *} :=
  sorry

end PartialHoare

end GCL

end LoVe

