/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 练习6：归纳谓词

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：偶数与奇数

`Even`谓词对于偶数为`True`，对于奇数为`False`。 -/

#check Even

/- 我们将`Odd`定义为`Even`的否定： -/

def Odd (n : ℕ) : Prop :=
  ¬ Even n

/- 1.1. 证明1是奇数，并将此事实注册为simp规则。

提示：使用`cases`或`induction`来推理形如`Even …`的假设。 -/

@[simp] theorem Odd_1 :
    Odd 1 :=
  sorry

/- 1.2. 证明3和5是奇数。 -/

-- 在此处输入你的答案

/- 1.3. 通过结构归纳完成以下证明。 -/

theorem Even_two_times :
    ∀m : ℕ, Even (2 * m)
  | 0     => Even.zero
  | m + 1 =>
    sorry


/- ## 问题2：网球比赛

回顾演示中的网球比分归纳类型： -/

#check Score

/- 2.1. 定义一个归纳谓词，当发球方领先时返回`True`，否则返回`False`。 -/

inductive ServAhead : Score → Prop
  -- 在此处补充缺失的案例

/- 2.2. 通过证明以下定理来验证你的谓词定义。 -/

theorem ServAhead_vs {m n : ℕ} (hgt : m > n) :
    ServAhead (Score.vs m n) :=
  sorry

theorem ServAhead_advServ :
    ServAhead Score.advServ :=
  sorry

theorem not_ServAhead_advRecv :
    ¬ ServAhead Score.advRecv :=
  sorry

theorem ServAhead_gameServ :
    ServAhead Score.gameServ :=
  sorry

theorem not_ServAhead_gameRecv :
    ¬ ServAhead Score.gameRecv :=
  sorry

/- 2.3. 将上述定理陈述与你的定义进行比较。你观察到了什么？ -/

-- 在此处输入你的答案


/- ## 问题3：二叉树

3.1. 证明`IsFull_mirror`的逆命题。你可以利用已证明的定理（例如`IsFull_mirror`、`mirror_mirror`）。 -/

#check IsFull_mirror
#check mirror_mirror

theorem mirror_IsFull {α : Type} :
    ∀t : Tree α, IsFull (mirror t) → IsFull t :=
  sorry

/- 3.2. 为二叉树定义一个`map`函数，类似于`List.map`。 -/

def Tree.map {α β : Type} (f : α → β) : Tree α → Tree β :=
  sorry

/- 3.3. 通过案例分析证明以下定理。 -/

theorem Tree.map_eq_empty_iff {α β : Type} (f : α → β) :
    ∀t : Tree α, Tree.map f t = Tree.nil ↔ t = Tree.nil :=
  sorry

/- 3.4 (**选做**). 通过规则归纳证明以下定理。 -/

theorem map_mirror {α β : Type} (f : α → β) :
    ∀t : Tree α, IsFull t → IsFull (Tree.map f t) :=
  sorry

end LoVe

