/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 练习4：前向证明 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：连接词与量词

1.1. 为以下定理提供结构化证明。 -/

theorem I (a : Prop) :
    a → a :=
  assume ha : a
  show a from
    ha


theorem K (a b : Prop) :
    a → b → b :=
  assume ha : a
  assume hb : b
  show b from
    hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  assume habc : a → b → c
  assume hb : b
  assume ha : a
  show c from
    habc ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha

/- 请给出与 `proj_fst` 不同的答案。 -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  assume ha : a
  assume ha' : a
  show a from
    ha'

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  assume habc : a → b → c
  assume ha : a
  assume hac : a → c
  assume hb : b
  show c from
    hac ha

/- 1.2. 为反证规则提供结构化证明。 -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  assume hab : a → b
  assume hnb : b → False
  assume ha : a
  show False from
    hnb (hab ha)

/- 1.3. 为 `∀` 对 `∧` 的分配律提供结构化证明。 -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  Iff.intro
    (assume hall : (∀x, p x ∧ q x)
     And.intro
       (fix ha : α
        show p ha from
          And.left (hall ha))
       (fix ha : α
        show q ha from
          And.right (hall ha)))
    (assume hand : (∀x, p x) ∧ (∀x, q x)
     fix ha : α
     And.intro
       ((And.left hand) ha)
       ((And.right hand) ha))

/- 1.4 (**选做**). 为以下性质提供结构化证明，
该性质可用于将 `∀` 量词移过 `∃` 量词。 -/

theorem forall_exists_of_exists_forall {α : Type} (p : α → α → Prop) :
    (∃x, ∀y, p x y) → (∀y, ∃x, p x y) :=
  assume hexists : (∃x, ∀y, p x y)
  (Exists.elim hexists
     (assume ha : α
      assume hall : (∀ (y : α), p ha y)
      assume ha' : α
      Exists.intro
        (ha)
        (hall ha')))


/- ## 问题2：等式链

2.1. 使用 `calc` 编写以下证明。

      (a + b) * (a + b)
    = a * (a + b) + b * (a + b)
    = a * a + a * b + b * a + b * b
    = a * a + a * b + a * b + b * b
    = a * a + 2 * a * b + b * b

提示：这是一个难题。你可能需要用到策略 `simp` 和 `ac_rfl`，
以及一些定理 `mul_add`, `add_mul`, `add_comm`, `add_assoc`,
`mul_comm`, `mul_assoc`, 和 `Nat.two_mul`。 -/

theorem binomial_square (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  calc
    (a + b) * (a + b) = (a + b) * a + (a + b) * b :=
      by rw [mul_add]
    _ = a * a + b * a + a * b + b * b :=
      by simp [add_mul, add_assoc]
    _ = a * a + a * b + a * b + b * b :=
      by simp [mul_comm]
    _ = a * a + 2 * a * b + b * b :=
      by simp [add_assoc, ←Nat.two_mul, mul_assoc]

/- 2.2 (**选做**). 再次证明相同的命题，这次使用结构化证明，
用 `have` 步骤对应 `calc` 等式。尽量复用上述证明思路，机械地进行。 -/

theorem binomial_square₂ (a b : ℕ) :
    (a + b) * (a + b) = a * a + 2 * a * b + b * b :=
  have hma : (a + b) * (a + b) = (a + b) * a + (a + b) * b :=
      by rw [mul_add]
  have ham : (a + b) * (a + b) = a * a + b * a + a * b + b * b :=
      by simp [hma, add_mul, add_assoc]
  have hmc : (a + b) * (a + b) = a * a + a * b + a * b + b * b :=
      by simp [ham, mul_comm]
  show _ from
    by simp [hmc, add_assoc, ←Nat.two_mul, mul_assoc]


/- ## 问题3 (**选做**)：单点规则

3.1 (**选做**). 用结构化证明证明以下错误的 `∀` 单点规则公式是不一致的。 -/

axiom All.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∀x : α, x = t ∧ P x) ↔ P t

theorem All.proof_of_False :
    False :=
  sorry /- TODO -/

/- 3.2 (**选做**). 用结构化证明证明以下错误的 `∃` 单点规则公式是不一致的。 -/

axiom Exists.one_point_wrong {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t → P x) ↔ P t

theorem Exists.proof_of_False :
    False :=
  sorry /- TODO -/

end LoVe
