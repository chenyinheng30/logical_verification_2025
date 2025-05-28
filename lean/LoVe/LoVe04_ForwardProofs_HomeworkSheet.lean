/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe 家庭作业4（10分）：正向证明

将占位符（例如 `:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1（4分）：逻辑谜题

考虑以下策略证明： -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    { intro hna
      apply False.elim
      apply hna
      exact ha }
    { intro hb
      exact hb }

/- 1.1（2分）。再次证明相同的定理，这次提供一个证明项。

提示：有一个简单的方法。 -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fun (a b : Prop) (hor : ¬ a ∨ b) (ha : a) ↦
    Or.elim hor
      (λ hna ↦ False.elim (hna ha))
      (λ hb ↦ hb)

/- 1.2（2分）。再次证明相同的定理，这次提供一个结构化证明，使用 `fix`、`assume` 和 `show`。 -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume hor : ¬ a ∨ b
  assume ha : a
  Or.elim hor
  (assume hna : ¬ a
   show b from
     False.elim (hna ha))
  (assume hb : b
   show b from hb)

/- ## 问题2（6分）：连接词和量词

2.1（3分）。提供一个结构化证明，证明在 `∀` 量词下 `∨` 的交换律，仅使用 `∀`、`∨` 和 `↔` 的引入和消去规则，不使用其他定理。 -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
    (assume hpq : (∀x, p x ∨ q x)
     fix ha : α
     Or.elim (hpq ha)
       (assume hp : p ha
        show q ha ∨ p ha from
          Or.inr hp)
       (assume hq : q ha
        show q ha ∨ p ha from
          Or.inl hq))
    (assume hqp : (∀x, q x ∨ p x)
     fix ha : α
     Or.elim (hqp ha)
       (assume hq : q ha
        show p ha ∨ q ha from
          Or.inr hq)
       (assume hp : p ha
        show p ha ∨ q ha from
          Or.inl hp))

/- 2.2（3分）。我们在第3讲的练习中已经证明或陈述了 `ExcludedMiddle`、`Peirce` 和 `DoubleNegation` 之间六种可能蕴含关系中的三种。利用我们已经有的三个定理，用结构化证明证明剩下的三个缺失的蕴含关系。 -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  assume hdn : DoubleNegation
  fix a b : Prop
  assume haba : (a → b) → a
  hdn a
  assume hna : ¬a
  have ha : a :=
    haba
    assume ha : a
    show b from
      False.elim (hna ha)
  hna ha

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume hp : (∀a b : Prop, ((a → b) → a) → a)
  fix ha : Prop
  hp (ha ∨ ¬ha) False
  assume hor : ¬(ha ∨ ¬ha)
  have hna : ¬ha :=
    by
      intro ha'
      apply hor
      apply Or.inl
      exact ha'
  Or.inr
  assume ha' : ha
  False.elim (hna ha')

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume hem : ExcludedMiddle
  fix a : Prop
  assume hnna : ¬¬a
  Or.elim (hem a)
  (assume ha : a
   show a from
     ha)
  (assume hna : ¬a
   show a from
     False.elim (hnna hna))

end BackwardProofs

end LoVe
