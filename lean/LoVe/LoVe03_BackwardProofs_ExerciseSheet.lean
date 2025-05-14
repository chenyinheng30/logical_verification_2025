/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe 练习3：逆向证明

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## 问题1：连接词与量词

1.1. 使用基本策略完成以下证明。

提示：在《指南》第3.3节末尾描述了一些进行此类证明的策略。 -/

theorem I (a : Prop) :
    a → a :=
  by
    intro ha
    exact ha

theorem K (a b : Prop) :
    a → b → b :=
  by
    intro ha hb
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intro habc hb ha
    exact habc ha hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intro ha _
    exact ha

/- 请给出与`proj_fst`不同的解答： -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intro _ ha
    exact ha

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intro _ ha hac _
    exact hac ha

/- 1.2. 使用基本策略证明逆否命题规则。 -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intro hab hnb ha
    apply hnb
    apply hab
    exact ha

/- 1.3. 使用基本策略证明`∀`对`∧`的分配律。

提示：本题较难，尤其是从右到左的方向。可能需要像讲座中`and_swap_braces`证明那样的正向推理。 -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    intro hl
    apply And.intro
    { intro x
      exact And.left (hl x) }
    { intro x
      exact And.right (hl x) }
    intro hr _
    apply And.intro
    { apply And.left hr }
    { apply And.right hr }


/- ## 问题2：自然数

2.1. 证明以下关于第一讲中定义的`mul`运算符第一个参数的递归等式。 -/

#check mul

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n with
    | zero  => rfl
    | succ n' ih => simp [add, mul, ih]

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
    | zero  => rfl
    | succ n' ih =>
      simp [add, add_comm,  mul, ih]
      ac_rfl

/- 2.2. 使用`induction`策略证明乘法的交换律和结合律。注意谨慎选择归纳变量。 -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  by
    induction n with
    | zero  =>
      simp [mul, mul_zero]
    | succ n' ih =>
      simp [mul, mul_succ, add_comm, ih]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
    | zero =>
      simp [mul]
    | succ n' ih =>
      simp [mul, mul_add, ih]

/- 2.3. 使用`rw`证明`mul_add`的对称变体。要在特定位置应用交换律，可以通过传递参数（例如`mul_comm _ l`）来实例化规则。 -/

theorem add_mul (l m n : ℕ) :
    mul (add l m) n = add (mul n l) (mul n m) :=
  by
    induction n with
    | zero =>
      rw [mul, mul_zero, mul_zero, add_zero]
    | succ n' ih =>
      simp [mul, mul_succ, ih]
      rw [add_comm _ l, add_assoc, add_assoc]
      rw [add_comm m _, add_assoc]

/- ## 问题3（选做）：直觉主义逻辑

直觉主义逻辑通过假设一个经典公理扩展为经典逻辑。公理的选择有多种可能性。本题中，我们关注三个不同公理的逻辑等价性： -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- 在下面的证明中，避免使用Lean的`Classical`命名空间中的定理。

3.1（选做）. 使用策略证明以下蕴含关系。

提示：你将需要用到`Or.elim`和`False.elim`。可以使用`rw [ExcludedMiddle]`来展开`ExcludedMiddle`的定义，其他公理同理。 -/

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  by
    rw [ExcludedMiddle, Peirce]
    intro hem ha hb haba
    apply Or.elim (hem ha)
    { intro hha
      exact hha }
    { intro hna
      apply haba
      intro hha
      exact False.elim (hna hha) }

/- 3.2（选做）. 使用策略证明以下蕴含关系。 -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  by
    rw [Peirce, DoubleNegation]
    intro hp ha hna
    apply hp ha
    intro hha
    exact False.elim (hna hha)

/- 剩下的蕴含关系留作课后作业： -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    rw [DoubleNegation, ExcludedMiddle]
    intro hnd ha
    apply hnd
    intro hor
    apply hor
    apply Or.inl
    apply hnd
    intro hna
    apply hor
    apply Or.inr
    apply hnd
    intro hnna
    exact False.elim (hnna hna)


end SorryTheorems

end BackwardProofs

end LoVe
