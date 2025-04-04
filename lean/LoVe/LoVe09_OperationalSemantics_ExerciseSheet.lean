/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 练习9：操作语义

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：守卫命令语言

1976年，E. W. Dijkstra提出了守卫命令语言（GCL），这是一种具有内置非确定性的极简命令式语言。以下是其一个变体的语法：

    S  ::=  x := e       -- 赋值
         |  assert B     -- 断言
         |  S ; S        -- 顺序组合
         |  S | ⋯ | S    -- 非确定性选择
         |  loop S       -- 非确定性迭代

赋值和顺序组合与WHILE语言相同。其他语句的语义如下：

* `assert B` 如果`B`求值为false则中止；否则该命令无操作。

* `S | ⋯ | S` 选择任意一个分支执行，忽略其他分支。

* `loop S` 执行`S`任意次数。

在Lean中，GCL由以下归纳类型捕获： -/

namespace GCL

inductive Stmt : Type
  | assign : String → (State → ℕ) → Stmt
  | assert : (State → Prop) → Stmt
  | seq    : Stmt → Stmt → Stmt
  | choice : List Stmt → Stmt
  | loop   : Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 1.1. 根据上述GCL的非正式规范，完成以下大步语义。 -/

inductive BigStep : (Stmt × State) → State → Prop
  -- 在此处补充缺失的`assign`规则
  | assert (B s) (hB : B s) :
    BigStep (Stmt.assert B, s) s
  -- 在此处补充缺失的`seq`规则
  -- 下面，`Ss[i]'hless`返回`Ss`的第`i`个元素，由于条件`hless`保证其存在
  | choice (Ss s t i) (hless : i < List.length Ss)
      (hbody : BigStep (Ss[i]'hless, s) t) :
    BigStep (Stmt.choice Ss, s) t
  -- 在此处补充缺失的`loop`规则

infixl:110 " ⟹ " => BigStep

/- 1.2. 如我们在WHILE语言的讲座中所做的那样，证明以下反演规则。 -/

@[simp] theorem BigStep_assign_iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  sorry

@[simp] theorem BigStep_assert {B s t} :
    (Stmt.assert B, s) ⟹ t ↔ t = s ∧ B s :=
  sorry

@[simp] theorem BigStep_seq_iff {S₁ S₂ s t} :
    (Stmt.seq S₁ S₂, s) ⟹ t ↔ (∃u, (S₁, s) ⟹ u ∧ (S₂, u) ⟹ t) :=
  sorry

theorem BigStep_loop {S s u} :
    (Stmt.loop S, s) ⟹ u ↔
    (s = u ∨ (∃t, (S, s) ⟹ t ∧ (Stmt.loop S, t) ⟹ u)) :=
  sorry

/- 这个更有难度： -/

@[simp] theorem BigStep_choice {Ss s t} :
    (Stmt.choice Ss, s) ⟹ t ↔
    (∃(i : ℕ) (hless : i < List.length Ss), (Ss[i]'hless, s) ⟹ t) :=
  sorry

end GCL

/- 1.3. 通过填充下面的`sorry`占位符，完成以下确定性程序到GCL程序的转换。 -/

def gcl_of : Stmt → GCL.Stmt
  | Stmt.skip =>
    GCL.Stmt.assert (fun _ ↦ True)
  | Stmt.assign x a =>
    sorry
  | S; T =>
    sorry
  | Stmt.ifThenElse B S T  =>
    sorry
  | Stmt.whileDo B S =>
    sorry

/- 1.4. 在上述`gcl_of`的定义中，`skip`被转换为`assert (fun _ ↦ True)`。通过比较两种结构的大步语义，我们可以确认这是合理的。你能想到其他正确的方式来定义`skip`的情况吗？ -/

-- 在此处输入你的答案


/- ## 问题2：程序等价性

对于这个问题，我们引入程序等价性的概念：`S₁ ~ S₂`。 -/

def BigStepEquiv (S₁ S₂ : Stmt) : Prop :=
  ∀s t, (S₁, s) ⟹ t ↔ (S₂, s) ⟹ t

infix:50 (priority := high) " ~ " => BigStepEquiv

/- 程序等价性是一种等价关系，即它是自反的、对称的和传递的。 -/

theorem BigStepEquiv.refl {S} :
    S ~ S :=
  fix s t : State
  show (S, s) ⟹ t ↔ (S, s) ⟹ t from
    by rfl

theorem BigStepEquiv.symm {S₁ S₂} :
    S₁ ~ S₂ → S₂ ~ S₁ :=
  assume h : S₁ ~ S₂
  fix s t : State
  show (S₂, s) ⟹ t ↔ (S₁, s) ⟹ t from
    Iff.symm (h s t)

theorem BigStepEquiv.trans {S₁ S₂ S₃} (h₁₂ : S₁ ~ S₂) (h₂₃ : S₂ ~ S₃) :
    S₁ ~ S₃ :=
  fix s t : State
  show (S₁, s) ⟹ t ↔ (S₃, s) ⟹ t from
    Iff.trans (h₁₂ s t) (h₂₃ s t)

/- 2.1. 证明以下程序等价性。 -/

theorem BigStepEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  sorry

theorem BigStepEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  sorry

theorem BigStepEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  sorry

theorem BigStepEquiv.if_seq_while_skip {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip ~ Stmt.whileDo B S :=
  sorry

/- 2.2 (**可选**). 程序等价性可用于将子程序替换为具有相同语义的其他子程序。证明以下所谓的同余规则以促进此类替换： -/

theorem BigStepEquiv.seq_congr {S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂)
      (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  sorry

theorem BigStepEquiv.if_congr {B S₁ S₂ T₁ T₂} (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  sorry

end LoVe

