/- 版权声明 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 演示9：操作语义

在本讲及接下来两讲中，我们将了解如何使用Lean来规定编程语言的语法和语义，并对语义进行推理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 首要事项：形式化项目

作为两次作业的替代，你可以选择完成一个验证项目，价值20分。如果选择此选项，请在本周末前通过电子邮件告知授课教师。对于一个完全成功的项目，我们期望约200行（或更多）的Lean代码，包括定义和证明。

以下是一些项目构想：

计算机科学：

* 扩展WHILE语言，增加静态数组或其他特性；
* 函数式数据结构（如平衡树）；
* 函数式算法（如冒泡排序、归并排序、Tarjan算法）；
* 从表达式或命令式程序到（例如）栈机器的编译器；
* 类型系统（如Benjamin Pierce的《类型与编程语言》）；
* 安全属性（如Volpano-Smith风格的非干涉分析）；
* 一阶项理论，包括匹配、项重写；
* 自动机理论；
* 上下文无关文法或正则表达式的规范化；
* 进程代数和互模拟；
* 证明系统的可靠性和可能的完备性（如Genzen的相继式演算、自然演绎、表系统）；
* 分离逻辑；
* 使用Hoare逻辑的验证程序。

数学：

* 图论；
* 组合数学；
* 数论。

元编程：

* 自定义策略；
* 自定义诊断工具。

过往评价：

问：你觉得项目如何？

答：很愉快。

答：有趣且困难。

答：很好，我认为这种形式非常棒，它给了人们完成挑战性练习并提交不完整作业的机会。

答：我真的很喜欢。这是一种很棒的学习方式——找到你感兴趣的东西，深入一点，遇到困难时寻求帮助。我希望我能多做些这样的项目！

答：能有时间自己研究感兴趣的内容真是太棒了。

答：实际上非常有趣！！！

答：非常有帮助。它提供了更多时间专注于课程的特定方面。


## 形式语义

形式语义有助于规定和推理编程语言本身以及单个程序。

它可以构成验证编译器、解释器、验证器、静态分析器、类型检查器等的基础。没有形式化证明，这些工具几乎总是错误的。

在这一领域，证明助手被广泛使用。每年，约10-20%的POPL论文部分或全部形式化。成功的原因：

* 开始所需的机制（背景库、策略）很少，只需归纳类型、谓词和递归函数。

* 证明往往有很多情况，这与计算机非常匹配。

* 证明助手会跟踪在扩展编程语言功能时需要更改的内容。

典型案例：WebAssembly。引用Conrad Watt（略有缩写）：

    我们完成了WebAssembly语言核心执行语义和类型系统的完整Isabelle机械化。为了完成这个证明，官方WebAssembly规范中的几个缺陷（由我们的证明和建模工作发现）需要修正。在某些情况下，这意味着类型系统最初是不健全的。

    我们与工作组保持了建设性对话，验证新增功能。特别是，WebAssembly实现与主机环境交互的机制在工作组原始论文中没有正式规定。扩展我们的机械化模型以涵盖这一特性揭示了WebAssembly规范中的一个缺陷，破坏了类型系统的健全性。


## 极简命令式语言

状态`s`是从变量名到值的函数（`String → ℕ`）。

__WHILE__是一种极简命令式语言，语法如下：

    S  ::=  skip                 -- 空操作
         |  x := a               -- 赋值
         |  S; S                 -- 顺序组合
         |  if B then S else S   -- 条件语句
         |  while B do S         -- while循环

其中`S`表示语句（也称为命令或程序），`x`表示变量，`a`表示算术表达式，`B`表示布尔表达式。 -/

#print State

inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → ℕ) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt

infixr:90 "; " => Stmt.seq

/- 在我们的语法中，我们有意不规定算术和布尔表达式的具体语法。在Lean中，我们有选择：

* 可以使用类似第2讲中的`AExp`类型，布尔表达式类似。

* 可以认为算术表达式就是从状态到自然数的函数（`State → ℕ`），布尔表达式是谓词（`State → Prop`或`State → Bool`）。

这对应于深嵌入和浅嵌入的区别：

* 某些语法（表达式、公式、程序等）的__深嵌入__由证明助手中规定的抽象语法树（如`AExp`）及其语义（如`eval`）组成。

* 相比之下，__浅嵌入__直接重用逻辑中的相应机制（如项、函数、谓词类型）。

深嵌入允许我们对语法（及其语义）进行推理。浅嵌入更轻量，因为可以直接使用，无需定义语义。

我们将对程序使用深嵌入（我们觉得有趣），对赋值和布尔表达式使用浅嵌入（我们觉得乏味）。

程序

  while x > y do
    skip;
    x := x - 1

建模为 -/

def sillyLoop : Stmt :=
  Stmt.whileDo (fun s ↦ s "x" > s "y")
    (Stmt.skip;
     Stmt.assign "x" (fun s ↦ s "x" - 1))


/- ## 大步语义

__操作语义__对应于理想化的解释器（用类似Prolog的语言规定）。两种主要变体：

* 大步语义；

* 小步语义。

在__大步语义__（也称为__自然语义__）中，判断形式为`(S, s) ⟹ t`：

    从状态`s`开始执行`S`，终止于状态`t`。

示例：

    `(x := x + y; y := 0, [x ↦ 3, y ↦ 5]) ⟹ [x ↦ 8, y ↦ 0]`

推导规则：

    ——————————————— Skip
    (skip, s) ⟹ s

    ——————————————————————————— Assign
    (x := a, s) ⟹ s[x ↦ s(a)]

    (S, s) ⟹ t   (T, t) ⟹ u
    ——————————————————————————— Seq
    (S; T, s) ⟹ u

    (S, s) ⟹ t
    ————————————————————————————— If-True   若s(B)为真
    (if B then S else T, s) ⟹ t

    (T, s) ⟹ t
    ————————————————————————————— If-False  若s(B)为假
    (if B then S else T, s) ⟹ t

    (S, s) ⟹ t   (while B do S, t) ⟹ u
    —————————————————————————————————————— While-True   若s(B)为真
    (while B do S, s) ⟹ u

    ————————————————————————— While-False   若s(B)为假
    (while B do S, s) ⟹ s

其中`s(e)`表示状态`s`中表达式`e`的值，`s[x ↦ s(e)]`表示与`s`相同的状态，除了变量`x`绑定到值`s(e)`。

在Lean中，判断对应于归纳谓词，推导规则对应于谓词的引入规则。使用归纳谓词而非递归函数可以处理非终止（如发散的`while`）和非确定性（如多线程）。 -/

inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
    BigStep (Stmt.skip, s) s
  | assign (x a s) :
    BigStep (Stmt.assign x a, s) (s[x ↦ a s])
  | seq (S T s t u) (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
    BigStep (S; T, s) u
  | if_true (B S T s t) (hcond : B s)
      (hbody : BigStep (S, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t) (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
    BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u) (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
    BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s) (hcond : ¬ B s) :
    BigStep (Stmt.whileDo B S, s) s

infix:110 " ⟹ " => BigStep

theorem sillyLoop_from_1_BigStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⟹ (fun _ ↦ 0) :=
  by
    rw [sillyLoop]
    apply BigStep.while_true
    { simp }
    { apply BigStep.seq
      { apply BigStep.skip }
      { apply BigStep.assign } }
    { simp
      apply BigStep.while_false
      simp }


/- ## 大步语义的性质

有了大步语义，我们可以：

* 证明编程语言的性质，如程序间的等价性证明和确定性；

* 对具体程序进行推理，证明关于初始状态`s`和最终状态`t`的定理。 -/

theorem BigStep_deterministic {Ss l r} (hl : Ss ⟹ l)
      (hr : Ss ⟹ r) :
    l = r :=
  by
    induction hl generalizing r with
    | skip s =>
      cases hr with
      | skip => rfl
    | assign x a s =>
      cases hr with
      | assign => rfl
    | seq S T s l₀ l hS hT ihS ihT =>
      cases hr with
      | seq _ _ _ r₀ _ hS' hT' =>
        cases ihS hS' with
        | refl =>
          cases ihT hT' with
          | refl => rfl
    | if_true B S T s l hB hS ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => apply ih hS'
      | if_false _ _ _ _ _ hB' hS' => aesop
    | if_false B S T s l hB hT ih =>
      cases hr with
      | if_true _ _ _ _ _ hB' hS'  => aesop
      | if_false _ _ _ _ _ hB' hS' => apply ih hS'
    | while_true B S s l₀ l hB hS hw ihS ihw =>
      cases hr with
      | while_true _ _ _ r₀ hB' hB' hS' hw' =>
        cases ihS hS' with
        | refl =>
          cases ihw hw' with
          | refl => rfl
      | while_false _ _ _ hB' => aesop
    | while_false B S s hB =>
      cases hr with
      | while_true _ _ _ s' _ hB' hS hw => aesop
      | while_false _ _ _ hB'           => rfl

/-
theorem BigStep_terminates {S s} :
    ∃t, (S, s) ⟹ t :=
  sorry   -- 不可证
-/

/- 我们可以定义关于大步语义的反演规则： -/

@[simp] theorem BigStep_skip_Iff {s t} :
    (Stmt.skip, s) ⟹ t ↔ t = s :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | skip => rfl }
    { intro h
      rw [h]
      apply BigStep.skip }

@[simp] theorem BigStep_assign_Iff {x a s t} :
    (Stmt.assign x a, s) ⟹ t ↔ t = s[x ↦ a s] :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | assign => rfl }
    { intro h
      rw [h]
      apply BigStep.assign }

@[simp] theorem BigStep_seq_Iff {S T s u} :
    (S; T, s) ⟹ u ↔ (∃t, (S, s) ⟹ t ∧ (T, t) ⟹ u) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | seq =>
        apply Exists.intro
        apply And.intro <;>
          assumption }
    { intro h
      cases h with
      | intro s' h' =>
        cases h' with
        | intro hS hT =>
          apply BigStep.seq <;>
            assumption }

@[simp] theorem BigStep_if_Iff {B S T s t} :
    (Stmt.ifThenElse B S T, s) ⟹ t ↔
    (B s ∧ (S, s) ⟹ t) ∨ (¬ B s ∧ (T, s) ⟹ t) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ _ hB hS =>
        apply Or.intro_left
        aesop
      | if_false _ _ _ _ _ hB hT =>
        apply Or.intro_right
        aesop }
    { intro h
      cases h with
      | inl h =>
        cases h with
        | intro hB hS =>
          apply BigStep.if_true <;>
            assumption
      | inr h =>
        cases h with
        | intro hB hT =>
          apply BigStep.if_false <;>
            assumption }

theorem BigStep_while_Iff {B S s u} :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (B s ∧ ∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u)
    ∨ (¬ B s ∧ u = s) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | while_true _ _ _ t _ hB hS hw => aesop
      | while_false _ _ _ hB => aesop }
    { intro h
      cases h with
      | inl hex =>
        cases hex with
        | intro t h =>
          cases h with
          | intro hB h =>
            cases h with
            | intro hS hwhile =>
              apply BigStep.while_true <;>
                assumption
      | inr h =>
        cases h with
        | intro hB hus =>
          rw [hus]
          apply BigStep.while_false
          assumption}

@[simp] theorem BigStep_while_true_Iff {B S s u}
      (hcond : B s) :
    (Stmt.whileDo B S, s) ⟹ u ↔
    (∃t, (S, s) ⟹ t ∧ (Stmt.whileDo B S, t) ⟹ u) :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]

@[simp] theorem BigStep_while_false_Iff {B S s t}
      (hcond : ¬ B s) :
    (Stmt.whileDo B S, s) ⟹ t ↔ t = s :=
  by
    rw [BigStep_while_Iff]
    simp [hcond]


/- ## 小步语义

大步语义：

* 不允许推理中间状态；

* 不能表达非终止或交错（对于多线程）。

__小步语义__（也称为__结构操作语义__）解决了上述问题。

判断形式为`(S, s) ⇒ (T, t)`：

    从状态`s`开始，执行`S`的一步，将我们留在状态`t`，剩余程序`T`待执行。

执行是有限或无限的链`(S₀, s₀) ⇒ (S₁, s₁) ⇒ …`。

对`(S, s)`称为__配置__。如果不存在形如`(S, s) ⇒ _`的转换，则称为__终止__。

示例：

      `(x := x + y; y := 0, [x ↦ 3, y ↦ 5])`
    `⇒ (skip; y := 0,       [x ↦ 8, y ↦ 5])`
    `⇒ (y := 0,             [x ↦ 8, y ↦ 5])`
    `⇒ (skip,               [x ↦ 8, y ↦ 0])`

推导规则：

    ————————————————————————————————— Assign
    (x := a, s) ⇒ (skip, s[x ↦ s(a)])

    (S, s) ⇒ (S', s')
    ———-——————————————————— Seq-Step
    (S; T, s) ⇒ (S'; T, s')

    ————————————————————— Seq-Skip
    (skip; S, s) ⇒ (S, s)

    ———————————————————————————————— If-True   若s(B)为真
    (if B then S else T, s) ⇒ (S, s)

    ———————————————————————————————— If-False  若s(B)为假
    (if B then S else T, s) ⇒ (T, s)

    ——————————————————————————————————————————————————————————————— While
    (while B do S, s) ⇒ (if B then (S; while B do S) else skip, s)

没有`skip`的规则（为什么？）。 -/

inductive SmallStep : Stmt × State → Stmt × State → Prop where
  | assign (x a s) :
    SmallStep (Stmt.assign x a, s) (Stmt.skip, s[x ↦ a s])
  | seq_step (S S' T s s') (hS : SmallStep (S, s) (S', s')) :
    SmallStep (S; T, s) (S'; T, s')
  | seq_skip (T s) :
    SmallStep (Stmt.skip; T, s) (T, s)
  | if_true (B S T s) (hcond : B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (S, s)
  | if_false (B S T s) (hcond : ¬ B s) :
    SmallStep (Stmt.ifThenElse B S T, s) (T, s)
  | whileDo (B S s) :
    SmallStep (Stmt.whileDo B S, s)
      (Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip, s)

infixr:100 " ⇒ " => SmallStep
infixr:100 " ⇒* " => RTC SmallStep

theorem sillyLoop_from_1_SmallStep :
    (sillyLoop, (fun _ ↦ 0)["x" ↦ 1]) ⇒*
    (Stmt.skip, (fun _ ↦ 0)) :=
  by
    rw [sillyLoop]
    apply RTC.head
    { apply SmallStep.whileDo }
    { apply RTC.head
      { apply SmallStep.if_true
        aesop }
      { apply RTC.head
        { apply SmallStep.seq_step
          apply SmallStep.seq_skip }
        { apply RTC.head
          { apply SmallStep.seq_step
            apply SmallStep.assign }
          { apply RTC.head
            { apply SmallStep.seq_skip }
            { apply RTC.head
              { apply SmallStep.whileDo }
              { apply RTC.head
                { apply SmallStep.if_false
                  simp }
                { simp
                  apply RTC.refl } } } } } } }

/- 有了小步语义，我们可以**定义**大步语义：

    `(S, s) ⟹ t` 当且仅当 `(S, s) ⇒* (skip, t)`

其中`r*`表示关系`r`的自反传递闭包。

或者，如果已经定义了大步语义，可以**证明**上述等价定理来验证我们的定义。

小步语义的主要缺点是我们现在有两个关系`⇒`和`⇒*`，推理往往更复杂。


## 小步语义的性质

我们可以证明配置`(S, s)`终止当且仅当`S = skip`。这确保我们没有遗漏推导规则。 -/

theorem SmallStep_final (S s) :
    (¬ ∃T t, (S, s) ⇒ (T, t)) ↔ S = Stmt.skip :=
  by
    induction S with
    | skip =>
      simp
      intros T t hstep
      cases hstep
    | assign x a =>
      simp
      apply Exists.intro Stmt.skip
      apply Exists.intro (s[x ↦ a s])
      apply SmallStep.assign
    | seq S T ihS ihT =>
      simp
      cases Classical.em (S = Stmt.skip) with
      | inl h =>
        rw [h]
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.seq_skip
      | inr h =>
        simp [h] at ihS
        cases ihS with
        | intro S' hS₀ =>
          cases hS₀ with
          | intro s' hS =>
            apply Exists.intro (S'; T)
            apply Exists.intro s'
            apply SmallStep.seq_step
            assumption
    | ifThenElse B S T ihS ihT =>
      simp
      cases Classical.em (B s) with
      | inl h =>
        apply Exists.intro S
        apply Exists.intro s
        apply SmallStep.if_true
        assumption
      | inr h =>
        apply Exists.intro T
        apply Exists.intro s
        apply SmallStep.if_false
        assumption
    | whileDo B S ih =>
      simp
      apply Exists.intro
        (Stmt.ifThenElse B (S; Stmt.whileDo B S)
           Stmt.skip)
      apply Exists.intro s
      apply SmallStep.whileDo

theorem SmallStep_deterministic {Ss Ll Rr}
      (hl : Ss ⇒ Ll) (hr : Ss ⇒ Rr) :
    Ll = Rr :=
  by
    induction hl generalizing Rr with
    | assign x a s =>
      cases hr with
      | assign _ _ _ => rfl
    | seq_step S S₁ T s s₁ hS₁ ih =>
      cases hr with
      | seq_step S S₂ _ _ s₂ hS₂ =>
        have hSs₁₂ :=
          ih hS₂
        aesop
      | seq_skip => cases hS₁
    | seq_skip T s =>
      cases hr with
      | seq_step _ S _ _ s' hskip => cases hskip
      | seq_skip                  => rfl
    | if_true B S T s hB =>
      cases hr with
      | if_true  => rfl
      | if_false => aesop
    | if_false B S T s hB =>
      cases hr with
      | if_true  => aesop
      | if_false => rfl
    | whileDo B S s =>
      cases hr with
      | whileDo => rfl

/- 我们也可以定义关于小步语义的反演规则。以下是三个例子： -/

theorem SmallStep_skip {S s t} :
    ¬ ((Stmt.skip, s) ⇒ (S, t)) :=
  by
    intro h
    cases h

@[simp] theorem SmallStep_seq_Iff {S T s Ut} :
    (S; T, s) ⇒ Ut ↔
    (∃S' t, (S, s) ⇒ (S', t) ∧ Ut = (S'; T, t))
    ∨ (S = Stmt.skip ∧ Ut = (T, s)) :=
  by
    apply Iff.intro
    { intro hST
      cases hST with
      | seq_step _ S' _ _ s' hS =>
        apply Or.intro_left
        apply Exists.intro S'
        apply Exists.intro s'
        aesop
      | seq_skip =>
        apply Or.intro_right
        aesop }
    {
      intro hor
      cases hor with
      | inl hex =>
        cases hex with
        | intro S' hex' =>
          cases hex' with
          | intro s' hand =>
            cases hand with
            | intro hS hUt =>
              rw [hUt]
              apply SmallStep.seq_step
              assumption
      | inr hand =>
        cases hand with
        | intro hS hUt =>
          rw [hS, hUt]
          apply SmallStep.seq_skip }

@[simp] theorem SmallStep_if_Iff {B S T s Us} :
    (Stmt.ifThenElse B S T, s) ⇒ Us ↔
    (B s ∧ Us = (S, s)) ∨ (¬ B s ∧ Us = (T, s)) :=
  by
    apply Iff.intro
    { intro h
      cases h with
      | if_true _ _ _ _ hB  => aesop
      | if_false _ _ _ _ hB => aesop }
    { intro hor
      cases hor with
      | inl hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_true
          assumption
      | inr hand =>
        cases hand with
        | intro hB hUs =>
          rw [hUs]
          apply SmallStep.if_false
          assumption }


/- ### 大步语义与小步语义的等价性（**可选**）

更重要的结果是大步语义与小步语义之间的联系：

    `(S, s) ⟹ t ↔ (S, s) ⇒* (Stmt.skip, t)`

其证明（如下）超出了本课程范围。 -/

theorem RTC_SmallStep_seq {S T s u}
      (h : (S, s) ⇒* (Stmt.skip, u)) :
    (S; T, s) ⇒* (Stmt.skip; T, u) :=
  by
    apply RTC.lift (fun Ss ↦ (Prod.fst Ss; T, Prod.snd Ss)) _ h
    intro Ss Ss' hrtc
    cases Ss with
    | mk S s =>
      cases Ss' with
      | mk S' s' =>
        apply SmallStep.seq_step
        assumption

theorem RTC_SmallStep_of_BigStep {Ss t} (hS : Ss ⟹ t) :
    Ss ⇒* (Stmt.skip, t) :=
  by
    induction hS with
    | skip => exact RTC.refl
    | assign =>
      apply RTC.single
      apply SmallStep.assign
    | seq S T s t u hS hT ihS ihT =>
      apply RTC.trans
      { exact RTC_SmallStep_seq ihS }
      { apply RTC.head
        apply SmallStep.seq_skip
        assumption }
    | if_true B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_true
        assumption }
      { assumption }
    | if_false B S T s t hB hst ih =>
      apply RTC.head
      { apply SmallStep.if_false
        assumption }
      { assumption }
    | while_true B S s t u hB hS hw ihS ihw =>
      apply RTC.head
      { apply SmallStep.whileDo }
      { apply RTC.head
        { apply SmallStep.if_true
          assumption }
        { apply RTC.trans
          { exact RTC_SmallStep_seq ihS }
          { apply RTC.head
            apply SmallStep.seq_skip
            assumption } } }
    | while_false B S s hB =>
      apply RTC.tail
      apply RTC.single
      apply SmallStep.whileDo
      apply SmallStep.if_false
      assumption

theorem BigStep_of_SmallStep_of_BigStep {Ss₀ Ss₁ s₂}
      (h₁ : Ss₀ ⇒ Ss₁) :
    Ss₁ ⟹ s₂ → Ss₀ ⟹ s₂ :=
  by
    induction h₁ generalizing s₂ with
    | assign x a s               => simp
    | seq_step S S' T s s' hS ih => aesop
    | seq_skip T s               => simp
    | if_true B S T s hB         => aesop
    | if_false B S T s hB        => aesop
    | whileDo B S s              => aesop

theorem BigStep_of_RTC_SmallStep {Ss t} :
    Ss ⇒* (Stmt.skip, t) → Ss ⟹ t :=
  by
    intro hS
    induction hS using RTC.head_induction_on with
    | refl =>
      apply BigStep.skip
    | head Ss Ss' hST hsmallT ih =>
      cases Ss' with
      | mk S' s' =>
        apply BigStep_of_SmallStep_of_BigStep hST
        apply ih

theorem BigStep_Iff_RTC_SmallStep {Ss t} :
    Ss ⟹ t ↔ Ss ⇒* (Stmt.skip, t) :=
  Iff.intro RTC_SmallStep_of_BigStep BigStep_of_RTC_SmallStep

end LoVe

