/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe09_OperationalSemantics_Demo


/- # LoVe 演示 11：指称语义

我们回顾第三种编程语言语义规范方法：指称语义。指称语义试图直接定义程序的含义。

如果操作语义是理想化的解释器，霍尔逻辑是理想化的验证器，那么指称语义就是理想化的编译器。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 组合性

__指称语义__将每个程序的含义定义为数学对象：

    `⟦ ⟧ : 语法 → 语义`

指称语义的关键特性是__组合性__：复合语句的含义应基于其组成部分的含义来定义。这使得以下定义不合格：

    `⟦S⟧ = {st | (S, Prod.fst st) ⟹ Prod.snd st}`

（即

    `⟦S⟧ = {(s, t) | (S, s) ⟹ t}`）

因为操作语义不具备组合性。

简而言之，我们需要：

    `⟦S; T⟧               = … ⟦S⟧ … ⟦T⟧ …`
    `⟦if B then S else T⟧ = … ⟦S⟧ … ⟦T⟧ …`
    `⟦while B do S⟧       = … ⟦S⟧ …`

算术表达式的求值函数

    `eval : AExp → ((String → ℤ) → ℤ)`

就是一种指称语义。我们希望为命令式程序实现类似的定义。


## 关系型指称语义

我们可以将命令式程序的语义表示为从初始状态到最终状态的函数，或更一般地表示为初始状态与最终状态之间的关系：`Set (State × State)`。

对于 `skip`、`:=`、`;` 和 `if then else`，指称语义的定义较为简单： -/

namespace SorryDefs

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      => sorry

end SorryDefs

/- 我们用 `⟦S⟧` 表示 `denote S`。对于 `while`，我们希望写成：

    `((denote S ◯ denote (Stmt.whileDo B S)) ⇃ B)`
    `∪ (Id ⇃ (fun s ↦ ¬ B s))`

但由于对 `Stmt.whileDo B S` 的递归调用，这会导致无限递归。

我们需要找到一个满足以下条件的 `X`：

    `X = ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s))`

换句话说，我们需要寻找一个不动点。

本讲座的主要内容是构建一个最小不动点算子 `lfp`，使我们能够定义 `while` 的情况：

    `lfp (fun X ↦ ((denote S ◯ X) ⇃ B) ∪ (Id ⇃ (fun s ↦ ¬ B s)))`


## 不动点

函数 `f` 的__不动点__（或固定点）是方程 `X = f X` 的解。

一般情况下，不动点可能不存在（例如 `f := Nat.succ`），或者可能存在多个不动点（例如 `f := id`）。但在某些条件下，可以保证存在唯一的__最小不动点__和唯一的__最大不动点__。

考虑以下__不动点方程__：

    `X = (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m) X`
      `= (fun n : ℕ ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ X m)`

其中 `X : ℕ → Prop` 且
`f := (fun (P : ℕ → Prop) (n : ℕ) ↦ n = 0 ∨ ∃m : ℕ, n = m + 2 ∧ P m)`。

上述示例只有一个不动点。该不动点方程唯一地指定 `X` 为描述偶数的谓词。

一般情况下，最小和最大不动点可能不同：

    `X = X`

这里，最小不动点是 `fun _ ↦ False`，最大不动点是 `fun _ ↦ True`。按照惯例，`False < True`，因此 `(fun _ ↦ False) < (fun _ ↦ True)`。类似地，`∅ < @Set.univ ℕ`。

对于编程语言的语义：

* `X` 的类型为 `Set (State × State)`（同构于 `State → State → Prop`），表示状态之间的关系；

* `f` 对应于要么执行循环的额外一次迭代（如果条件 `B` 为真），要么保持原样（如果 `B` 为假）。

最小不动点对应于程序的有限执行，这正是我们关心的内容。

**关键观察**：

    归纳谓词对应于最小不动点，但它们已内置于 Lean 的逻辑（归纳构造演算）中。


## 单调函数

设 `α` 和 `β` 为带有偏序 `≤` 的类型。函数 `f : α → β` 是__单调的__，如果满足：

    `a₁ ≤ a₂ → f a₁ ≤ f a₂`   对所有 `a₁`, `a₂` 成立

集合（如 `∪`）、关系（如 `◯`）和函数（如 `fun x ↦ x`、`fun _ ↦ k`、`∘`）的许多操作都是单调的或保持单调性。

所有单调函数 `f : Set α → Set α` 都存在最小和最大不动点。

**非单调函数示例**：

    `f A = (if A = ∅ then Set.univ else ∅)`

假设 `α` 非空，我们有 `∅ ⊆ Set.univ`，但 `f ∅ = Set.univ ⊈ ∅ = f Set.univ`。 -/

def Monotone {α β : Type} [PartialOrder α] [PartialOrder β]
  (f : α → β) : Prop :=
  ∀a₁ a₂, a₁ ≤ a₂ → f a₁ ≤ f a₂

theorem Monotone_id {α : Type} [PartialOrder α] :
    Monotone (fun a : α ↦ a) :=
  by
    intro a₁ a₂ ha
    exact ha

theorem Monotone_const {α β : Type} [PartialOrder α]
    [PartialOrder β] (b : β) :
    Monotone (fun _ : α ↦ b) :=
  by
    intro a₁ a₂ ha
    exact le_refl b

theorem Monotone_union {α β : Type} [PartialOrder α]
      (f g : α → Set β) (hf : Monotone f) (hg : Monotone g) :
    Monotone (fun a ↦ f a ∪ g a) :=
  by
    intro a₁ a₂ ha b hb
    cases hb with
    | inl h => exact Or.inl (hf a₁ a₂ ha h)
    | inr h => exact Or.inr (hg a₁ a₂ ha h)

/- 我们将在练习中证明以下两个定理。 -/

namespace SorryTheorems

theorem Monotone_comp {α β : Type} [PartialOrder α]
      (f g : α → Set (β × β)) (hf : Monotone f)
      (hg : Monotone g) :
    Monotone (fun a ↦ f a ◯ g a) :=
  sorry

theorem Monotone_restrict {α β : Type} [PartialOrder α]
      (f : α → Set (β × β)) (P : β → Prop) (hf : Monotone f) :
    Monotone (fun a ↦ f a ⇃ P) :=
  sorry

end SorryTheorems


/- ## 完全格

为了在集合上定义最小不动点，我们需要 `⊆` 和 `⋂`：⋂ {A | f A ⊆ A}。完全格抽象地捕捉了这一概念。__完全格__是一个有序类型 `α`，其中每个 `Set α` 类型的集合都有一个下确界。

更准确地说，完全格包含：

* 一个偏序 `≤ : α → α → Prop`（即自反、反对称、传递的二元谓词）；

* 一个称为__下确界__的算子 `Inf : Set α → α`。

此外，`Inf A` 必须满足以下两个性质：

* `Inf A` 是 `A` 的下界：对所有 `b ∈ A`，`Inf A ≤ b`；

* `Inf A` 是最大下界：对所有满足 `∀a, a ∈ A → b ≤ a` 的 `b`，有 `b ≤ Inf A`。

**注意**：`Inf A` 不一定是 `A` 的元素。

示例：

* 对于所有 `α`，`Set α` 是关于 `⊆` 和 `⋂` 的实例；
* `Prop` 是关于 `→` 和 `∀` 的实例（`Inf A := ∀a ∈ A, a`）；
* `ENat := ℕ ∪ {∞}`；
* `EReal := ℝ ∪ {- ∞, ∞}`；
* 如果 `α` 是完全格，则 `β → α` 也是；
* 如果 `α` 和 `β` 是完全格，则 `α × β` 也是。

有限示例（抱歉使用 ASCII 艺术）：

                Z            Inf {}           = ?
              /   \          Inf {Z}          = ?
             A     B         Inf {A, B}       = ?
              \   /          Inf {Z, A}       = ?
                Y            Inf {Z, A, B, Y} = ?

非示例：

* `ℕ`、`ℤ`、`ℚ`、`ℝ`：`∅` 没有下确界。
* `ERat := ℚ ∪ {- ∞, ∞}`：`Inf {q | 2 < q * q} = sqrt 2` 不在 `ERat` 中。 -/

class CompleteLattice (α : Type)
  extends PartialOrder α : Type where
  Inf    : Set α → α
  Inf_le : ∀A b, b ∈ A → Inf A ≤ b
  le_Inf : ∀A b, (∀a, a ∈ A → b ≤ a) → b ≤ Inf A

/- 对于集合： -/

instance Set.CompleteLattice {α : Type} :
  CompleteLattice (Set α) :=
  { @Set.PartialOrder α with
    Inf         := fun X ↦ {a | ∀A, A ∈ X → a ∈ A}
    Inf_le      := by aesop
    le_Inf      := by aesop }


/- ## 最小不动点 -/

def lfp {α : Type} [CompleteLattice α] (f : α → α) : α :=
  CompleteLattice.Inf {a | f a ≤ a}

theorem lfp_le {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : f a ≤ a) :
    lfp f ≤ a :=
  CompleteLattice.Inf_le _ _ h

theorem le_lfp {α : Type} [CompleteLattice α] (f : α → α)
      (a : α) (h : ∀a', f a' ≤ a' → a ≤ a') :
    a ≤ lfp f :=
  CompleteLattice.le_Inf _ _ h

/- **Knaster-Tarski 定理**：对于任何单调函数 `f`：

* `lfp f` 是一个不动点：`lfp f = f (lfp f)`（定理 `lfp_eq`）；
* `lfp f` 小于任何其他不动点：`X = f X → lfp f ≤ X`。 -/

theorem lfp_eq {α : Type} [CompleteLattice α] (f : α → α)
      (hf : Monotone f) :
    lfp f = f (lfp f) :=
  by
    have h : f (lfp f) ≤ lfp f :=
      by
        apply le_lfp
        intro a' ha'
        apply le_trans
        { apply hf
          apply lfp_le
          assumption }
        { assumption }
    apply le_antisymm
    { apply lfp_le
      apply hf
      assumption }
    { assumption }


/- ## 关系型指称语义（续） -/

def denote : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denote S ◯ denote T
  | Stmt.ifThenElse B S T =>
    (denote S ⇃ B) ∪ (denote T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    lfp (fun X ↦ ((denote S ◯ X) ⇃ B)
      ∪ (Id ⇃ (fun s ↦ ¬ B s)))

notation (priority := high) "⟦" S "⟧" => denote S

theorem Monotone_while_lfp_arg (S B) :
    Monotone (fun X ↦ ⟦S⟧ ◯ X ⇃ B ∪ Id ⇃ (fun s ↦ ¬ B s)) :=
  by
    apply Monotone_union
    { apply SorryTheorems.Monotone_restrict
      apply SorryTheorems.Monotone_comp
      { exact Monotone_const _ }
      { exact Monotone_id } }
    { apply SorryTheorems.Monotone_restrict
      exact Monotone_const _ }


/- ## 应用于程序等价性

基于指称语义，我们引入程序等价性的概念：`S₁ ~ S₂`。（与练习 9 比较。） -/

def DenoteEquiv (S₁ S₂ : Stmt) : Prop :=
  ⟦S₁⟧ = ⟦S₂⟧

infix:50 (priority := high) " ~ " => DenoteEquiv

/- 从定义中明显看出 `~` 是一个等价关系。

程序等价性可用于将子程序替换为具有相同语义的其他子程序。这通过以下同余规则实现： -/

theorem DenoteEquiv.seq_congr {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    S₁; T₁ ~ S₂; T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.if_congr {B} {S₁ S₂ T₁ T₂ : Stmt}
      (hS : S₁ ~ S₂) (hT : T₁ ~ T₂) :
    Stmt.ifThenElse B S₁ T₁ ~ Stmt.ifThenElse B S₂ T₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

theorem DenoteEquiv.while_congr {B} {S₁ S₂ : Stmt}
      (hS : S₁ ~ S₂) :
    Stmt.whileDo B S₁ ~ Stmt.whileDo B S₂ :=
  by
    simp [DenoteEquiv, denote] at *
    simp [*]

/- 比较这些证明与基于大步语义的相应证明（练习 8）的简洁性。

让我们证明一些程序等价性。 -/

theorem DenoteEquiv.skip_assign_id {x} :
    Stmt.assign x (fun s ↦ s x) ~ Stmt.skip :=
  by simp [DenoteEquiv, denote, Id]

theorem DenoteEquiv.seq_skip_left {S} :
    Stmt.skip; S ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.seq_skip_right {S} :
    S; Stmt.skip ~ S :=
  by simp [DenoteEquiv, denote, Id, comp]

theorem DenoteEquiv.if_seq_while {B S} :
    Stmt.ifThenElse B (S; Stmt.whileDo B S) Stmt.skip
    ~ Stmt.whileDo B S :=
  by
    simp [DenoteEquiv, denote]
    apply Eq.symm
    apply lfp_eq
    apply Monotone_while_lfp_arg


/- ## 指称语义与大步语义的等价性
## （可选） -/

theorem denote_of_BigStep (Ss : Stmt × State) (t : State)
      (h : Ss ⟹ t) :
    (Prod.snd Ss, t) ∈ ⟦Prod.fst Ss⟧ :=
  by
    induction h with
    | skip s => simp [denote]
    | assign x a s => simp [denote]
    | seq S T s t u hS hT ihS ihT =>
      simp [denote]
      aesop
    | if_true B S T s t hB hS ih =>
      simp at *
      simp [denote, *]
    | if_false B S T s t hB hT ih =>
      simp at *
      simp [denote, *]
    | while_true B S s t u hB hS hw ihS ihw =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]
      aesop
    | while_false B S s hB =>
      rw [Eq.symm DenoteEquiv.if_seq_while]
      simp at *
      simp [denote, *]

theorem BigStep_of_denote :
    ∀(S : Stmt) (s t : State), (s, t) ∈ ⟦S⟧ → (S, s) ⟹ t
  | Stmt.skip,             s, t => by simp [denote]
  | Stmt.assign x a,       s, t => by simp [denote]
  | Stmt.seq S T,          s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | intro u hu =>
        cases hu with
        | intro hsu hut =>
          apply BigStep.seq
          { exact BigStep_of_denote _ _ _ hsu }
          { exact BigStep_of_denote _ _ _ hut }
  | Stmt.ifThenElse B S T, s, t =>
    by
      intro hst
      simp [denote] at hst
      cases hst with
      | inl htrue =>
        cases htrue with
        | intro hst hB =>
          apply BigStep.if_true
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
      | inr hfalse =>
        cases hfalse with
        | intro hst hB =>
          apply BigStep.if_false
          { exact hB }
          { exact BigStep_of_denote _ _ _ hst }
  | Stmt.whileDo B S,      s, t =>
    by
      have hw : ⟦Stmt.whileDo B S⟧
        ≤ {st | (Stmt.whileDo B S, Prod.fst st) ⟹
             Prod.snd st} :=
        by
          apply lfp_le _ _ _
          intro uv huv
          cases uv with
          | mk u v =>
            simp at huv
            cases huv with
            | inl hand =>
              cases hand with
              | intro hst hB =>
                cases hst with
                | intro w hw =>
                  cases hw with
                  | intro huw hw =>
                    apply BigStep.while_true
                    { exact hB }
                    { exact BigStep_of_denote _ _ _ huw }
                    { exact hw }
            | inr hand =>
              cases hand with
              | intro hvu hB =>
                cases hvu
                apply BigStep.while_false
                exact hB
      apply hw

theorem denote_Iff_BigStep (S : Stmt) (s t : State) :
    (s, t) ∈ ⟦S⟧ ↔ (S, s) ⟹ t :=
  Iff.intro (BigStep_of_denote S s t) (denote_of_BigStep (S, s) t)


/- ## 基于归纳谓词的更简单方法（可选） -/

inductive Awhile (B : State → Prop)
    (r : Set (State × State)) :
  State → State → Prop
  | true {s t u} (hcond : B s) (hbody : (s, t) ∈ r)
      (hrest : Awhile B r t u) :
    Awhile B r s u
  | false {s} (hcond : ¬ B s) :
    Awhile B r s s

def denoteAwhile : Stmt → Set (State × State)
  | Stmt.skip             => Id
  | Stmt.assign x a       =>
    {st | Prod.snd st = (Prod.fst st)[x ↦ a (Prod.fst st)]}
  | Stmt.seq S T          => denoteAwhile S ◯ denoteAwhile T
  | Stmt.ifThenElse B S T =>
    (denoteAwhile S ⇃ B)
    ∪ (denoteAwhile T ⇃ (fun s ↦ ¬ B s))
  | Stmt.whileDo B S      =>
    {st | Awhile B (denoteAwhile S) (Prod.fst st)
       (Prod.snd st)}

end LoVe

