/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示 12：数学的逻辑基础

我们将深入探索Lean的逻辑基础。这里描述的大多数特性
特别适用于定义数学对象并证明关于它们的定理。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 宇宙

不仅项有类型，类型本身也有类型。例如，

    `@And.intro : ∀a b, a → b → a ∧ b`

和

    `∀a b, a → b → a ∧ b : Prop`

那么，`Prop`的类型是什么？`Prop`的类型与我们目前构造的几乎所有其他类型相同：

    `Prop : Type`

`Type`的类型又是什么？类型判断 `Type : Type` 会导致矛盾，
称为**吉拉尔悖论**，类似于罗素悖论。实际上：

    `Type   : Type 1`
    `Type 1 : Type 2`
    `Type 2 : Type 3`
    ⋮

别名：

    `Type`   := `Type 0`
    `Prop`   := `Sort 0`
    `Type u` := `Sort (u + 1)`

类型的类型（`Sort u`、`Type u` 和 `Prop`）称为__宇宙__。
`Sort u`中的`u`称为__宇宙层级__。

层级关系由以下类型判断捕获：

    ————————————————————————— Sort
    C ⊢ Sort u : Sort (u + 1) -/

#check @And.intro
#check ∀a b : Prop, a → b → a ∧ b
#check Prop
#check ℕ
#check Type
#check Type 1
#check Type 2

universe u v

#check Type u

#check Sort 0
#check Sort 1
#check Sort 2
#check Sort u

#check Type _


/- ## Prop的特殊性

`Prop`在许多方面与其他宇宙不同。


### 非直谓性

函数类型 `σ → τ` 被放入`σ`和`τ`所在宇宙中较大的那个：

    C ⊢ σ : Type u    C ⊢ τ : Type v
    ————————————————————————————————— SimpleArrow-Type
    C ⊢ σ → τ : Type (max u v)

对于依赖类型，这推广为：

    C ⊢ σ : Type u    C, x : σ ⊢ τ[x] : Type v
    ——————————————————————————————————————————— Arrow-Type
    C ⊢ (x : σ) → τ[x] : Type (max u v)

`Type v`宇宙的这种行为称为__直谓性__。

为了强制像`∀a : Prop, a → a`这样的表达式类型为`Prop`，我们需要为`Prop`制定特殊类型规则：

    C ⊢ σ : Sort u    x : σ ⊢ τ[x] : Prop
    —————————————————————————————————————— Arrow-Prop
    C ⊢ (∀x : σ, τ[x]) : Prop

`Prop`的这种行为称为__非直谓性__。

规则`Arrow-Type`和`Arrow-Prop`可以推广为单一规则：

    C ⊢ σ : Sort u    C, x : σ ⊢ τ[x] : Sort v
    ——————————————————————————————————————————— Arrow
    C ⊢ (x : σ) → τ[x] : Sort (imax u v)

其中

    `imax u 0       = 0`
    `imax u (v + 1) = max u (v + 1)` -/

#check fun (α : Type u) (β : Type v) ↦ α → β
#check ∀a : Prop, a → a


/- ### 证明无关性

`Prop`与`Type u`的第二个区别是__证明无关性__：

    `∀(a : Prop) (h₁ h₂ : a), h₁ = h₂`

这使得推理依赖类型更加容易。

当将命题视为类型、证明视为该类型的元素时，
证明无关性意味着命题要么是空类型，要么恰好有一个居民。

证明无关性可以通过`rfl`证明。

证明无关性的一个不幸后果是它阻止我们通过模式匹配和递归进行规则归纳。 -/

#check proof_irrel

theorem proof_irrel {a : Prop} (h₁ h₂ : a) :
    h₁ = h₂ :=
  by rfl


/- ### 无大消除

`Prop`与`Type u`的另一个区别是`Prop`不允许__大消除__，
这意味着无法从命题的证明中提取数据。

这是允许证明无关性所必需的。 -/

/-
-- 失败
def unsquare (i : ℤ) (hsq : ∃j, i = j * j) : ℤ :=
  match hsq with
  | Exists.intro j _ => j
-/

/- 如果上述代码被接受，我们可以如下推导出`False`。

设

    `hsq₁` := `Exists.intro 3 (by linarith)`
    `hsq₂` := `Exists.intro (-3) (by linarith)`

为`∃j, (9 : ℤ) = j * j`的两个证明。那么

    `unsquare 9 hsq₁ = 3`
    `unsquare 9 hsq₂ = -3`

然而，根据证明无关性，`hsq₁ = hsq₂`。因此

    `unsquare 9 hsq₂ = 3`

于是

    `3 = -3`

矛盾。

作为折衷，Lean允许__小消除__。之所以称为小消除，
是因为它仅消除到`Prop`，而大消除可以消除到任意大的宇宙`Sort u`。
这意味着我们可以使用`match`分析证明结构、提取存在量词的见证等，
只要`match`表达式本身是一个证明。我们在第5讲中已经见过几个这样的例子。

作为进一步折衷，Lean允许对__语法单例__进行大消除：
那些在`Prop`中且可以语法上确定其基数为0或1的类型。
这些是诸如`False`和`a ∧ b`等命题，它们最多以一种方式证明。


## 选择公理

Lean的逻辑包含选择公理，这使得可以从任何非空类型中获取任意元素。

考虑Lean的`Nonempty`归纳谓词： -/

#print Nonempty

/- 该谓词表示`α`至少有一个元素。

要证明`Nonempty α`，我们必须向`Nonempty.intro`提供一个`α`值： -/

theorem Nat.Nonempty :
    Nonempty ℕ :=
  Nonempty.intro 0

/- 由于`Nonempty`位于`Prop`中，无法进行大消除，
因此无法从`Nonempty α`的证明中提取使用的元素。

选择公理允许我们在能证明`Nonempty α`时获取`α`类型的某个元素： -/

#check Classical.choice

/- 它只会给我们`α`的任意一个元素；我们无法知道这是否是用于证明`Nonempty α`的元素。

常量`Classical.choice`是不可计算的，这就是为什么一些逻辑学家更喜欢不使用这个公理。 -/

/-
#eval Classical.choice Nat.Nonempty     -- 失败
-/
#reduce Classical.choice Nat.Nonempty

/- 选择公理只是Lean核心库中的一个公理，让用户可以选择使用或不使用它。

使用它的定义必须标记为`noncomputable`： -/

noncomputable def arbitraryNat : ℕ :=
  Classical.choice Nat.Nonempty

/- 以下工具依赖于选择公理。


### 排中律 -/

#check Classical.em


/- ### 希尔伯特选择 -/

#check Classical.choose
#check Classical.choose_spec


/- ### 集合论的选择公理 -/

#print Classical.axiomOfChoice


/- ## 子类型

子类型化是从现有类型创建新类型的机制。

给定基类型元素上的谓词，__子类型__仅包含满足该属性的基类型元素。
更准确地说，子类型包含元素-证明对，组合了基类型的元素和证明其满足属性的证明。

子类型化适用于那些无法定义为归纳类型的类型。例如，任何尝试按以下方式定义有限集类型的尝试都会失败： -/

-- 错误
inductive Finset (α : Type) : Type
  | empty  : Finset α
  | insert : α → Finset α → Finset α

/- 为什么这不能建模有限集？

给定基类型和属性，子类型的语法为

    `{` _变量_ `:` _基类型_ `//` _应用于变量的属性_ `}`

别名：

    `{x : τ // P[x]}` := `@Subtype τ (fun x ↦ P[x])`

示例：

    `{i : ℕ // i ≤ n}`            := `@Subtype ℕ (fun i ↦ i ≤ n)`
    `{A : Set α // Set.Finite A}` := `@Subtype (Set α) Set.Finite`


### 第一个例子：满二叉树 -/

#check Tree
#check IsFull
#check mirror
#check IsFull_mirror
#check mirror_mirror

def FullTree (α : Type) : Type :=
  {t : Tree α // IsFull t}

#print Subtype
#check Subtype.mk

/- 要定义`FullTree`的元素，我们必须提供`Tree`和证明它是满的： -/

def nilFullTree : FullTree ℕ :=
  Subtype.mk Tree.nil IsFull.nil

def fullTree6 : FullTree ℕ :=
  Subtype.mk (Tree.node 6 Tree.nil Tree.nil)
    (by
       apply IsFull.node
       apply IsFull.nil
       apply IsFull.nil
       rfl)

#reduce Subtype.val fullTree6
#check Subtype.property fullTree6

/- 我们可以将`Tree`上的现有操作提升到`FullTree`： -/

def FullTree.mirror {α : Type} (t : FullTree α) :
  FullTree α :=
  Subtype.mk (LoVe.mirror (Subtype.val t))
    (by
       apply IsFull_mirror
       apply Subtype.property t)

#reduce Subtype.val (FullTree.mirror fullTree6)

/- 当然，我们可以证明关于提升操作的定理： -/

theorem FullTree.mirror_mirror {α : Type}
      (t : FullTree α) :
    (FullTree.mirror (FullTree.mirror t)) = t :=
  by
    apply Subtype.eq
    simp [FullTree.mirror, LoVe.mirror_mirror]

#check Subtype.eq


/- ### 第二个例子：向量 -/

def Vector (α : Type) (n : ℕ) : Type :=
  {xs : List α // List.length xs = n}

def vector123 : Vector ℤ 3 :=
  Subtype.mk [1, 2, 3] (by rfl)

def Vector.neg {n : ℕ} (v : Vector ℤ n) : Vector ℤ n :=
  Subtype.mk (List.map Int.neg (Subtype.val v))
    (by
       rw [List.length_map]
       exact Subtype.property v)

theorem Vector.neg_neg (n : ℕ) (v : Vector ℤ n) :
    Vector.neg (Vector.neg v) = v :=
  by
    apply Subtype.eq
    simp [Vector.neg]


/- ## 商类型

商是数学中用于构造`ℤ`、`ℚ`、`ℝ`等类型的强大构造。

与子类型化类似，商化从现有类型构造新类型。不同于子类型，
商类型包含基类型的所有元素，但基类型中不同的元素在商类型中可能被视为相同。
用数学术语来说，商类型同构于基类型的划分。

要定义商类型，我们需要提供它派生的类型和确定哪些元素被视为相等的等价关系。 -/

#check Quotient
#print Setoid

#check Quotient.mk
#check Quotient.sound
#check Quotient.exact

#check Quotient.lift
#check Quotient.lift₂
#check @Quotient.inductionOn


/- ## 第一个例子：整数

让我们将整数`ℤ`构造为自然数对`ℕ × ℕ`的商类型。

自然数对`(p, n)`表示整数`p - n`。非负整数`p`可以表示为`(p, 0)`。
负整数`-n`可以表示为`(0, n)`。然而，同一个整数有多种表示方式；
例如，`(7, 0)`、`(8, 1)`、`(9, 2)`和`(10, 3)`都表示整数`7`。

我们可以使用什么等价关系？

我们希望两个对`(p₁, n₁)`和`(p₂, n₂)`相等当`p₁ - n₁ = p₂ - n₂`。
然而，这不可行，因为`ℕ`上的减法行为不良（例如，`0 - 1 = 0`）。
相反，我们使用`p₁ + n₂ = p₂ + n₁`。 -/

instance Int.Setoid : Setoid (ℕ × ℕ) :=
  { r :=
      fun pn₁ pn₂ : ℕ × ℕ ↦
        Prod.fst pn₁ + Prod.snd pn₂ =
        Prod.fst pn₂ + Prod.snd pn₁
    iseqv :=
      { refl :=
          by
            intro pn
            rfl
        symm :=
          by
            intro pn₁ pn₂ h
            rw [h]
        trans :=
          by
            intro pn₁ pn₂ pn₃ h₁₂ h₂₃
            linarith } }

theorem Int.Setoid_Iff (pn₁ pn₂ : ℕ × ℕ) :
    pn₁ ≈ pn₂ ↔
    Prod.fst pn₁ + Prod.snd pn₂ =
    Prod.fst pn₂ + Prod.snd pn₁ :=
  by rfl

def Int : Type :=
  Quotient Int.Setoid

def Int.zero : Int :=
  ⟦(0, 0)⟧

theorem Int.zero_Eq (m : ℕ) :
    Int.zero = ⟦(m, m)⟧ :=
  by
    rw [Int.zero]
    apply Quotient.sound
    rw [Int.Setoid_Iff]
    simp

def Int.add : Int → Int → Int :=
  Quotient.lift₂
    (fun pn₁ pn₂ : ℕ × ℕ ↦
       ⟦(Prod.fst pn₁ + Prod.fst pn₂,
         Prod.snd pn₁ + Prod.snd pn₂)⟧)
    (by
       intro pn₁ pn₂ pn₁' pn₂' h₁ h₂
       apply Quotient.sound
       rw [Int.Setoid_Iff] at *
       linarith)

theorem Int.add_Eq (p₁ n₁ p₂ n₂ : ℕ) :
    Int.add ⟦(p₁, n₁)⟧ ⟦(p₂, n₂)⟧ =
    ⟦(p₁ + p₂, n₁ + n₂)⟧ :=
  by rfl

theorem Int.add_zero (i : Int) :
    Int.add Int.zero i = i :=
  by
    induction i using Quotient.inductionOn with
    | h pn =>
      cases pn with
      | mk p n => simp [Int.zero, Int.add]

/- 这种定义语法会很方便： -/

/-
-- 失败
def Int.add : Int → Int → Int
  | ⟦(p₁, n₁)⟧, ⟦(p₂, n₂)⟧ => ⟦(p₁ + p₂, n₁ + n₂)⟧
-/

/- 但这会很危险： -/

/-
-- 失败
def Int.fst : Int → ℕ
  | ⟦(p, n)⟧ => p
-/

/- 使用`Int.fst`，我们可以推导出`False`。首先，我们有

    `Int.fst ⟦(0, 0)⟧ = 0`
    `Int.fst ⟦(1, 1)⟧ = 1`

但由于`⟦(0, 0)⟧ = ⟦(1, 1)⟧`，我们得到

    `0 = 1` -/


/- ### 第二个例子：无序对

__无序对__是不区分第一个和第二个分量的对。通常写作`{a, b}`。

我们将引入无序对类型`UPair`作为对`(a, b)`关于"包含相同元素"关系的商。 -/

instance UPair.Setoid (α : Type) : Setoid (α × α) :=
{ r :=
    fun ab₁ ab₂ : α × α ↦
      ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
      ({Prod.fst ab₂, Prod.snd ab₂} : Set α)
  iseqv :=
    { refl  := by simp
      symm  := by aesop
      trans := by aesop } }

theorem UPair.Setoid_Iff {α : Type} (ab₁ ab₂ : α × α) :
    ab₁ ≈ ab₂ ↔
    ({Prod.fst ab₁, Prod.snd ab₁} : Set α) =
    ({Prod.fst ab₂, Prod.snd ab₂} : Set α) :=
  by rfl

def UPair (α : Type) : Type :=
  Quotient (UPair.Setoid α)

#check UPair.Setoid

/- 很容易证明我们的对确实是无序的： -/

theorem UPair.mk_symm {α : Type} (a b : α) :
    (⟦(a, b)⟧ : UPair α) = ⟦(b, a)⟧ :=
  by
    apply Quotient.sound
    rw [UPair.Setoid_Iff]
    aesop

/- 无序对的另一种表示是基数为1或2的集合。
以下操作将`UPair`转换为该表示： -/

def Set_of_UPair {α : Type} : UPair α → Set α :=
  Quotient.lift (fun ab : α × α ↦ {Prod.fst ab, Prod.snd ab})
    (by
       intro ab₁ ab₂ h
       rw [UPair.Setoid_Iff] at *
       exact h)


/- ### 通过规范化和子类型化的替代定义

商类型的每个元素对应一个`≈`等价类。
如果存在系统方法为每个类获取**规范代表**，我们可以使用子类型代替商类型，仅保留规范代表。

考虑上面的商类型`Int`。我们可以说一个对`(p, n)`是__规范的__，如果`p`或`n`为`0`。 -/

namespace Alternative

inductive Int.IsCanonical : ℕ × ℕ → Prop
  | nonpos {n : ℕ} : Int.IsCanonical (0, n)
  | nonneg {p : ℕ} : Int.IsCanonical (p, 0)

def Int : Type :=
  {pn : ℕ × ℕ // Int.IsCanonical pn}

/- **规范化**自然数对很容易： -/

def Int.normalize : ℕ × ℕ → ℕ × ℕ
  | (p, n) => if p ≥ n then (p - n, 0) else (0, n - p)

theorem Int.IsCanonical_normalize (pn : ℕ × ℕ) :
    Int.IsCanonical (Int.normalize pn) :=
  by
    cases pn with
    | mk p n =>
      simp [Int.normalize]
      cases Classical.em (p ≥ n) with
      | inl hpn =>
        simp [*]
        exact Int.IsCanonical.nonneg
      | inr hpn =>
        simp [*]
        exact Int.IsCanonical.nonpos

/- 对于无序对，没有明显的规范形式，除非总是将较小的元素放在前面（或后面）。
这需要`α`上的线性序`≤`。 -/

def UPair.IsCanonical {α : Type} [LinearOrder α] :
  α × α → Prop
  | (a, b) => a ≤ b

def UPair (α : Type) [LinearOrder α] : Type :=
  {ab : α × α // UPair.IsCanonical ab}

end Alternative

end LoVe
