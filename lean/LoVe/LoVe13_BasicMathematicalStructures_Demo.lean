/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe 演示13：基础数学结构

我们介绍关于基础数学结构的定义和证明，例如群、域和线性序。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 单一二元运算符的类型类

数学上，一个__群__是一个集合`G`配备一个二元运算符`⬝ : G × G → G`，满足以下性质（称为__群公理__）：

* 结合律：对所有`a, b, c ∈ G`，有`(a ⬝ b) ⬝ c = a ⬝ (b ⬝ c)`；
* 单位元：存在一个元素`e ∈ G`使得对所有`a ∈ G`，有`e ⬝ a = a`和`a ⬝ e = a`；
* 逆元：对每个`a ∈ G`，存在一个逆元`b ∈ G`使得`b ⬝ a = e`和`a ⬝ b = e`。

群的例子包括：
* `ℤ`配备`+`；
* `ℝ`配备`+`；
* `ℝ \ {0}`配备`*`。

在Lean中，群的类型类可以如下定义： -/

namespace MonolithicGroup

class Group (α : Type) where
  mul          : α → α → α
  one          : α
  inv          : α → α
  mul_assoc    : ∀a b c, mul (mul a b) c = mul a (mul b c)
  one_mul      : ∀a, mul one a = a
  mul_left_inv : ∀a, mul (inv a) a = one

end MonolithicGroup

/- 然而在Lean中，群是更大的代数结构层次的一部分：

类型类             | 性质                                   | 例子
------------------ | -------------------------------------- | -------------------
`Semigroup`        | `*`的结合律                           | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Monoid`           | 带有单位元`1`的`Semigroup`            | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`LeftCancelSemigroup` | 满足`c * a = c * b → a = b`的`Semigroup` |
`RightCancelSemigroup`| 满足`a * c = b * c → a = b`的`Semigroup` |
`Group`            | 带有逆元`⁻¹`的`Monoid`                |

这些结构大多有交换版本：`CommSemigroup`、`CommMonoid`、`CommGroup`。

__乘法__结构（基于`*`、`1`、`⁻¹`）被复制以产生__加法__版本（基于`+`、`0`、`-`）：

类型类                | 性质                                    | 例子
--------------------- | --------------------------------------- | -------------------
`AddSemigroup`        | `+`的结合律                            | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddMonoid`           | 带有单位元`0`的`AddSemigroup`          | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddLeftCancelSemigroup` | 满足`c + a = c + b → a = b`的`AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddRightCancelSemigroup`| 满足`a + c = b + c → a = b`的`AddSemigroup` | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`AddGroup`            | 带有逆元`-`的`AddMonoid`                | `ℝ`, `ℚ`, `ℤ` -/

#print Group
#print AddGroup

/- 让我们定义自己的类型——模2整数，并将其注册为加法群。 -/

inductive Int2 : Type
  | zero
  | one

def Int2.add : Int2 → Int2 → Int2
  | Int2.zero, a         => a
  | Int2.one,  Int2.zero => Int2.one
  | Int2.one,  Int2.one  => Int2.zero

instance Int2.AddGroup : AddGroup Int2 :=
  { add            := Int2.add
    zero           := Int2.zero
    neg            := fun a ↦ a
    add_assoc      :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    zero_add       :=
      by
        intro a
        cases a <;>
          rfl
    add_zero       :=
      by
        intro a
        cases a <;>
          rfl
    neg_add_cancel :=
      by
        intro a
        cases a <;>
          rfl
    nsmul         :=
      @nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
    zsmul         :=
      @zsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)
        (Neg.mk (fun a ↦ a))
        (@nsmulRec Int2 (Zero.mk Int2.zero) (Add.mk Int2.add)) }

/- `nsmul`和`znmul`是冗余的，出于技术原因需要它们。 -/

#reduce Int2.one + 0 - 0 - Int2.one

/- 另一个例子：列表是一个`AddMonoid`： -/

instance List.AddMonoid {α : Type} : AddMonoid (List α) :=
  { zero      := []
    add       := fun xs ys ↦ xs ++ ys
    add_assoc := List.append_assoc
    zero_add  := List.nil_append
    add_zero  := List.append_nil
    nsmul     :=
      @nsmulRec (List α) (Zero.mk [])
        (Add.mk (fun xs ys ↦ xs ++ ys))}


/- ## 具有两个二元运算符的类型类

数学上，一个__域__是一个集合`F`满足：

* `F`在运算符`+`（称为加法）下形成一个交换群，单位元为`0`。
* `F \ {0}`在运算符`*`（称为乘法）下形成一个交换群。
* 乘法对加法满足分配律——即对所有`a, b, c ∈ F`，有`a * (b + c) = a * b + a * c`。

在Lean中，域也是更大层次结构的一部分：

类型类      | 性质                                         | 例子
----------- | -------------------------------------------- | -------------------
`Semiring`  | 具有分配律的`Monoid`和`AddCommMonoid`        | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`CommSemiring` | 具有`*`交换律的`Semiring`                  | `ℝ`, `ℚ`, `ℤ`, `ℕ`
`Ring`      | 具有分配律的`Monoid`和`AddCommGroup`         | `ℝ`, `ℚ`, `ℤ`
`CommRing`  | 具有`*`交换律的`Ring`                      | `ℝ`, `ℚ`, `ℤ`
`DivisionRing` | 具有乘法逆元`⁻¹`的`Ring`                  | `ℝ`, `ℚ`
`Field`     | 具有`*`交换律的`DivisionRing`              | `ℝ`, `ℚ` -/

#print Field

/- 我们继续我们的例子： -/

def Int2.mul : Int2 → Int2 → Int2
  | Int2.one,  a => a
  | Int2.zero, _ => Int2.zero

theorem Int2.mul_assoc (a b c : Int2) :
     Int2.mul (Int2.mul a b) c = Int2.mul a (Int2.mul b c) :=
  by
    cases a <;>
      cases b <;>
      cases c <;>
      rfl

instance Int2.Field : Field Int2 :=
  { Int2.AddGroup with
    one            := Int2.one
    mul            := Int2.mul
    inv            := fun a ↦ a
    add_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    exists_pair_ne :=
      by
        apply Exists.intro Int2.zero
        apply Exists.intro Int2.one
        simp
    zero_mul       :=
      by
        intro a
        rfl
    mul_zero       :=
      by
        intro a
        cases a <;>
          rfl
    one_mul        :=
      by
        intro a
        rfl
    mul_one        :=
      by
        intro a
        cases a <;>
          rfl
    mul_inv_cancel :=
      by
        intro a h
        cases a
        { apply False.elim
          apply h
          rfl }
        { rfl }
    inv_zero       := by rfl
    mul_assoc      := Int2.mul_assoc
    mul_comm       :=
      by
        intro a b
        cases a <;>
          cases b <;>
          rfl
    left_distrib   :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          rfl
    right_distrib  :=
      by
        intro a b c
        cases a <;>
          cases b <;>
          cases c <;>
          rfl
    nnqsmul        := _
    nnqsmul_def    :=
      by
        intro a b
        rfl
    qsmul          := _
    qsmul_def :=
      by
        intro a b
        rfl
    nnratCast_def  :=
      by
        intro q
        rfl }

#reduce (1 : Int2) * 0 / (0 - 1)

#reduce (3 : Int2)

theorem ring_example (a b : Int2) :
    (a + b) ^ 3 = a ^ 3 + 3 * a ^ 2 * b + 3 * a * b ^ 2 + b ^ 3
    :=
  by ring

/- `ring`通过规范化表达式来证明交换环和半环上的等式。


## 强制转换

当组合来自`ℕ`、`ℤ`、`ℚ`和`ℝ`的数字时，我们可能需要将一种类型转换为另一种。Lean有一种机制可以自动引入强制转换，由`Coe.coe`（语法糖：`↑`）表示。`Coe.coe`可以设置为在任意类型之间提供隐式强制转换。

许多强制转换已经就位，包括以下：

* `Coe.coe : ℕ → α`将`ℕ`转换为另一个半环`α`；
* `Coe.coe : ℤ → α`将`ℤ`转换为另一个环`α`；
* `Coe.coe : ℚ → α`将`ℚ`转换为另一个除环`α`。

例如，以下代码可以工作，尽管自然数上没有定义取反`- n`： -/

theorem neg_mul_neg_Nat (n : ℕ) (z : ℤ) :
    (- z) * (- n) = z * n :=
  by simp

/- 注意Lean如何引入了`↑`强制转换： -/

#check neg_mul_neg_Nat

/- 类型注解可以记录我们的意图： -/

theorem neg_Nat_mul_neg (n : ℕ) (z : ℤ) :
    (- n : ℤ) * (- z) = n * z :=
  by simp

#print neg_Nat_mul_neg

/- 在涉及强制转换的证明中，策略`norm_cast`可能很方便。 -/

theorem Eq_coe_int_imp_Eq_Nat (m n : ℕ)
      (h : (m : ℤ) = (n : ℤ)) :
    m = n :=
  by norm_cast at h

theorem Nat_coe_Int_add_eq_add_Nat_coe_Int (m n : ℕ) :
    (m : ℤ) + (n : ℤ) = ((m + n : ℕ) : ℤ) :=
  by norm_cast

/- `norm_cast`将强制转换向表达式内部移动，作为一种简化形式。像`simp`一样，它通常会产生一个子目标。

`norm_cast`依赖于以下定理： -/

#check Nat.cast_add
#check Int.cast_add
#check Rat.cast_add


/- ### 列表、多重集和有限集

对于元素的有限集合，有不同的结构可用：

* 列表：顺序和重复重要；
* 多重集：仅重复重要；
* 有限集：顺序和重复都不重要。 -/

theorem List_duplicates_example :
    [2, 3, 3, 4] ≠ [2, 3, 4] :=
  by decide

theorem List_order_example :
    [4, 3, 2] ≠ [2, 3, 4] :=
  by decide

theorem Multiset_duplicates_example :
    ({2, 3, 3, 4} : Multiset ℕ) ≠ {2, 3, 4} :=
  by decide

theorem Multiset_order_example :
    ({2, 3, 4} : Multiset ℕ) = {4, 3, 2} :=
  by decide

theorem Finset_duplicates_example :
    ({2, 3, 3, 4} : Finset ℕ) = {2, 3, 4} :=
  by decide

theorem Finset_order_example :
    ({2, 3, 4} : Finset ℕ) = {4, 3, 2} :=
  by decide

/- `decide`是一个可用于真可判定目标（例如，一个真可执行表达式）的策略。 -/

def List.elems : Tree ℕ → List ℕ
  | Tree.nil        => []
  | Tree.node a l r => a :: List.elems l ++ List.elems r

def Multiset.elems : Tree ℕ → Multiset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r =>
    {a} ∪ Multiset.elems l ∪ Multiset.elems r

def Finset.elems : Tree ℕ → Finset ℕ
  | Tree.nil        => ∅
  | Tree.node a l r => {a} ∪ Finset.elems l ∪ Finset.elems r

#eval List.sum [2, 3, 4]
#eval Multiset.sum ({2, 3, 4} : Multiset ℕ)

#eval List.prod [2, 3, 4]
#eval Multiset.prod ({2, 3, 4} : Multiset ℕ)


/- ## 序类型类

上面介绍的许多结构都可以排序。例如，自然数上众所周知的序可以如下定义： -/

inductive Nat.le : ℕ → ℕ → Prop
  | refl : ∀a : ℕ, Nat.le a a
  | step : ∀a b : ℕ, Nat.le a b → Nat.le a (b + 1)

#print Preorder

/- 这是一个线性序的例子。一个__线性序__（或__全序__）是一个二元关系`≤`，满足对所有`a`、`b`、`c`，以下性质成立：

* 自反性：`a ≤ a`；
* 传递性：如果`a ≤ b`且`b ≤ c`，则`a ≤ c`；
* 反对称性：如果`a ≤ b`且`b ≤ a`，则`a = b`；
* 完全性：`a ≤ b`或`b ≤ a`。

如果一个关系具有前三个性质，它是一个__偏序__。一个例子是集合、有限集或多重集上的`⊆`。如果一个关系具有前两个性质，它是一个__预序__。一个例子是比较列表的长度。

在Lean中，有这些不同类型序的类型类：`LinearOrder`、`PartialOrder`和`Preorder`。 -/

#print Preorder
#print PartialOrder
#print LinearOrder

/- 我们可以如下声明按长度比较列表的预序： -/

instance List.length.Preorder {α : Type} : Preorder (List α) :=
  { le :=
      fun xs ys ↦ List.length xs ≤ List.length ys
    lt :=
      fun xs ys ↦ List.length xs < List.length ys
    le_refl :=
      by
        intro xs
        apply Nat.le_refl
    le_trans :=
      by
        intro xs ys zs
        exact Nat.le_trans
    lt_iff_le_not_le :=
      by
        intro a b
        exact Nat.lt_iff_le_not_le }

/- 这个实例引入了中缀语法`≤`以及关系`≥`、`<`和`>`： -/

theorem list.length.Preorder_example :
    [1] > [] :=
  by decide

/- 完全格（第11讲）被形式化为另一个类型类`CompleteLattice`，它继承自`PartialOrder`。

结合序和代数结构的类型类也可用：

    `OrderedCancelCommMonoid`
    `OrderedCommGroup`
    `OrderedSemiring`
    `LinearOrderedSemiring`
    `LinearOrderedCommRing`
    `LinearOrderedField`

所有这些数学结构通过单调性规则（例如，`a ≤ b → c ≤ d → a + c ≤ b + d`）和消去规则（例如，`c + a ≤ c + b → a ≤ b`）将`≤`和`<`与`0`、`1`、`+`和`*`联系起来。 -/

end LoVe

