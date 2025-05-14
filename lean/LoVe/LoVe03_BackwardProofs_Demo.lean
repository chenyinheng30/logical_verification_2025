/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见`LICENSE.txt`。 -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示3：逆向证明

__策略__（tactic）对证明目标进行操作，要么证明它，要么创建新的子目标。策略是一种__逆向__证明机制：它们从目标出发，朝着可用的假设和定理方向工作。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace BackwardProofs


/- ## 策略模式

战术证明的语法：

    by
      _策略₁_
      …
      _策略N_

关键字`by`向Lean表明这是一个战术证明。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  by
    intro a b
    intro ha hb
    apply ha

/- 注意`a → b → a`被解析为`a → (b → a)`。

Lean中的命题是`Prop`类型的项。`Prop`是一个类型，就像`Nat`和`List Bool`一样。实际上，命题和类型之间存在密切对应关系，这将在第4讲中解释。


## 基础策略

`intro`将`∀`量化的变量或蕴含`→`的假设从目标的结论（`⊢`之后）移动到目标的前提（`⊢`之前）。

`apply`将目标的结论与指定定理的结论匹配，并将定理的假设作为新目标添加。 -/

theorem fst_of_two_props_params (a b : Prop) (ha : a) (hb : b) :
    a :=
  by apply ha

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  by
    intro ha
    apply hbc
    apply hab
    apply ha

theorem prop_comp_params (a b c : Prop) (hab : a → b) (hbc : b → c) (ha: a) :
    c :=
  by
    apply hbc
    apply hab
    apply ha

/- 上述证明的逐步解释：

* 假设我们有一个`a`的证明。
* 目标是`c`，如果我们能证明`b`（来自`hbc`），就可以得到`c`。
* 目标是`b`，如果我们能证明`a`（来自`hab`），就可以得到`b`。
* 我们已经知道`a`（来自`ha`）。

接下来，`exact`将目标的结论与指定定理匹配，关闭目标。在这种情况下，我们通常可以使用`apply`，但`exact`能更好地传达我们的意图。 -/

theorem fst_of_two_props_exact (a b : Prop) (ha : a) (hb : b) :
    a :=
  by exact ha

/- `assumption`从局部上下文中找到一个与目标结论匹配的假设，并应用它来证明目标。 -/

theorem fst_of_two_props_assumption (a b : Prop)
      (ha : a) (hb : b) :
    a :=
  by assumption

/- `rfl`证明`l = r`，其中两边在计算上是语法相等的。计算包括定义的展开、β-归约（将`fun`应用于参数）、`let`等。 -/

theorem α_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = (fun y ↦ f y) :=
  by rfl

theorem β_example {α β : Type} (f : α → β) (a : α) :
    (fun x ↦ f x) a = f a :=
  by rfl

def double (n : ℕ) : ℕ :=
  n + n

theorem δ_example :
    double 5 = 5 + 5 :=
  by rfl

/- `let`引入一个局部作用域的定义。下面的`n := 2`仅在表达式`n + n`中有效。 -/

theorem ζ_example :
    (let n : ℕ := 2
     n + n) = 4 :=
  by rfl

theorem η_example {α β : Type} (f : α → β) :
    (fun x ↦ f x) = f :=
  by rfl

/- `(a, b)`是一个对，其第一个分量是`a`，第二个分量是`b`。`Prod.fst`是一个投影，提取对中的第一个分量。 -/

theorem ι_example {α β : Type} (a : α) (b : β) :
    Prod.fst (a, b) = a :=
  by rfl


/- ## 逻辑连接词和量词的推理

引入规则： -/

#check True.intro
#check And.intro
#check Or.inl
#check Or.inr
#check Iff.intro
#check Exists.intro

/- 消去规则： -/

#check False.elim
#check And.left
#check And.right
#check Or.elim
#check Iff.mp
#check Iff.mpr
#check Exists.elim

/- `¬`的定义及相关定理： -/

#print Not
#check Classical.em
#check Classical.byContradiction

/- 没有`Not`（`¬`）的显式规则，因为`¬ p`被定义为`p → False`。 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 上述证明的逐步解释：

* 假设我们知道`a ∧ b`。
* 目标是`b ∧ a`。
* 显示`b`，如果我们能显示一个右边为`b`的合取式。
* 可以，我们已经有`a ∧ b`。
* 显示`a`，如果我们能显示一个左边为`a`的合取式。
* 可以，我们已经有`a ∧ b`。

`{ … }`组合器专注于特定的子目标。内部的策略必须完全证明它。在下面的证明中，`{ … }`用于两个子目标，以给证明更多结构。 -/

theorem And_swap_braces :
    ∀a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    { exact And.right hab }
    { exact And.left hab }

/- 注意上面我们直接将假设`hab`传递给定理`And.right`和`And.left`，而不是等待定理的假设作为新子目标出现。这是一个小的正向步骤，在一个逆向证明中。 -/

opaque f : ℕ → ℕ

theorem f5_if (h : ∀n : ℕ, f n = n) :
    f 5 = 5 :=
  by exact h 5

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  by
    intro hab
    apply Or.elim hab
    { intro ha
      exact Or.inr ha }
    { intro hb
      exact Or.inl hb }

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  by
    intro hab ha
    apply hab
    exact ha

theorem Not_Not_intro (a : Prop) :
    a → ¬¬ a :=
  by
    intro ha hna
    apply hna
    exact ha

theorem Exists_double_iden :
    ∃n : ℕ, double n = n :=
  by
    apply Exists.intro 0
    rfl


/- ## 关于等式的推理 -/

#check Eq.refl
#check Eq.symm
#check Eq.trans
#check Eq.subst

/- 上述规则可以直接使用： -/

theorem Eq_trans_symm {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans
    { exact hab }
    { apply Eq.symm
      exact hcb }

/- `rw`将单个等式作为从左到右的重写规则应用一次。要从右到左应用等式，在其名称前加`←`。 -/

theorem Eq_trans_symm_rw {α : Type} (a b c : α)
      (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    rw [hab]
    rw [hcb]

/- `rw`可以展开定义。下面，`¬¬ a`变成`¬ a → False`，`¬ a`变成`a → False`。 -/

theorem a_proof_of_negation (a : Prop) :
    a → ¬¬ a :=
  by
    rw [Not]
    rw [Not]
    intro ha
    intro hna
    apply hna
    exact ha

/- `simp`应用一组标准的重写规则（__simp集__）直到穷尽。可以使用`@[simp]`属性扩展该集。可以使用语法`simp [_定理₁_, …, _定理N_]`临时将定理添加到simp集中。 -/

theorem cong_two_args_1p1 {α : Type} (a b c d : α)
      (g : α → α → ℕ → α) (hab : a = b) (hcd : c = d) :
    g a c (1 + 1) = g b d 2 :=
  by simp [hab, hcd]

/- `ac_rfl`类似于`rfl`，但它可以推理`+`、`*`和其他二元运算符的结合性和交换性。 -/

theorem abc_Eq_cba (a b c : ℕ) :
    a + b + c = c + b + a :=
  by ac_rfl


/- ## 数学归纳法证明

`induction`对指定变量进行归纳。它为每个构造函数生成一个命名的子目标。 -/

theorem add_zero (n : ℕ) :
    add 0 n = n :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_succ (m n : ℕ) :
    add (Nat.succ m) n = Nat.succ (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero       => simp [add, add_zero]
    | succ n' ih => simp [add, add_succ, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih => simp [add, ih]

/- `ac_rfl`是可扩展的。我们可以使用类型类实例机制（在第5讲中解释）将`add`注册为交换和结合的运算符。这对于下面的`ac_rfl`调用很有用。 -/

instance Associative_add : Std.Associative add :=
  { assoc := add_assoc }

instance Commutative_add : Std.Commutative add :=
  { comm := add_comm }

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero       => rfl
    | succ n' ih =>
      simp [add, mul, ih]
      ac_rfl


/- ## 清理策略

`clear`移除未使用的变量或假设。

`rename`更改变量或假设的名称。 -/

theorem cleanup_example (a b c : Prop) (ha : a) (hb : b)
      (hab : a → b) (hbc : b → c) :
    c :=
  by
    clear ha hab a
    apply hbc
    clear hbc c
    rename b => h
    exact h

end BackwardProofs

end LoVe
