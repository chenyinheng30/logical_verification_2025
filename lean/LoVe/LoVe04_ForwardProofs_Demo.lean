/- 版权所有 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl 和 Jannis Limperg。参见 `LICENSE.txt` 文件。 -/

import LoVe.LoVe02_ProgramsAndTheorems_Demo


/- # LoVe 演示4：正向证明

在构建证明时，通常采用__正向__推理更为合理：从已知事实出发，逐步推导至目标。Lean的结构化证明和原始证明项是支持正向推理的两种风格。 -/

set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe

namespace ForwardProofs


/- ## 结构化构造

结构化证明是建立在Lean的__证明项__之上的语法糖。

最简单的结构化证明形式是定理名称（可能带有参数）。 -/

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  sorry

theorem add_comm_zero_left (n : ℕ) :
    add 0 n = add n 0 :=
  add_comm 0 n

/- 等效的反向证明： -/

theorem add_comm_zero_left_by_exact (n : ℕ) :
    add 0 n = add n 0 :=
  by exact add_comm 0 n

/- `fix` 和 `assume` 将 `∀` 量化的变量和假设从目标移至局部上下文中。它们可视为 `intro` 策略的结构化版本。

`show` 用于重申待证目标。它可作为文档说明，或用于重新表述目标（通过计算等价）。 -/

theorem fst_of_two_props :
    ∀a b : Prop, a → b → a :=
  fix a b : Prop
  assume ha : a
  assume hb : b
  show a from
    ha

theorem fst_of_two_props_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  show a from
    ha

theorem fst_of_two_props_no_show (a b : Prop) (ha : a) (hb : b) :
    a :=
  ha

/- `have` 用于证明中间定理，可引用局部上下文。 -/

theorem prop_comp (a b c : Prop) (hab : a → b) (hbc : b → c) :
    a → c :=
  assume ha : a
  have hb : b :=
    hab ha
  have hc : c :=
    hbc hb
  show c from
    hc

theorem prop_comp_inline (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
  a → c :=
  assume ha : a
  show c from
    hbc (hab ha)


/- ## 关于连接词和量词的正向推理 -/

theorem And_swap (a b : Prop) :
    a ∧ b → b ∧ a :=
  assume hab : a ∧ b
  have ha : a :=
    And.left hab
  have hb : b :=
    And.right hab
  show b ∧ a from
    And.intro hb ha

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
       show b ∨ a from
         Or.inr ha)
      (assume hb : b
       show b ∨ a from
         Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  Exists.intro 0
    (show double 0 = 0 from
     by rfl)

theorem Nat_exists_double_iden_no_show :
    ∃n : ℕ, double n = n :=
  Exists.intro 0 (by rfl)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b
  assume ha : a
  show b from
    hab ha

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  assume ha : a
  assume hna : ¬ a
  show False from
    hna ha

/- 正如可以在反向证明中应用正向推理，也可以在正向证明中应用反向推理（通过`by`指示）： -/

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hall : ∀x, x = t → P x
     show P t from
       by
         apply hall t
         rfl)
    (assume hp : P t
     fix x : α
     assume heq : x = t
     show P x from
       by
         rw [heq]
         exact hp)

theorem beast_666 (beast : ℕ) :
    (∀n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point _ _

#print beast_666

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hex : ∃x, x = t ∧ P x
     show P t from
       Exists.elim hex
         (fix x : α
          assume hand : x = t ∧ P x
          have hxt : x = t :=
            And.left hand
          have hpx : P x :=
            And.right hand
          show P t from
            by
              rw [←hxt]
              exact hpx))
    (assume hp : P t
     show ∃x : α, x = t ∧ P x from
       Exists.intro t
         (have tt : t = t :=
            by rfl
          show t = t ∧ P t from
            And.intro tt hp))


/- ## 计算式证明

在非正式数学中，我们常使用等式、不等式或等价关系的传递链（如`a ≥ b ≥ c`）。在Lean中，这类计算式证明由`calc`支持。

语法：

    calc
      _项₀_ _运算符₁_ _项₁_ :=
        _证明₁_
      _ _运算符₂_ _项₂_ :=
        _证明₂_
     ⋮
      _ _运算符N_ _项N_ :=
        _证明N_ -/

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw [Nat.two_mul]
    _ = m + n + m :=
      by ac_rfl

/- `calc`能减少重复、省略部分`have`标签及传递性推理： -/

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  have hmul : 2 * m + n = m + m + n :=
    by rw [Nat.two_mul]
  have hcomm : m + m + n = m + n + m :=
    by ac_rfl
  show _ from
    Eq.trans hmul hcomm


/- ## 使用策略的正向推理

结构化证明命令`have`、`let`和`calc`也可作为策略使用。即使在策略模式下，以正向方式陈述中间结果和定义也很有用。 -/

theorem prop_comp_tactical (a b c : Prop) (hab : a → b)
    (hbc : b → c) :
    a → c :=
  by
    intro ha
    have hb : b :=
      hab ha
    let c' := c
    have hc : c' :=
      hbc hb
    exact hc


/- ## 依赖类型

依赖类型是依赖类型理论家族逻辑的标志性特征。

考虑函数`pick`，它接受数字`n : ℕ`并返回一个介于0和`n`之间的数。概念上，`pick`具有依赖类型：

    `(n : ℕ) → {i : ℕ // i ≤ n}`

我们可以将其视为`ℕ`索引的族，其中每个成员的类型可能依赖于索引：

    `pick n : {i : ℕ // i ≤ n}`

但类型也可能依赖于另一个类型，例如`List`（或`fun α ↦ List α`）和`fun α ↦ α → α`。

项可以依赖于类型，例如`fun α ↦ fun (x : α) ↦ x`（多态恒等函数）。

当然，项也可以依赖于项。

除非另有说明，__依赖类型__特指依赖于项的类型。这就是我们所说的简单类型理论不支持依赖类型的含义。

总结来说，在归纳构造演算中有四种`fun x ↦ t`的情况（参见Barendregt的`λ`立方体）：

主体(`t`) |              | 参数(`x`) | 描述
---------- | ------------ | ---------- | ----------------------------------
项         | 依赖于       | 项         | 简单类型的匿名函数
类型       | 依赖于       | 项         | 依赖类型（严格意义）
项         | 依赖于       | 类型       | 多态项
类型       | 依赖于       | 类型       | 类型构造器

修订后的类型规则：

    C ⊢ t : (x : σ) → τ[x]    C ⊢ u : σ
    ———————————————————————————————————— App'
    C ⊢ t u : τ[u]

    C, x : σ ⊢ t : τ[x]
    ———————————————————————————————————— Fun'
    C ⊢ (fun x : σ ↦ t) : (x : σ) → τ[x]

如果`x`不在`τ[x]`中出现，这两条规则退化为`App`和`Fun`

`App'`示例：

    ⊢ pick : (n : ℕ) → {i : ℕ // i ≤ n}    ⊢ 5 : ℕ
    ——————————————————————————————————————————————— App'
    ⊢ pick 5 : {i : ℕ // i ≤ 5}

`Fun'`示例：

    α : Type, x : α ⊢ x : α
    —————————————————————————————————— Fun 或 Fun'
    α : Type ⊢ (fun x : α ↦ x) : α → α
    ————————————————————————————————————————————————————— Fun'
    ⊢ (fun α : Type ↦ fun x : α ↦ x) : (α : Type) → α → α

值得注意的是，全称量化只是依赖类型的别名：

    `∀x : σ, τ` := `(x : σ) → τ`

下文将更清晰地展示这一点。


## PAT原则

`→`既用作蕴涵符号，也用作函数类型构造器。这两组概念不仅外观相同，根据PAT原则它们本质相同：

* PAT = 命题即类型；
* PAT = 证明即项。

类型：

* `σ → τ`是从`σ`到`τ`的全函数类型。
* `(x : σ) → τ[x]`是从`x : σ`到`τ[x]`的依赖函数类型。

命题：

* `P → Q`可读作"`P`蕴涵`Q`"，或作为将`P`的证明映射到`Q`证明的函数类型。
* `∀x : σ, Q[x]`可读作"对所有`x`，`Q[x]`"，或作为类型为`(x : σ) → Q[x]`的函数类型，将类型为`σ`的值`x`映射到`Q[x]`的证明。

项：

* 常量是项。
* 变量是项。
* `t u`是函数`t`应用于值`u`。
* `fun x ↦ t[x]`是将`x`映射到`t[x]`的函数。

证明：

* 定理或假设名称是证明。
* `H t`将证明`H`语句中的前导参数或量词实例化为项`t`，是证明。
* `H G`用证明`G`解除`H`语句中的前导假设，是证明。
* `fun h : P ↦ H[h]`是`P → Q`的证明，假设`H[h]`是对`h : P`的`Q`证明。
* `fun x : σ ↦ H[x]`是`∀x : σ, Q[x]`的证明，假设`H[x]`是对`x : σ`的`Q[x]`证明。 -/

theorem And_swap_raw (a b : Prop) :
    a ∧ b → b ∧ a :=
  fun hab : a ∧ b ↦ And.intro (And.right hab) (And.left hab)

theorem And_swap_tactical (a b : Prop) :
    a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    apply And.right
    exact hab
    apply And.left
    exact hab

/- 策略证明会被简化为证明项。 -/

#print And_swap
#print And_swap_raw
#print And_swap_tactical

end ForwardProofs


/- ## 通过模式匹配和递归进行归纳

根据PAT原则，归纳证明等同于递归指定的证明项。因此，作为`induction`策略的替代方案，归纳也可以通过模式匹配和递归完成：

* 归纳假设可通过所证定理的名称获得；
* 参数的良基性通常自动证明。 -/

#check reverse

theorem reverse_append {α : Type} :
    ∀xs ys : List α,
      reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys => by simp [reverse, reverse_append xs]

theorem reverse_append_tactical {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ reverse xs :=
  by
    induction xs with
    | nil           => simp [reverse]
    | cons x xs' ih => simp [reverse, ih]

theorem reverse_reverse {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    by simp [reverse, reverse_append, reverse_reverse xs]

end LoVe

