/- 版权声明 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 以及 Jannis Limperg。详见 `LICENSE.txt`。 -/

import LoVe.LoVelib


/- # LoVe 演示7：带效应的编程

单子（Monad）是函数式编程中重要的抽象概念。它通过副作用泛化了计算过程，使得在纯函数式编程语言中也能进行带效应的编程。Haskell已经证明单子可以非常成功地用于编写命令式程序。对我们而言，单子本身很有趣，还有两个额外原因：

* 它们为公理化推理提供了一个很好的例子。

* 它们是Lean自身编程（元编程，第8讲）所必需的。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 入门示例

考虑以下编程任务：

    实现一个函数 `sum257 ns`，对自然数列表 `ns` 的第二、第五和第七个元素求和。使用 `Option ℕ` 作为返回类型，这样当列表元素少于七个时，可以返回 `Option.none`。

一个直接的实现如下： -/

def nth {α : Type} : List α → Nat → Option α
  | [],      _     => Option.none
  | x :: _,  0     => Option.some x
  | _ :: xs, n + 1 => nth xs n

def sum257 (ns : List ℕ) : Option ℕ :=
  match nth ns 1 with
  | Option.none    => Option.none
  | Option.some n₂ =>
    match nth ns 4 with
    | Option.none    => Option.none
    | Option.some n₅ =>
      match nth ns 6 with
      | Option.none    => Option.none
      | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

/- 这段代码很丑陋，因为需要对选项类型进行大量模式匹配。

我们可以将所有丑陋的部分封装到一个函数中，称之为 `connect`： -/

def connect {α : Type} {β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

def sum257Connect (ns : List ℕ) : Option ℕ :=
  connect (nth ns 1)
    (fun n₂ ↦ connect (nth ns 4)
       (fun n₅ ↦ connect (nth ns 6)
          (fun n₇ ↦ Option.some (n₂ + n₅ + n₇))))

/- 与其自己定义 `connect`，我们可以使用Lean预定义的通用 `bind` 操作。还可以用 `pure` 替代 `Option.some`： -/

#check bind

def sum257Bind (ns : List ℕ) : Option ℕ :=
  bind (nth ns 1)
    (fun n₂ ↦ bind (nth ns 4)
       (fun n₅ ↦ bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇))))

/- 通过使用 `bind` 和 `pure`，`sum257Bind` 完全不涉及 `Option.none` 和 `Option.some` 的构造函数。

语法糖：

    `ma >>= f` := `bind ma f` -/

def sum257Op (ns : List ℕ) : Option ℕ :=
  nth ns 1 >>=
    fun n₂ ↦ nth ns 4 >>=
      fun n₅ ↦ nth ns 6 >>=
        fun n₇ ↦ pure (n₂ + n₅ + n₇)

/- 语法糖：

    do
      let a ← ma
      t
    :=
    ma >>= (fun a ↦ t)

    do
      ma
      t
    :=
    ma >>= (fun _ ↦ t) -/

def sum257Dos (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    do
      let n₅ ← nth ns 4
      do
        let n₇ ← nth ns 6
        pure (n₂ + n₅ + n₇)

/- 可以合并多个 `do`： -/

def sum257Do (ns : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth ns 1
    let n₅ ← nth ns 4
    let n₇ ← nth ns 6
    pure (n₂ + n₅ + n₇)

/- 尽管这种语法有命令式的风格，但函数本身仍是纯函数式程序。


## 两个操作与三条定律

`Option` 类型构造器是单子的一个例子。

一般来说，一个__单子__是一个依赖于某个类型参数 `α` 的类型构造器 `m`（即 `m α`），并配备两个特定的操作：

    `pure {α : Type} : α → m α`
    `bind {α β : Type} : m α → (α → m β) → m β`

对于 `Option`：

    `pure` := `Option.some`
    `bind` := `connect`

直观上，可以将单子看作一个“盒子”：

* `pure` 将数据放入盒子中。

* `bind` 允许我们访问盒子中的数据并修改它（甚至可能改变其类型，因为结果是 `m β` 单子，而非 `m α` 单子）。

通常没有办法从单子中提取数据，即从 `m α` 中获取 `α`。

总结来说，`pure a` 不产生副作用，只是提供一个包含值 `a` 的盒子；而 `bind ma f`（也写作 `ma >>= f`）先执行 `ma`，然后用 `ma` 的结果 `a`（在盒子中）执行 `f`。

选项单子只是众多单子实例中的一个。

类型                 | 效果
-------------------- | -------------------------------------------------------
`id`                 | 无副作用
`Option`             | 简单异常
`fun α ↦ σ → α × σ`  | 传递类型为 `σ` 的状态
`Set`                | 返回 `α` 值的非确定性计算
`fun α ↦ t → α`      | 读取类型为 `t` 的元素（如配置）
`fun α ↦ ℕ × α`      | 附加运行时间（如建模时间复杂度）
`fun α ↦ String × α` | 附加文本输出（如日志记录）
`IO`                 | 与操作系统交互
`TacticM`            | 与证明助手交互

以上所有都是一元类型构造器 `m : Type → Type`。

某些效果可以组合（如 `Option (t → α)`）。

某些效果不可执行（如 `Set α`）。尽管如此，它们在逻辑中抽象地建模程序时非常有用。

特定的单子可能提供一种无需 `bind` 就能从单子中提取盒中值的方法。

单子有多个优点，包括：

* 它们提供了方便且高度可读的 `do` 语法。

* 它们支持通用操作，如 `mmap {α β : Type} : (α → m β) → List α → m (List β)`，这些操作在所有单子中统一工作。

`bind` 和 `pure` 操作通常需要遵守三条定律。作为第一个程序的纯数据可以简化掉：

    do
      let a' ← pure a,
      f a'
  =
    f a

作为第二个程序的纯数据可以简化掉：

    do
      let a ← ma
      pure a
  =
    ma

嵌套的程序 `ma`、`f`、`g` 可以通过以下结合律扁平化：

    do
      let b ←
        do
          let a ← ma
          f a
      g b
  =
    do
      let a ← ma
      let b ← f a
      g b


## 单子的类型类

单子是一种数学结构，因此我们使用类将它们添加为类型类。可以将类型类视为一个参数化类型（这里是一个类型构造器 `m : Type → Type`）的结构。 -/

class LawfulMonad (m : Type → Type)
  extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β) :
    (pure a >>= f) = f a
  bind_pure {α : Type} (ma : m α) :
    (ma >>= pure) = ma
  bind_assoc {α β γ : Type} (f : α → m β) (g : β → m γ)
      (ma : m α) :
    ((ma >>= f) >>= g) = (ma >>= (fun a ↦ f a >>= g))

/- 逐步说明：

* 我们创建一个参数化一元类型构造器 `m` 的结构。

* 该结构继承自名为 `Bind` 和 `Pure` 的结构，这些结构提供了 `m` 上的 `bind` 和 `pure` 操作及一些语法糖。

* 定义向 `Bind` 和 `Pure` 已有的字段中添加了三个字段，用于存储定律的证明。

要用具体单子实例化此定义，必须提供类型构造器 `m`（如 `Option`）、`bind` 和 `pure` 操作符，以及定律的证明。


## 无副作用

我们的第一个单子是平凡单子 `m := id`（即 `m := (fun α ↦ α)`）。 -/

def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | a, f => f a

instance id.LawfulMonad : LawfulMonad id :=
  { pure       := id.pure
    bind       := id.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }


/- ## 基本异常

如前所述，选项类型提供了基本的异常机制。 -/

def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} :
  Option α → (α → Option β) → Option β
  | Option.none,   _ => Option.none
  | Option.some a, f => f a

instance Option.LawfulMonad : LawfulMonad Option :=
  { pure       := Option.pure
    bind       := Option.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        cases ma with
        | none   => rfl
        | some _ => rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        cases ma with
        | none   => rfl
        | some _ => rfl }

def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a


/- ## 可变状态

状态单子提供了对应于可变状态的抽象。某些编译器能识别状态单子以生成高效的命令式代码。 -/

def Action (σ α : Type) : Type :=
  σ → α × σ

def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {σ α : Type} (a : α) : Action σ α
  | s => (a, s)

def Action.bind {σ : Type} {α β : Type} (ma : Action σ α)
      (f : α → Action σ β) :
    Action σ β
  | s =>
    match ma s with
    | (a, s') => f a s'

/- `Action.pure` 类似于 `return` 语句；它不改变状态。

`Action.bind` 类似于两个语句相对于状态的顺序组合。 -/

instance Action.LawfulMonad {σ : Type} :
  LawfulMonad (Action σ) :=
  { pure       := Action.pure
    bind       := Action.bind
    pure_bind  :=
      by
        intro α β a f
        rfl
    bind_pure  :=
      by
        intro α ma
        rfl
    bind_assoc :=
      by
        intro α β γ f g ma
        rfl }

def increasingly : List ℕ → Action ℕ (List ℕ)
  | []        => pure []
  | (n :: ns) =>
    do
      let prev ← Action.read
      if n < prev then
        increasingly ns
      else
        do
          Action.write n
          let ns' ← increasingly ns
          pure (n :: ns')

#eval increasingly [1, 2, 3, 2] 0
#eval increasingly [1, 2, 3, 2, 4, 5, 2] 0


/- ## 非确定性

集合单子存储任意数量（可能无限）的 `α` 值。 -/

#check Set

def Set.pure {α : Type} : α → Set α
  | a => {a}

def Set.bind {α β : Type} : Set α → (α → Set β) → Set β
  | A, f => {b | ∃a, a ∈ A ∧ b ∈ f a}

instance Set.LawfulMonad : LawfulMonad Set :=
  { pure       := Set.pure
    bind       := Set.bind
    pure_bind  :=
      by
        intro α β a f
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_pure  :=
      by
        intro α ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
    bind_assoc :=
      by
        intro α β γ f g ma
        simp [Pure.pure, Bind.bind, Set.pure, Set.bind]
        apply Set.ext
        aesop }

/- `aesop` 是一个通用的证明搜索策略。除其他功能外，它会在假设中消除逻辑符号 `∧`、`∨`、`↔` 和 `∃`，并在目标中引入 `∧`、`↔` 和 `∃`，并定期调用简化器。它可以成功证明目标、失败或部分成功，留下一些未完成的子目标给用户。


## 通用算法：列表迭代

我们考虑一个通用的带效应程序 `mmap`，它遍历列表并对每个元素应用函数 `f`。 -/

def nthsFine {α : Type} (xss : List (List α)) (n : ℕ) :
  List (Option α) :=
  List.map (fun xs ↦ nth xs n) xss

#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsFine [[11, 12, 13, 14], [21, 22, 23]] 3

def mmap {m : Type → Type} [LawfulMonad m] {α β : Type}
    (f : α → m β) :
  List α → m (List β)
  | []      => pure []
  | a :: as =>
    do
      let b ← f a
      let bs ← mmap f as
      pure (b :: bs)

def nthsCoarse {α : Type} (xss : List (List α)) (n : ℕ) :
  Option (List α) :=
  mmap (fun xs ↦ nth xs n) xss

#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 2
#eval nthsCoarse [[11, 12, 13, 14], [21, 22, 23]] 3

theorem mmap_append {m : Type → Type} [LawfulMonad m]
      {α β : Type} (f : α → m β) :
    ∀as as' : List α, mmap f (as ++ as') =
      do
        let bs ← mmap f as
        let bs' ← mmap f as'
        pure (bs ++ bs')
  | [],      _   =>
    by simp [mmap, LawfulMonad.bind_pure, LawfulMonad.pure_bind]
  | a :: as, as' =>
    by simp [mmap, mmap_append _ as as', LawfulMonad.pure_bind,
      LawfulMonad.bind_assoc]

end LoVe

