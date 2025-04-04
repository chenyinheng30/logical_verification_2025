/- 版权 © 2018–2025 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, 和 Jannis Limperg。参见 `LICENSE.txt`。 -/

import LoVe.LoVe07_EffectfulProgramming_Demo


/- # LoVe 练习7：带效应的编程

将占位符（例如`:= sorry`）替换为你的解答。 -/


set_option autoImplicit false
set_option tactic.hygienic false

namespace LoVe


/- ## 问题1：带失败的状态单子

我们引入一个更丰富的合法单子概念，它提供满足以下定律的`orelse`操作符。
`emp`表示失败。`orelse x y`会先尝试`x`，失败时回退到`y`。 -/

class LawfulMonadWithOrelse (m : Type → Type)
  extends LawfulMonad m where
  emp {α : Type} : m α
  orelse {α : Type} : m α → m α → m α
  emp_orelse {α : Type} (a : m α) :
    orelse emp a = a
  orelse_emp {α : Type} (a : m α) :
    orelse a emp = a
  orelse_assoc {α : Type} (a b c : m α) :
    orelse (orelse a b) c = orelse a (orelse b c)
  emp_bind {α β : Type} (f : α → m β) :
    (emp >>= f) = emp
  bind_emp {α β : Type} (f : m α) :
    (f >>= (fun a ↦ (emp : m β))) = emp

/- 1.1. 我们将`Option`类型构造器设置为`LawfulMonad_with_orelse`。完成证明。

提示：使用`simp [Bind.bind]`展开bind操作符的定义，使用`simp [Option.orelse]`展开`orelse`操作符的定义。 -/

def Option.orelse {α : Type} : Option α → Option α → Option α
  | Option.none,   ma' => ma'
  | Option.some a, _   => Option.some a

instance Option.LawfulMonadWithOrelse :
  LawfulMonadWithOrelse Option :=
  { Option.LawfulMonad with
    emp          := Option.none
    orelse       := Option.orelse
    emp_orelse   :=
      sorry
    orelse_emp   :=
      by
        intro α ma
        simp [Option.orelse]
        cases ma
        { rfl }
        { rfl }
    orelse_assoc :=
      sorry
    emp_bind     :=
      by
        intro α β f
        simp [Bind.bind]
        rfl
    bind_emp     :=
      sorry
  }

@[simp] theorem Option.some_bind {α β : Type} (a : α) (g : α → Option β) :
    (Option.some a >>= g) = g a :=
  sorry

/- 1.2. 现在我们准备定义`FAction σ`：一个带有类型为`σ`的内部状态且可能失败的单子（不同于`Action σ`）。

我们首先定义`FAction σ α`，其中`σ`是内部状态的类型，`α`是存储在单子中的值的类型。我们使用`Option`来建模失败。这意味着在定义`FAction`的单子操作时，也可以使用`Option`的单子操作。

提示：

* 记住`FAction σ α`是函数类型的别名，因此可以使用模式匹配和`fun s ↦ …`来定义`FAction σ α`的值。

* `FAction`与讲座演示中的`Action`非常相似。可以参考那里的实现获取灵感。 -/

def FAction (σ : Type) (α : Type) : Type :=
  sorry

/- 1.3. 为`FAction`定义`get`和`set`函数，其中`get`返回状态单子传递的状态，`set s`将状态更改为`s`。 -/

def get {σ : Type} : FAction σ σ :=
  sorry

def set {σ : Type} (s : σ) : FAction σ Unit :=
  sorry

/- 我们为`FAction`设置`>>=`语法： -/

def FAction.bind {σ α β : Type} (f : FAction σ α) (g : α → FAction σ β) :
  FAction σ β
  | s => f s >>= (fun (a, s) ↦ g a s)

instance FAction.Bind {σ : Type} : Bind (FAction σ) :=
  { bind := FAction.bind }

theorem FAction.bind_apply {σ α β : Type} (f : FAction σ α)
      (g : α → FAction σ β) (s : σ) :
    (f >>= g) s = (f s >>= (fun as ↦ g (Prod.fst as) (Prod.snd as))) :=
  by rfl

/- 1.4. 为`FAction`定义`pure`操作符，使其满足三个定律。 -/

def FAction.pure {σ α : Type} (a : α) : FAction σ α :=
  sorry

/- 我们为`FAction`设置`pure`语法： -/

instance FAction.Pure {σ : Type} : Pure (FAction σ) :=
  { pure := FAction.pure }

theorem FAction.pure_apply {σ α : Type} (a : α) (s : σ) :
    (pure a : FAction σ α) s = Option.some (a, s) :=
  by rfl

/- 1.5. 将`FAction`注册为单子。

提示：

* 当需要证明两个函数相等时，`funext`定理很有用。

* 定理`FAction.pure_apply`或`FAction.bind_apply`可能有用。 -/

instance FAction.LawfulMonad {σ : Type} : LawfulMonad (FAction σ) :=
  { FAction.Bind, FAction.Pure with
    pure_bind :=
      by
      sorry
    bind_pure :=
      by
        intro α ma
        apply funext
        intro s
        have bind_pure_helper :
          (do
             let x ← ma s
             pure (Prod.fst x) (Prod.snd x)) =
          ma s :=
          by apply LawfulMonad.bind_pure
        aesop
    bind_assoc :=
      sorry
  }


/- ## 问题2 (**选做**)：Kleisli操作符

Kleisli操作符`>=>`（不要与`>>=`混淆）对于管道化带效应的函数很有用。注意`fun a ↦ f a >>= g`应解析为`fun a ↦ (f a >>= g)`，而不是`(fun a ↦ f a) >>= g`。 -/

def kleisli {m : Type → Type} [LawfulMonad m] {α β γ : Type} (f : α → m β)
    (g : β → m γ) : α → m γ :=
  fun a ↦ f a >>= g

infixr:90 (priority := high) " >=> " => kleisli

/- 2.1 (**选做**). 证明`pure`是Kleisli操作符的左单位和右单位。 -/

theorem pure_kleisli {m : Type → Type} [LawfulMonad m] {α β : Type}
      (f : α → m β) :
    (pure >=> f) = f :=
  sorry

theorem kleisli_pure {m : Type → Type} [LawfulMonad m] {α β : Type}
      (f : α → m β) :
    (f >=> pure) = f :=
  sorry

/- 2.2 (**选做**). 证明Kleisli操作符满足结合律。 -/

theorem kleisli_assoc {m : Type → Type} [LawfulMonad m] {α β γ δ : Type}
      (f : α → m β) (g : β → m γ) (h : γ → m δ) :
    ((f >=> g) >=> h) = (f >=> (g >=> h)) :=
  sorry

end LoVe

