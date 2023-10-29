```lean
import GlimpseOfLean.Library.Basic

open Function
```

## 合取

在这个文件中，我们将学习如何处理合取（“逻辑与”）操作符和存在量词。

在 Lean 中，两个声明 `P` 和 `Q` 的合取由 `P ∧ Q` 表示，读作 "P 和 Q"。

我们可以像使用 '↔' 一样使用合取：
* 如果 `h : P ∧ Q`，那么 `h.1 : P` 和 `h.2 : Q`。
* 要证明 `P ∧ Q`，使用 `constructor` 策略。

此外，我们可以分解合取和等价性。
* 如果 `h : P ∧ Q`，策略 `rcases h with ⟨hP, hQ⟩`
  会给出两个新的假设 `hP : P` 和 `hQ : Q`。
* 如果 `h : P ↔ Q`，策略 `rcases h with ⟨hPQ, hQP⟩`
  会给出两个新的假设 `hPQ : P → Q` 和 `hQP : Q → P`。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}
```

人们也可以在不使用构造器策略的情况下证明一个结论，只需使用 `⟨`/`⟩` 括号将两侧的证据收集起来，所以上述证明可以被重写为。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩
}
```

你可以在接下来的练习中选择你自己的风格。

# CAN PROOFS IN LEAN HELP YOU UNDERSTAND MATHS?

对于使用 Lean 的数学证明，是否能帮助你理解数学？

To answer this, let’s see the proof of a simple theorem in lean proof mode. It will give you an idea of how theorems are proved in Lean.
 
为了回答这个问题，让我们看一下在 Lean 证明模式下一个简单的定理的证明。它会给你一个关于定理在 Lean 中是如何被证明的概念。

## The Theorem \(x \cdot y = y \cdot x\)

### 定理 \(x \cdot y = y \cdot x\)

The theorem says that multiplication is commutative. This is a truth universally acknowledged in the realm of mathematics. Here’s how Lean represents and proves the theorem:

这个定理表明，乘法是可交换的。这是数学领域公认的真理。以下是 Lean 如何表示和证明这个定理:

### Theorem in Lean

### 在 Lean 里的定理

The given statement will appear like:

给出的陈述会如下所示：

```lean
theorem mul_comm (x y : ℕ) : x * y = y * x
```

The proof mode is started by using `begin` and `end`. Here’s the entire theorem and proof in Lean:

通过使用 `begin` 和 `end` 来开始证明模式。以下是在 Lean 中的整个定理以及证明：

```lean
theorem mul_comm (x y : ℕ) : x * y = y * x :=
begin
  induction y with d hd,
  { rw mul_zero, rw zero_mul },
  { rw succ_mul, rw ←hd, rw mul_succ }
end
```

The symbol `:=` indicates the start of the proof.

Symbo `rw` stands for rewrite. It means Lean should use the equation in the bracket to simplify the statement.

The symbol `←` points the equation to be used in the opposite direction.

The symbol `induction` offers a way to perform induction on natural numbers.

Symbol `with` is used to introduce two things: the base case and the inductive case. They are denoted by `d` and `hd` respectively.

符号 `:=` 表示证明的开始。

符号 `rw` 代表重写。它意味着 Lean 应该使用括号中的等式来简化陈述。

符号 `←` 指向应以相反的方向使用的等式。

符号 `induction` 提供了对自然数进行归纳的方式。

符号 `with` 用于引入两件事:基本情况和归纳情况。它们分别由 `d` 和 `hd` 表示。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  -- sorry
  constructor
  · intro h h'
    rcases h' with ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq
  -- sorry
}
```

当然，Lean 不需要任何帮助来证明这类逻辑自明的命题。
这就是 `tauto` 策略的作用，它可以证明命题逻辑中的真实语句。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  tauto
}
```

# 存在量词

为了证明 `∃ x, P x`，我们提供一些 `x₀` 使用策略 `use x₀`，然后证明 `P x₀`。这个 `x₀` 可以是来自局部环境的对象，也可以是更复杂的表达式。在下面的例子中，`use` 后要检查的属性根据定义是真的，所以证明就结束了。

```lean
example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}
```

为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来确定一个有效的 `x₀`。

同样，`h` 可以直接来自局部上下文，或者可以是一个更复杂的表达式。

```lean
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by {
  -- Let's fix k₀ such that n = k₀ + 1.
  rcases h with ⟨k₀, hk₀⟩
  -- It now suffices to prove k₀ + 1 > 0.
  rw [hk₀]
  -- and we have a lemma about this
  exact Nat.succ_pos k₀
}
```

下面的习题将使用 ℤ 的可整除性（注意 ∣ 符号，这不是 ASCII）。

根据定义，`a ∣ b ↔ ∃ k, b = a*k`，所以你可以使用 `use` 策略来证明 `a ∣ b`。

```lean
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by {
  -- sorry
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k*l
  calc
    c = b*l   := hl
    _ = (a*k)*l := by rw [hk]
    _ = a*(k*l) := by ring
  -- sorry
}
```

我们现在可以开始组合量词，使用定义

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`
  
翻译为：

  `满射 (f : X → Y) := 对于所有 的 y，存在 x，使得 f x = y`

```lean
example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by {
  -- sorry
  intro y
  rcases h y with ⟨w, hw⟩
  use f w
  exact hw
  -- sorry
}
```

这是关于 `∃` 和 `∧` 的文件的结束。你已经学习了战术
* `rcases`
* `tauto`
* `use`

这是 `Basics` 文件夹的结束。我们故意留出了逻辑或运算符
和所有关于否定的内容，这样你就可以尽快进入
实际的数学内容。你现在可以从 `Topics` 中选择一个文件。

请参阅 `03Forall` 底部的选择描述。
