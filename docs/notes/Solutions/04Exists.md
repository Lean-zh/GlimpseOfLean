```lean
import GlimpseOfLean.Library.Basic

open Function
```

## 逻辑连接词

在这个文件中，我们学习如何处理合取（"逻辑与"）运算符和存在量词。

在 Lean 中，两个语句 P 和 Q 的合取用 `P ∧ Q` 表示，读作 "P 和 Q"。

我们可以像使用 `↔` 一样使用合取：
* 如果 `h : P ∧ Q`，那么 `h.1 : P` 和 `h.2 : Q`。
* 要证明 `P ∧ Q`，可以使用 `constructor` 策略。

此外，我们可以对合取和等价进行分解。
* 如果 `h : P ∧ Q`，则 `rcases h with ⟨hP, hQ⟩` 策略会得到两个新的假设 `hP : P` 和 `hQ : Q`。
* 如果 `h : P ↔ Q`，则 `rcases h with ⟨hPQ, hQP⟩` 策略会得到两个新的假设 `hPQ : P → Q` 和 `hQP : Q → P`。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq
}
```

我们还可以通过使用 `⟨`/`⟩` 括号将两边组合起来，而不使用构造策略来证明合取。因此，上面的证明可以改写为：

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by {
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩
}
```

你可以在下一个练习中选择你自己的风格。

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

当然，Lean 不需要额外的帮助来证明这种逻辑重言式。这是 `tauto` 策略的工作，它可以证明命题逻辑中的真陈述。
```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by {
  tauto
}
```

# 存在量词

为了证明 `∃ x, P x`，我们使用 `use x₀` 策略给出一些 `x₀`，然后证明 `P x₀`。这个 `x₀` 可以是来自局部上下文的对象，也可以是一个更复杂的表达式。在下面的示例中，`use` 后面要检查的属性在定义上是成立的，因此证明结束了。

```lean
example : ∃ n : ℕ, 8 = 2*n := by {
  use 4
}
```

为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来固定一个适用的 `x₀`。

同样，`h` 可以直接来自局部上下文，也可以是一个更复杂的表达式。

```lean
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by {
  -- 我们来固定一个 k₀，使得 n = k₀ + 1。
  rcases h with ⟨k₀, hk₀⟩
  -- 现在我们只需要证明 k₀ + 1 > 0。
  rw [hk₀]
  -- 然后我们有一个关于这个的引理
  exact Nat.succ_pos k₀
}
```

下面的练习使用整数的除法（注意 ∣ 符号并不是 ASCII）。

根据定义，`a ∣ b ↔ ∃ k, b = a*k`，因此可以使用 `use` 策略来证明 `a ∣ b`。

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

现在我们可以开始组合量词，使用定义

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

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

这就是关于 `∃` 和 `∧` 的文件的结束。你已经学会了一些策略。
这是`Basics`文件夹的结束。我们有意忽略了逻辑或运算符和否定等内容，以便您能尽快进入实际的数学内容。现在您可以从`Topics`中选择一个文件。

请参阅`03Forall`底部的描述以了解选择。
