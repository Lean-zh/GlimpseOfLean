```lean
import GlimpseOfLean.Library.Basic

open Function

```

## 合取

在这个文件中，我们学习如何处理合取（"逻辑与"）操作符和存在量词。

在 Lean 中，两个命题 `P` 和 `Q` 的合取记为 `P ∧ Q`，读作"P 和 Q"。

我们可以像使用 `↔` 一样使用合取：
* 如果 `h : P ∧ Q`，那么 `h.1 : P` 且 `h.2 : Q`。
* 要证明 `P ∧ Q`，使用 `constructor` 策略。

此外，我们可以分解合取和等价关系。
* 如果 `h : P ∧ Q`，策略 `rcases h with ⟨hP, hQ⟩` 给出两个新假设 `hP : P` 和 `hQ : Q`。
* 如果 `h : P ↔ Q`，策略 `rcases h with ⟨hPQ, hQP⟩` 给出两个新假设 `hPQ : P → Q` 和 `hQP : Q → P`。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

```

也可以通过使用 `⟨`/`⟩` 括号收集两边来证明合取，而不使用 constructor 策略，因此上面的证明可以重写为。

```lean
example (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

```

在下一个练习中你可以选择自己的风格。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  sorry

```

当然 Lean 不需要任何帮助来证明这种逻辑重言式。这是 `tauto` 策略的工作，它可以证明命题逻辑中的真命题。

```lean
example (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  tauto

```

# 存在量词

为了证明 `∃ x, P x`，我们使用策略 `use x₀` 给出某个 `x₀`，然后证明 `P x₀`。这个 `x₀` 可以是局部上下文中的对象或者更复杂的表达式。在下面的例子中，`use` 之后要检查的性质根据定义为真，所以证明结束了。

```lean
example : ∃ n : ℕ, 8 = 2*n := by
  use 4

```

为了使用 `h : ∃ x, P x`，我们使用 `rcases` 策略来固定一个有效的 `x₀`。

这里 `h` 可以直接来自局部上下文，也可以是更复杂的表达式。

```lean
example (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  -- 设 k₀ 使得 n = k₀ + 1。
  rcases h with ⟨k₀, hk₀⟩
  -- 现在只需证明 k₀ + 1 > 0。
  rw [hk₀]
  -- 而我们有关于此的引理
  exact Nat.succ_pos k₀

```

接下来的练习使用 ℤ 中的整除性（注意 ∣ 符号不是 ASCII 符号）。

根据定义，`a ∣ b ↔ ∃ k, b = a*k`，所以你可以使用 `use` 策略来证明 `a ∣ b`。

```lean
example (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  sorry


```

我们现在可以开始组合量词，使用定义

  `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`

```lean
example (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  sorry

```

这是关于 `∃` 和 `∧` 的文件的结尾。你学会了策略
* `rcases`
* `tauto`
* `use`

这是 `Basics` 文件夹的结尾。我们故意省略了逻辑或操作符和关于否定的所有内容，以便你能尽快进入实际的数学内容。你现在可以从 `Topics` 中选择一个文件。

关于选择的描述请参见 `03Forall` 的底部。
