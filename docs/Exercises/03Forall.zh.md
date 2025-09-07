```lean
import GlimpseOfLean.Library.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Function

namespace Forall
```

# 全称量词

在这个文件中，我们将学习 `∀` 量词。

设 `P` 是类型 `X` 上的一个谓词。这意味着对于每一个类型为 `X` 的数学对象 `x`，我们得到一个数学陈述 `P x`。在 Lean 中，`P x` 的类型是 `Prop`。

Lean 将 `∀ x, P x` 的证明 `h` 看作一个函数，该函数将任意的 `x : X` 映射到 `P x` 的证明 `h x`。这已经解释了使用以 `∀` 开头的假设或引理的主要方式。

为了证明 `∀ x, P x`，我们使用 `intro x` 来固定一个任意的类型为 `X` 的对象，并将其命名为 `x`（`intro` 是 "introduce"（引入）的缩写）。

还要注意，我们不需要在表达式 `∀ x, P x` 中给出 `x` 的类型，只要 `P` 的类型对 Lean 来说是明确的，Lean 就能推断出 `x` 的类型。

让我们定义一个谓词来练习 `∀`。

```lean
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

```

在下一个证明中，我们也借机介绍 `unfold` 策略，它简单地展开定义。这里这样做纯粹是出于教学目的，Lean 并不需要这些 `unfold` 调用。我们还将使用 `rfl` 策略，它证明根据定义（在非常强的意义上）为真的等式，它代表 "reflexivity"（自反性）。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  -- 我们的假设 f 是偶函数意味着 ∀ x, f (-x) = f x
  unfold even_fun at hf
  -- 对于 g 也是如此
  unfold even_fun at hg
  -- 我们需要证明 ∀ x, (f+g)(-x) = (f+g)(x)
  unfold even_fun
  -- 设 x 为任意实数
  intro x
  -- 然后开始计算
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g (-x)     := by rw [hf x]
               _ = f x + g x        := by rw [hg x]
               _ = (f + g) x        := by rfl


```

像 `apply`、`exact`、`rfl` 和 `calc` 这样的策略会自动展开定义。你可以通过删除上面例子中的 `unfold` 行来测试这一点。

像 `rw` 和 `ring` 这样的策略通常不会展开出现在目标中的定义。这就是为什么第一行计算是必要的，尽管它的证明只是 `rfl`。在那一行之前，`rw [hf x]` 找不到任何类似 `f (-x)` 的东西，因此会放弃。然而最后一行不是必要的，因为它只是证明了一个根据定义为真的东西，并且后面没有跟着 `rw`。

另外，Lean 不需要被告知 `hf` 应该在重写之前特化为 `x`，就像在第一个文件中一样。

还要回忆 `rw` 可以接受一个表达式列表用于重写。例如 `rw [h₁, h₂, h₃]` 等价于三行 `rw [h₁]`、`rw [h₂]` 和 `rw [h₃]`。注意当使用这种语法阅读证明时，你可以检查这些重写之间的策略状态。你只需要将光标移动到列表内部即可。

因此我们可以将上面的证明压缩为：

```lean
example (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x)  := by rfl
               _ = f x + g x        := by rw [hf, hg]

```

现在让我们练习一下。回忆一下，如果你需要学习如何输入一个 unicode 符号，你可以将鼠标光标放在符号上方并等待一秒钟。

```lean
example (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  sorry

```

让我们增加更多量词，并练习正向和反向推理。

在下面的定义中，注意 `∀ x₁, ∀ x₂, ...` 是如何简化为 `∀ x₁ x₂, ...` 的。

```lean
def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

```

让我们非常明确地首先使用正向推理。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- 设 x₁ 和 x₂ 为满足 x₁ ≤ x₂ 的实数
  intro x₁ x₂ h
  -- 由于 f 是非递减的，所以 f x₁ ≤ f x₂。
  have step₁ : f x₁ ≤ f x₂ := by exact hf x₁ x₂ h
  -- 由于 g 是非递减的，我们得到 g (f x₁) ≤ g (f x₂)。
  exact hg (f x₁) (f x₂) step₁

```

在上面的证明中，注意在 `hf x₁ x₂ h` 中指定 `x₁` 和 `x₂` 是多么不方便，因为它们可以从 `hf` 的类型中推断出来。我们本来可以写 `hf _ _ h`，Lean 会填充用 `_` 表示的空洞。同样的说明适用于最后一行。

上面证明的一个可能的变体是使用 `specialize` 策略来将 `hf` 替换为其对相关值的特化。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

```

这个 `specialize` 策略主要用于探索，或为在假设中重写做准备。通常可以通过使用直接涉及原始假设的更复杂表达式来替换它的使用，如下面的变体所示：

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)

```

让我们看看反向推理在这里会是什么样子的。和这种风格的惯例一样，我们使用 `apply` 并享受 Lean 使用所谓的归一化（unification）为我们特化假设。

```lean
example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- 设 x₁ 和 x₂ 为满足 x₁ ≤ x₂ 的实数
  intro x₁ x₂ h
  -- 我们需要证明 (g ∘ f) x₁ ≤ (g ∘ f) x₂。
  -- 由于 g 是非递减的，只要证明 f x₁ ≤ f x₂ 就足够了
  apply hg
  -- 这由我们关于 f 的假设可得
  apply hf
  -- 以及关于 x₁ 和 x₂ 的假设
  exact h

example (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  sorry

```

# 寻找引理

Lean 的数学库包含许多有用的事实，要记住所有的名字是不可能的。下面的练习教你两种避免需要记住名字的技巧。
* `simp` 会简化复杂的表达式。
* `apply?` 会从库中寻找引理。

使用 `simp` 作为第一步来证明以下内容。注意 `X : Set ℝ` 意味着 `X` 是一个（仅）包含实数的集合。

```lean
example (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  sorry

```

使用 `apply?` 来找到说明每个具有紧支集的连续函数都有全局最小值的引理。你可以点击出现的建议来将 `apply?` 替换为它建议的策略。

```lean
example (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  sorry

```

注意 `apply?` 不仅仅建议完整的证明。它可以建议适用但需要检查副条件的引理。接受这样的建议将输出使用 `refine` 策略的不完整证明。

注意每个建议都附有需要检查的副条件列表。因此你需要根据副条件的样子来决定接受哪个建议。例如，如果目标是证明函数的连续性，有一个引理总是适用：说明任何从离散拓扑空间出发的函数都是连续的引理。但它将源空间的离散性作为副条件。因此当决定接受这个建议时你应该小心，因为它很快就会导致死胡同。

这是本文件的结尾，你在这里学会了如何处理全称量词。你学会了以下策略：
* `unfold`
* `specialize`
* `simp`
* `apply?`

现在你可以选择接下来做什么。还有一个基础文件 `04Exists` 关于存在量词和合取。你可以现在就做，或者直接深入到某个专门的文件中。在后一种情况下，如果你在任何涉及 `∃`/`∧` 的内容上遇到困难，你应该回到 `04Exists` (where `∧` is the symbol for conjunctions, aka the logical "and" operator)。

你可以从 `Topics` 文件夹中的专门文件开始。你可以选择：
* `SequenceLimit`（较简单，数学）如果你想做一些初等微积分。建议先完成 `04Exists` 文件。
* `Probability`（较简单，数学）如果你想研究概率测度、独立集合和条件概率，包括贝叶斯定理。
* `RingTheory`（中等难度，数学）如果你想做一些交换代数。它从交换环的基础知识开始，然后介绍理想并证明 Nœther's first isomorphism theorem, and finishes with the Chinese remainder theorem 在一般交换环中。
* `GaloisAdjunctions`（较难，数学）如果你想要更多抽象并学习如何证明关于完全格之间的伴随的事实。它以乘积拓扑的构造子及其泛性质结束尽可能少操作开集。
* `ClassicalPropositionalLogic`（较简单，逻辑）如果你想学习如何在 Lean 中做经典命题逻辑。
* `IntuitionisticPropositionalLogic`（较难，逻辑）如果你想要更大的挑战并做直觉主义命题逻辑。

注意这两个逻辑文件真正适合对逻辑作为目标而非作为工具感兴趣的人。
